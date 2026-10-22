/*
 * Copyright (C) the libgit2 contributors. All rights reserved.
 *
 * This file is part of libgit2, distributed under the GNU GPL v2 with
 * a Linking Exception. For full terms see the included COPYING file.
 */

#include "fetch.h"

#include "git2/oid.h"
#include "git2/refs.h"
#include "git2/revwalk.h"
#include "git2/transport.h"
#include "git2/sys/remote.h"

#include "oid.h"
#include "remote.h"
#include "refspec.h"
#include "pack.h"
#include "repository.h"
#include "refs.h"
#include "transports/smart.h"
#include "futils.h"
#include "fs_path.h"
#include "config.h"

static bool filter_spec_is_blob_limit(const char *filter_spec)
{
	const char *size;

	if (strncmp(filter_spec, "blob:limit=", 11))
		return false;

	size = filter_spec + 11;
	if (!*size)
		return false;

	while (git__isdigit(*size))
		size++;

	return !*size || (!size[1] && strchr("kmg", *size));
}

static bool filter_spec_is_tree_depth(const char *filter_spec)
{
	const char *depth;

	if (strncmp(filter_spec, "tree:", 5))
		return false;

	depth = filter_spec + 5;
	if (!*depth)
		return false;

	while (git__isdigit(*depth))
		depth++;

	return !*depth;
}

static int validate_filter_spec(const char *filter_spec)
{
	if (!filter_spec)
		return 0;

	if (!strcmp(filter_spec, "blob:none") ||
	    filter_spec_is_blob_limit(filter_spec) ||
	    filter_spec_is_tree_depth(filter_spec))
		return 0;

	git_error_set(
	        GIT_ERROR_INVALID,
	        "unsupported fetch filter '%s'; supported filters are "
	        "'blob:none', 'blob:limit=<n>[kmg]', and 'tree:<depth>'",
	        filter_spec);
	return GIT_EINVALIDSPEC;
}

static int maybe_want(git_remote *remote, git_remote_head *head, git_refspec *tagspec, git_remote_autotag_option_t tagopt)
{
	int match = 0, valid;

	if (git_reference_name_is_valid(&valid, head->name) < 0)
		return -1;

	if (!valid)
		return 0;

	if (tagopt == GIT_REMOTE_DOWNLOAD_TAGS_ALL) {
		/*
		 * If tagopt is --tags, always request tags
		 * in addition to the remote's refspecs
		 */
		if (git_refspec_src_matches(tagspec, head->name))
			match = 1;
	}

	if (!match && git_remote__matching_refspec(remote, head->name))
		match = 1;

	if (!match)
		return 0;

	return git_vector_insert(&remote->refs, head);
}

static int mark_local(git_remote *remote)
{
	git_remote_head *head;
	git_odb *odb;
	size_t i;

	if (git_repository_odb__weakptr(&odb, remote->repo) < 0)
		return -1;

	git_vector_foreach(&remote->refs, i, head) {
		/* If we have the object, mark it so we don't ask for it.
		   However if we are unshallowing or changing history
		   depth, we need to ask for it even though the head
		   exists locally; and a filtered fetch of objects by
		   ID wants what is beneath them, which a partial clone
		   may lack even when it has the objects themselves. */
		if (remote->nego.depth == GIT_FETCH_DEPTH_FULL &&
		    !(remote->fetching_oids && remote->nego.filter_spec) &&
		    git_odb_exists(odb, &head->oid))
			head->local = 1;
		else
			remote->need_pack = 1;
	}

	return 0;
}

static int maybe_want_oid(git_remote *remote, git_refspec *spec)
{
	git_remote_head *oid_head;

	oid_head = git__calloc(1, sizeof(git_remote_head));
	GIT_ERROR_CHECK_ALLOC(oid_head);

	git_oid__fromstr(&oid_head->oid, spec->src, remote->repo->oid_type);

	if (spec->dst) {
		oid_head->name = git__strdup(spec->dst);
		GIT_ERROR_CHECK_ALLOC(oid_head->name);
	}

	if (git_vector_insert(&remote->local_heads, oid_head) < 0 ||
	    git_vector_insert(&remote->refs, oid_head) < 0)
		return -1;

	return 0;
}

static int filter_wants(git_remote *remote, const git_fetch_options *opts)
{
	git_remote_head **heads;
	git_refspec tagspec, head, *spec;
	int error = 0;
	size_t i, heads_len;
	unsigned int remote_caps;
	unsigned int oid_mask = GIT_REMOTE_CAPABILITY_TIP_OID |
	                        GIT_REMOTE_CAPABILITY_REACHABLE_OID;
	git_remote_autotag_option_t tagopt = remote->download_tags;

	if (opts && opts->download_tags != GIT_REMOTE_DOWNLOAD_TAGS_UNSPECIFIED)
		tagopt = opts->download_tags;

	git_vector_clear(&remote->refs);
	if ((error = git_refspec__parse(&tagspec, GIT_REFSPEC_TAGS, true)) < 0)
		return error;

	/*
	 * The fetch refspec can be NULL, and what this means is that the
	 * user didn't specify one. This is fine, as it means that we're
	 * not interested in any particular branch but just the remote's
	 * HEAD, which will be stored in FETCH_HEAD after the fetch.
	 */
	if (remote->active_refspecs.length == 0) {
		if ((error = git_refspec__parse(&head, "HEAD", true)) < 0)
			goto cleanup;

		error = git_refspec__dwim_one(&remote->active_refspecs, &head, &remote->refs);
		git_refspec__dispose(&head);

		if (error < 0)
			goto cleanup;
	}

	if ((error = git_remote_ls((const git_remote_head ***)&heads, &heads_len, remote)) < 0 ||
	    (error = git_remote_capabilities(&remote_caps, remote)) < 0)
		goto cleanup;

	/* Handle remote heads */
	for (i = 0; i < heads_len; i++) {
		if ((error = maybe_want(remote, heads[i], &tagspec, tagopt)) < 0)
			goto cleanup;
	}

	/* Handle explicitly specified OID specs */
	git_vector_foreach(&remote->active_refspecs, i, spec) {
		if (!git_oid__is_hexstr(spec->src, remote->repo->oid_type))
			continue;

		if (!(remote_caps & oid_mask)) {
			git_error_set(
				GIT_ERROR_NET,
				"server does not support fetching objects by ID");
			error = GIT_ENOTSUPPORTED;
			goto cleanup;
		}

		if ((error = maybe_want_oid(remote, spec)) < 0)
			goto cleanup;
	}

	error = mark_local(remote);

cleanup:
	git_refspec__dispose(&tagspec);

	return error;
}

/*
 * In this first version, we push all our refs in and start sending
 * them out. When we get an ACK we hide that commit and continue
 * traversing until we're done
 */
int git_fetch_negotiate(git_remote *remote, const git_fetch_options *opts)
{
	git_transport *t = remote->transport;
	int error;

	remote->need_pack = 0;
	remote->nego.filter_spec = NULL;
	remote->nego.no_haves = remote->fetching_oids;

	if (opts) {
		GIT_ASSERT_ARG(opts->depth >= 0);
		remote->nego.depth = opts->depth;

		if (opts->version >= 2)
			remote->nego.filter_spec = opts->filter_spec;
	}

	if (remote->nego.filter_spec && !remote->name) {
		git_error_set(
			GIT_ERROR_INVALID,
			"filtered fetch requires a named remote");
		return GIT_EINVALID;
	}

	if ((error = validate_filter_spec(remote->nego.filter_spec)) < 0)
		return error;

	if (filter_wants(remote, opts) < 0)
		return -1;

	/* Don't try to negotiate when we don't want anything */
	if (!remote->need_pack)
		return 0;

	/*
	 * Now we have everything set up so we can start tell the
	 * server what we want and what we have.
	 */
	remote->nego.refs = (const git_remote_head * const *)remote->refs.contents;
	remote->nego.refs_len = remote->refs.length;

	if (git_repository__shallow_roots(&remote->nego.shallow_roots,
	                                  &remote->nego.shallow_roots_len,
	                                  remote->repo) < 0)
		return -1;

	error = t->negotiate_fetch(t,
		remote->repo,
		&remote->nego);

	git__free(remote->nego.shallow_roots);

	return error;
}

/*
 * Whether this fetch comes from a promisor remote: the filtered fetch that
 * makes a partial clone, a fetch of omitted objects by ID, or any fetch
 * from the remote that extensions.partialclone names.
 */
static bool fetch_is_from_promisor(git_remote *remote)
{
	git_config *config;
	git_str key = GIT_STR_INIT;
	int promisor = 0;

	if (remote->nego.filter_spec || remote->fetching_oids)
		return true;

	if (!remote->name ||
	    git_repository_config__weakptr(&config, remote->repo) < 0 ||
	    git_str_printf(&key, "remote.%s.promisor", remote->name) < 0 ||
	    git_config_get_bool(&promisor, config, key.ptr) < 0)
		promisor = 0;

	git_error_clear();
	git_str_dispose(&key);
	return promisor != 0;
}

static int list_packs(git_vector *out, git_str *packdir, git_repository *repo)
{
	int error;

	if ((error = git_repository__item_path(packdir, repo, GIT_REPOSITORY_ITEM_OBJECTS)) < 0 ||
	    (error = git_str_joinpath(packdir, packdir->ptr, "pack")) < 0)
		return error;

	if (!git_fs_path_isdir(packdir->ptr))
		return 0;

	return git_fs_path_dirload(out, packdir->ptr, packdir->size + 1, 0);
}

/*
 * Mark each pack this fetch added as a promisor pack, with a
 * "<pack>.promisor" file beside it, as git's index-pack --promisor does.
 * git (fsck, gc, repack, and its own lazy fetch) uses the marker to tell
 * an object a partial clone omitted on purpose from one that is lost.
 */
static int mark_promisor_packs(git_repository *repo, git_vector *before)
{
	git_vector after = GIT_VECTOR_INIT;
	git_str packdir = GIT_STR_INIT, marker = GIT_STR_INIT;
	const char *name;
	size_t i, j;
	int error;

	if ((error = list_packs(&after, &packdir, repo)) < 0)
		goto done;

	git_vector_foreach(&after, i, name) {
		const char *seen;
		bool existed = false;
		size_t len = strlen(name);

		if (len < 5 || strcmp(name + len - 5, ".pack"))
			continue;

		git_vector_foreach(before, j, seen) {
			if (!strcmp(seen, name)) {
				existed = true;
				break;
			}
		}

		if (existed)
			continue;

		git_str_clear(&marker);
		if ((error = git_str_joinpath(&marker, packdir.ptr, name)) < 0)
			goto done;

		git_str_truncate(&marker, marker.size - 5);

		if ((error = git_str_puts(&marker, ".promisor")) < 0 ||
		    (error = git_futils_writebuffer(&marker, marker.ptr, O_CREAT | O_EXCL | O_WRONLY, 0444)) < 0) {
			if (error == GIT_EEXISTS) {
				git_error_clear();
				error = 0;
				continue;
			}
			goto done;
		}
	}

done:
	git_vector_dispose_deep(&after);
	git_str_dispose(&packdir);
	git_str_dispose(&marker);
	return error;
}

int git_fetch_download_pack(git_remote *remote)
{
	git_oidarray shallow_roots = { NULL };
	git_transport *t = remote->transport;
	git_vector packs_before = GIT_VECTOR_INIT;
	git_str packdir = GIT_STR_INIT;
	bool promisor = fetch_is_from_promisor(remote);
	int error = 0;

	if (remote->need_pack) {
		if (promisor &&
		    (error = list_packs(&packs_before, &packdir, remote->repo)) < 0)
			goto done;

		if ((error = t->download_pack(t, remote->repo, &remote->stats)) != 0 ||
		    (error = t->shallow_roots(&shallow_roots, t)) != 0)
			goto done;

		if (promisor &&
		    (error = mark_promisor_packs(remote->repo, &packs_before)) < 0)
			goto done;

		if ((error = git_repository__shallow_roots_write(remote->repo, &shallow_roots)) < 0)
			goto done;
	}

	if (remote->nego.filter_spec && !remote->fetching_oids)
		error = git_repository__set_partial_clone(
			remote->repo, remote->name, remote->nego.filter_spec);

done:
	git_oidarray_dispose(&shallow_roots);
	git_vector_dispose_deep(&packs_before);
	git_str_dispose(&packdir);
	return error;
}

int git_fetch_options_init(git_fetch_options *opts, unsigned int version)
{
	GIT_INIT_STRUCTURE_FROM_TEMPLATE(
		opts, version, git_fetch_options, GIT_FETCH_OPTIONS_INIT);
	return 0;
}

#ifndef GIT_DEPRECATE_HARD
int git_fetch_init_options(git_fetch_options *opts, unsigned int version)
{
	return git_fetch_options_init(opts, version);
}
#endif
