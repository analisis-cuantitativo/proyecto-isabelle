-- Scope every `benchmark` row to a benchmark campaign (`version`) and record
-- the exact agent revision the pass ran on (`agent_revision`).
--
-- Motivation: the first campaign's analysis carries limitations that are
-- properties of *how it was run*, not of the data shape -- models saw
-- slightly different Isabelle interfaces (terra got an improved one), and
-- the grid was never completed for every model. A second campaign fixes
-- those, but only if v1 and v2 rows can be told apart and the conditions
-- each row ran under are recorded rather than asserted after the fact.
--
-- `version` is the campaign tag. Existing rows all belong to the first
-- campaign, so the column is added with `default 1`, which backfills them,
-- and the default is then dropped: after this migration every insert must
-- name its campaign explicitly, so an ad-hoc insert can't silently land in
-- v1 and contaminate the published numbers.
--
-- `agent_revision` is the git revision of the code that produced the pass
-- (`proyecto-isabelle@<sha>+DeepIsaHOL@<sha>`, see
-- `proyecto_isabelle.util.revision`). It stays nullable because v1 rows
-- genuinely predate it and NULL is the honest value there -- but the check
-- constraint below makes it mandatory from v2 onward, so "every model ran
-- against the same interface" becomes a claim you can verify with a
-- `select distinct agent_revision ... where version = 2` instead of one
-- that rests on the runner's memory.
--
-- Run this in the Supabase SQL editor, after
-- `0001_flatten_benchmark_to_per_pass.sql`. Safe to run more than once:
-- every statement is guarded.

alter table benchmark
    add column if not exists version smallint not null default 1,
    add column if not exists agent_revision text;

-- Backfill done by the `default 1` above; from here on inserts are explicit.
alter table benchmark
    alter column version drop default;

comment on column benchmark.version is
    'Benchmark campaign this pass belongs to. 1 = the original run reported '
    'in the OSE 26-4063-2026 report; 2 = the re-run under equalized '
    'conditions. Analysis must filter on this -- pooling campaigns silently '
    'mixes results produced under different agent interfaces.';

comment on column benchmark.agent_revision is
    'Git revision the pass ran on, as "proyecto-isabelle@<sha>+DeepIsaHOL@<sha>" '
    '(a "-dirty" suffix means uncommitted changes were present). NULL only for '
    'version 1 rows, which predate this column.';

-- From v2 onward a pass must say which code produced it.
do $$
begin
    if not exists (
        select 1 from pg_constraint
        where conname = 'benchmark_version_needs_revision'
    ) then
        alter table benchmark
            add constraint benchmark_version_needs_revision
            check (version = 1 or agent_revision is not null);
    end if;
end $$;

-- `get_missing_exercises_by_model` filters by (version, model_name) on every
-- run_all invocation; the dashboard and offline analysis filter by version.
create index if not exists benchmark_version_model_idx
    on benchmark (version, model_name);
