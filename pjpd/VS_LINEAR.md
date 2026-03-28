# When to Move from pjpd to Linear

pjpd is a local task tracker that lives in your repo and is operated by an AI assistant over MCP. It has no accounts, no network, no UI — just text files and conversation. That simplicity is the point.

Linear is a cloud-hosted project management tool built for software teams. It has a fast keyboard-driven UI, deep GitHub/Slack integrations, sprint cycles, roadmaps, and team workflows.

This doc isn't a feature matrix. It's a guide to the pressure points that would push you from one to the other.

## Where pjpd is enough

pjpd works well when the work fits in your head and the AI's context window. Specifically:

- **Solo or pair work.** You're the only one who needs to see the task list. The AI assistant is your collaborator, not a teammate who needs their own login.
- **Single-project focus.** You're working in one repo at a time. Tasks and ideas belong to that repo and don't need to reference work elsewhere.
- **Short-lived tasks.** Tasks track what to do in this session or this week, not quarterly commitments. They get created, worked, and marked done within a few coding sessions.
- **The AI does the bookkeeping.** You don't browse a dashboard. You say "what's left?" and the LLM reads the file and tells you. The overhead of managing tasks is near zero because the AI handles it inline.
- **Plain text is a feature.** The task file is committable, diffable, greppable. There's no vendor lock-in and no sync to break.

If this describes your workflow, Linear would add friction without adding value.

## Signals that you've outgrown pjpd

### 1. Someone else needs to see the work

The moment a second person needs to know what you're working on — a manager checking status, a teammate picking up a task, a designer waiting on a dependency — pjpd has no answer. There are no assignees, no shared views, no notifications. You'd be copy-pasting from a text file into Slack.

**Linear gives you:** assignees, team views, @mentions, an inbox, Slack integration, and guest access. The work becomes visible without you narrating it.

### 2. Tasks need more than two states

pjpd has ToDo and Done. That's fine when the AI is doing the work in a single session. But when tasks sit in progress for days, get blocked by external dependencies, go through review, or need triage before they hit the backlog — two states aren't enough.

**Linear gives you:** customizable per-team workflows (Backlog, Todo, In Progress, In Review, Done, Cancelled), plus automations that move issues between states based on PR activity or rules you define.

### 3. You need to plan across time

pjpd has priority but no dates. There are no sprints, no milestones, no "what are we shipping this week vs next month." If you find yourself mentally bucketing tasks into time horizons — or worse, encoding time into priority numbers — the model is straining.

**Linear gives you:** cycles (sprints) with capacity planning and burndown charts, project milestones with target dates, and roadmap views that lay projects out on a timeline.

### 4. Tasks start depending on each other

pjpd tasks are independent flat items. When you need to express "this blocks that," "these three things are subtasks of that epic," or "this is a duplicate of something filed last week" — you're back to encoding structure in description text.

**Linear gives you:** sub-issues, blocking/blocked-by relations, duplicate detection, and projects that group related issues with progress tracking.

### 5. You want the tools to talk to each other

pjpd lives in the repo. It doesn't know about your PRs, your error tracker, your support queue, or your design files. If closing a PR should close a task, you do it manually (or the AI does, if you remember to ask).

**Linear gives you:** GitHub/GitLab integration (auto-link branches and PRs, auto-transition on merge), Sentry integration (link errors to issues), Slack (create issues from messages), Figma embeds, and a GraphQL API for anything custom.

### 6. You need to measure the work

pjpd can count tasks by priority and status. That's it. If you want to know your velocity over time, whether you're on track for a deadline, how scope changed mid-sprint, or which area of the codebase generates the most work — the data isn't there.

**Linear gives you:** cycle velocity trends, project progress percentages, SLA compliance tracking, workload distribution across team members, and filterable views that serve as ad-hoc reports.

## What you'd lose

Moving to Linear isn't free. You give up things that matter:

- **Zero friction.** pjpd tasks are created in conversation as a side effect of working. Linear requires context-switching to a browser or app, even with keyboard shortcuts.
- **AI-native operation.** The LLM reads and writes pjpd directly. With Linear, the AI would need API integration (Linear does have an MCP server, but it's a different interaction model than local file access).
- **Repo-local data.** pjpd tasks live next to the code. They're in your git history. They work offline, on a plane, on an air-gapped machine. Linear needs a network.
- **Simplicity.** pjpd has seven tools and two entity types. Linear has hundreds of concepts to configure. Even with good defaults, there's an adoption curve.
- **Free, forever.** pjpd has no pricing tiers, no seat limits, no feature gates.

## The hybrid option

You don't have to choose. The two tools address different scopes:

- **Linear** tracks the team backlog: what's committed for the sprint, who owns what, how the project is progressing, what stakeholders can see.
- **pjpd** tracks the working session: the sub-tasks the AI is stepping through right now, the ideas that came up while debugging, the things that don't deserve a Linear issue yet.

A typical flow: pull a Linear issue, break it down into pjpd tasks with the AI, work through them, mark them done, then close the Linear issue. pjpd is scratch paper; Linear is the record of truth.

## Closing the gap from the pjpd side

Not every pressure point requires jumping to Linear. Some can be addressed with targeted additions to pjpd that preserve its simplicity. The key constraint: every feature must work through conversation with the AI over MCP, stored in plain text. Anything that needs a UI, a server, or multi-user coordination is out of scope — that's where Linear starts.

### Feasible: stays true to pjpd's nature

**A `blocked` status.** Adding a third state (ToDo, Blocked, Done) would let the AI flag tasks that are waiting on something external without losing them in the active list. Low cost: one more status string, a filter tweak, and the AI can explain *why* it's blocked in the description. This addresses pressure point #2 without a full workflow engine.

**A `due` field on tasks.** A plain date (no time, no recurrence) would let the AI sort by urgency vs. importance and warn about upcoming deadlines. The AI already reasons about time — giving it a field to record "by when" means it can answer "what's overdue?" instead of you remembering. This addresses pressure point #3 at the lightest possible weight.

**Cross-references between tasks.** A convention like `see: task-a2c4` in the description is already possible, but a formal `Blocked-By: task-x9y2` header would let the AI reason about dependency chains. No sub-task hierarchy, no graph — just "this one is waiting on that one." Addresses pressure point #4 for the common case.

**Promote idea to task.** Right now converting an idea to a task means creating a new task and marking the idea done — two calls with manual description copying. A `pjpd_promote_idea` tool that does this atomically would tighten the ideas-to-tasks pipeline. Small but removes friction from a natural workflow.

**Richer statistics over time.** The backup files in `bak/` are an untapped history. A tool that diffs the current state against recent backups could report tasks completed this week, score trends on ideas, or net task growth — giving you basic velocity without any new storage. Addresses pressure point #6 with data you already have.

### Stretch: possible but adds real complexity

**Multi-project awareness.** A `pjpd_list_projects` tool that scans sibling directories for `pjpd/` folders would let the AI answer "what else am I tracking?" without leaving the conversation. No shared state, no cross-project dependencies — just awareness. The AI could surface "you have 3 blocked tasks in the other repo" as context. Partially addresses pressure point #1 (visibility) for a solo developer working across repos.

**Git-aware task lifecycle.** Since pjpd already lives in the repo, a tool that reads `git branch` or `git log` could auto-suggest marking tasks done when a branch merges, or link a task to the branch it was worked on. This is the pjpd-native version of Linear's GitHub integration — no webhook, just local git state. Addresses pressure point #5 for the single tool that matters most.

### Out of scope: this is where you actually need Linear

Some gaps can't be closed without changing what pjpd is:

- **Multi-user visibility.** Assignees, shared views, notifications, and access control all require a server and user accounts. Bolting these onto local text files would produce a worse version of Linear.
- **Automations and workflows.** Rule engines ("when PR merges, move to Done") need an event system. pjpd is request-response through an AI — there's no daemon running to trigger rules.
- **Rich integrations.** Slack, Sentry, Figma, and Zendesk integrations require API credentials, webhooks, and ongoing maintenance. Each one is its own MCP server-sized project.
- **Team analytics.** Velocity across people, workload distribution, and SLA compliance require multi-user data that doesn't exist locally.

These are the hard walls. When you hit them, it's time for Linear — and pjpd becomes the local scratch layer underneath it.

## Summary

| You should stick with pjpd if... | You should move to Linear if... |
|---|---|
| You work solo with an AI assistant | Someone else needs to see the task list |
| Tasks live and die within a few sessions | Tasks persist for weeks with status changes |
| Priority is enough to order work | You need dates, sprints, and milestones |
| Tasks are independent flat items | Tasks have dependencies and hierarchy |
| Your repo is the only system that matters | You need GitHub, Slack, and Sentry integration |
| "How many are left?" is the only metric | You need velocity, burndown, and SLA tracking |

## A note on architecture

The feasible and stretch improvements above shouldn't live in pjpd itself. pjpd is a storage and CRUD layer — it reads, writes, and queries tasks and ideas in plain text. That's its job and it does it cleanly.

The gap-closing features (dependency reasoning, due date awareness, cross-repo visibility, git-state correlation) are *coordination* concerns. They reason about relationships between things, not the things themselves. That's a separate tool — a project-manager layer that consumes pjpd (and potentially other MCP servers like git) as data sources, and exposes higher-level tools: "what's blocking progress," "what's overdue across my repos," "this branch landed, what tasks does that close."

This separation has a practical benefit: it keeps pjpd's API stable and simple regardless of what sits on top. If the coordination layer is a custom MCP server today and Linear tomorrow, pjpd doesn't change. It stays the local scratch layer either way.
