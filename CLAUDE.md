This is a rewrite of the Lean project from `../code/project/`. All code and
documentation in `./src/` will be written and edited exclusively by me, a human.

You MUST NOT create, delete, or edit any file in the `./src/` directory.

You MAY create, delete, or edit any file in the `./tests/` directory. The
purpose of the `./tests/` directory is to contain test files that support this
rewrite in the style of test-driven development (TDD). Tests in the `./tests/`
directory MAY be informed by insights gained from work done in the
`../code/project/` directory. However, tests should not impose
implementation-specific behavior from the `../code/project/` project on this
rewrite.

Tests added by a Claude Opus 4.8 agent MUST be audited, efficiently but
effectively, by a separate, independent Claude Opus 4.8 agent to ensure the
added or modified tests make sense mathematically and verify that after applying
the expected suggestions, declarations would still type-check in the context
(Lean file and location within it) in which they resided.

Tests added by a Fable 5 agent SHOULD NOT be audited by a separate agent.

Agents using a Claude model that is weaker than Opus 4.8 (for example, Opus 4.7,
Opus 4.6, Sonnet 4.6, or Haiku 4.5) MUST NOT create, delete, or edit any file in
this project, not even test files. These weaker models may only read files in
this project.
