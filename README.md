# CS292C Formal Methods for Agentic Programming

This is a graduate seminar at UC Santa Barbara on the intersection of formal methods and AI coding agents. The emergence of autonomous coding agents (Claude Code, Cursor, Codex) has fundamentally changed software development: "programming" is now a goal-directed, multi-step interaction where LLMs autonomously decompose tasks, invoke tools, and refine outputs based on environment feedback. This course confronts the resulting verification challenge: **how do we guarantee correctness, security, and efficiency when the programmer is itself an agent?**

The course has four tightly integrated parts. Part I establishes the agentic programming paradigm. Part II introduces formal methods (Hoare logic, SAT/SMT, static analysis, model checking) as **the foundation**, with each technique immediately applied to an agentic problem. A midterm at the end of Part II consolidates this foundation. Part III tackles the full threat landscape — from skill supply-chain attacks to permission escalation — using the formal tools just learned. Part IV merges hardening, efficiency optimization, and frontier research into a capstone module.

# Office Hour

Instructor: Yu Feng

- Office hour: 1:30pm–2:30pm, Tuesday, HFH 2157

Lecture Time: 3pm–4:50pm, T/Th, Phelps 3526

Slack: TBD

# Course Schedule

| #   | Date   | Lecture                                              | Out  | Due  |
| --- | ------ | ---------------------------------------------------- | ---- | ---- |
| **Part I: Foundations of Agentic Programming** |||||
| 1   | 3/31   | The Agentic Programming Revolution                   |      |      |
| 2   | 4/2    | Building Agents: API, Tool Use & MCP                 |      |      |
| 3   | 4/7    | Agent Skills as Executable Infrastructure            | HW1  |      |
| 4   | 4/9    | Multi-Agent Orchestration & Workflow Patterns        |      |      |
| 5   | 4/14   | From Agent Behavior to Formal Specification          |      |      |
| **Part II: Formal Methods — The Foundation** |||||
| 6   | 4/16   | Hoare Logic I — Triples for Programs and Agents      |      | HW1  |
| 7   | 4/21   | Hoare Logic II — VCG and Weakest Preconditions       |      |      |
| 8   | 4/23   | SAT/SMT Solvers for Agent Policy Verification        | HW2  |      |
| 9   | 4/28   | Static Analysis: From Dataflow to Skill Auditing     |      |      |
| 10  | 4/30   | Model Checking Agentic Traces                        |      |      |
| 11  | 5/5    | **Midterm** (In Class)                               |      | HW2  |
| **Part III: Security of Agentic Systems** |||||
| 12  | 5/7    | Threat Landscape of Agentic Systems                  |      |      |
| 13  | 5/12   | Skill Supply-Chain Attacks                           | HW3  |      |
| 14  | 5/14   | Permission Escalation & Formal Access Control        |      |      |
| 15  | 5/19   | Fuzzing and Behavioral Testing of Agent Skills       |      |      |
| 16  | 5/21   | Full-Lifecycle Formal Defenses                       |      | HW3  |
| **Part IV: Hardening, Efficiency & the Frontier** |||||
| 17  | 5/26   | Runtime Guardrails & Agent Hardening                 | HW4  |      |
| 18  | 5/28   | Efficiency: Token Optimization & Caching             |      |      |
| 19  | 6/2    | The Frontier: Verified Agentic Systems               |      |      |
| 20  | 6/4    | **Student Project Presentations & Wrap-up**          |      | HW4  |

## Grading (No curving)

| Letter | Percentage |
| ------ | ---------- |
| A      | 93–100%    |
| A-     | 85–92%     |
| B+     | 80–84%     |
| B      | 75–79%     |
| B-     | 70–74%     |
| C+     | 65–69%     |
| C      | 60–64%     |
| F      | <60%       |

- HW1: Build & Test an Agent Skill — 10%
- HW2: Formal Verification of Programs and Policies — 10%
- HW3: Security Audit & Fuzzing — 12%
- Midterm (In Class, Lecture 11) — 30%
- HW4: Final Research Project — 30% (Code 12% + Report 8% + Lightning Talk 10%)
- Participation & Peer Review — 8%

8 free late days across all assignments.

## 🗂️ Course Outline

### Part I: Foundations of Agentic Programming (Weeks 1–2)

1. **The Agentic Programming Revolution**
   From manual coding to autonomous agents. The reasoning loop: LLM as brain, tools as body. Comparison with classical program synthesis. Course logistics and project overview.

2. **Building Agents: API, Tool Use & MCP**
   Anthropic Claude API: Messages API, tool calling, extended thinking. Model Context Protocol (MCP): primitives (tools, resources, prompts), building servers and clients. Hands-on lab.

3. **Agent Skills as Executable Infrastructure**
   SKILL.md format, frontmatter metadata, progressive disclosure. Skills as persistent, portable, governance-bearing artifacts. The OpenClaw/ClawHub ecosystem (13,700+ skills). The GATE taxonomy: Grounding, Action, Transfer, Exchange.

4. **Multi-Agent Orchestration & Workflow Patterns**
   Subagent delegation, role-based decomposition. Design patterns (pipeline, coordinator-dispatcher, generator-critic, human-in-the-loop). Attention degradation and how structured roles mitigate it.

5. **From Agent Behavior to Formal Specification**
   What makes agent behavior hard to verify: non-determinism, tool side-effects, intent ambiguity. Mapping agentic components to formal equivalents (reasoning loop → transition system, tools → effectful commands, context window → working memory, skills → modular specs).

📘 **HW1**: Build a functional skill (Claude Code or OpenClaw) with proper SKILL.md, a multi-step workflow, and a behavioral eval suite.

---

### Part II: Formal Methods — The Foundation (Weeks 3–5)

6. **Hoare Logic I — Triples for Programs and Agents**
   Classical Hoare triples {P} C {Q} for IMP. Re-interpretation for agents: P = context + environment state, C = AgentDecide(tool_call), Q = post-state. Rules for assignment, sequencing, conditionals, loops.

7. **Hoare Logic II — VCG and Weakest Preconditions**
   Verification condition generation (VCG). Dijkstra's weakest precondition calculus. Running example: verifying that an agent's file-edit tool call satisfies directory-isolation pre-conditions.

8. **SAT/SMT Solvers for Agent Policy Verification**
   Propositional logic, CNF, DPLL, CDCL. First-order theories (EUF, LIA, arrays). Z3 hands-on. Application: encoding agent permission policies as SMT formulas.

9. **Static Analysis: From Dataflow to Skill Auditing**
   Abstract interpretation, taint tracking, dataflow analysis. Industrial tools: Infer, CodeQL. Bridge to agents: taint analysis on SKILL.md to detect prompt injection directives and credential exfiltration patterns.

10. **Model Checking Agentic Traces**
    Agent lifecycles as state transition systems. Temporal logic (LTL/CTL) for safety and liveness properties. Intent alignment: proving all execution traces satisfy user intent. The four formalization levels: step-, skill-, trace-, and system-level.

📝 **Midterm** (Lecture 11): Closed-book, closed-note. Covers Lectures 1–10.

📘 **HW2**: Implement a Hoare-logic verifier for IMP that generates VCs via Z3; write an SMT encoding of an agent permission policy.

---

### Part III: Security of Agentic Systems (Weeks 6–8)

11. **Threat Landscape of Agentic Systems**
    OWASP Top 10 for LLM Apps. Three-stage risk taxonomy: input boundary (indirect prompt injection), cognitive/collaboration (agent spoofing), system boundary (tool poisoning). Case studies from OpenClaw analysis.

12. **Skill Supply-Chain Attacks**
    Snyk ToxicSkills study (36% prompt injection rate). ClawHavoc campaign: AMOS macOS Stealer via malicious SKILL.md. Static analysis of YAML metadata for policy violations (SkillScanner). Connection to Prof. Feng's OpenClaw skill bug detection research.

13. **Permission Escalation & Formal Access Control**
    Confused deputy problem for agents. Tool permission inheritance. Privilege escalation via MCP tool chaining. MiniScope: mobile-style permission model from tool-call relationships. Connection to Prof. Feng's permission escalation research.

14. **Fuzzing and Behavioral Testing of Agent Skills**
    Adapting fuzzing to non-deterministic LLM agents. Data-flow-guided fuzzing (FuzzRDUCC). Multi-agent collaborative testing (Elevate: Observer/Generator/Planner with DFA models). Connection to Prof. Feng's fuzzing research.

15. **Full-Lifecycle Formal Defenses**
    Defense-in-depth: perception (input sanitization), decision (static skill auditing), execution (ephemeral sandboxing), governance (decentralized trace archiving). Encoding safety policies as Hoare-style contracts. SMT-based runtime monitors for tool-call sequences.

📘 **HW3**: Audit 20+ real ClawHub skills via static analysis; implement a taint analyzer detecting credential exfiltration, prompt injection, and unauthorized network calls; reproduce at least one known attack in a sandbox.

---

### Part IV: Hardening, Efficiency & the Frontier (Weeks 9–10)

16. **Runtime Guardrails & Agent Hardening**
    Circuit breakers, semantic firewalls, action control protocols. Sandboxing (ephemeral containers, restricted egress). Integrating formal monitors into production agent loops.

17. **Efficiency: Token Optimization & Caching**
    Token economics: prefill latency, input/output cost asymmetry. Prompt caching (Anthropic cache_control). Semantic caching (Redis). KV cache reuse. Prompt compression (LLMLingua). Hierarchical context compression. Model routing by task complexity.

18. **The Frontier: Verified Agentic Systems**
    Neuro-symbolic reasoning for agents. Self-improving agents (OpenClaw-RL). The GATE taxonomy revisited: language as executable infrastructure. Open research challenges. Guest lecture / invited talk.

📘 **HW4 (Final Research Project)**: Choose one track — (A) Verified Agent Policies, (B) Skill Fuzzer, (C) Efficiency Optimizer, or (D) Open Research. Deliverable: codebase, README, 4–6 page report, 10-min lightning talk at Lecture 20.

---

## 🛠 Tools & Resources

**Agent Frameworks**
- [Anthropic Claude API & Claude Code](https://docs.anthropic.com) — primary agent development platform
- [Model Context Protocol (MCP) SDK](https://github.com/anthropics/mcp)
- OpenClaw & ClawHub — open-source agentic AI for security case studies

**Formal Methods Tools**
- [Z3 SMT Solver](https://github.com/Z3Prover/z3)
- [Dafny](https://github.com/dafny-lang/dafny) / [Lean Prover](https://leanprover.github.io/)
- [Meta Infer](https://fbinfer.com/) / [CodeQL](https://codeql.github.com/)

**Security & Efficiency**
- ClawHub Skills Registry & Snyk ToxicSkills dataset
- OWASP Top 10 for LLM Applications
- LLMLingua, Langfuse, LiteLLM — token optimization and monitoring

---

## 📅 Key Dates

- **HW1 out**: Lecture 3 (4/7) | **due**: Lecture 6 (4/16)
- **HW2 out**: Lecture 8 (4/23) | **due**: Lecture 11 (5/5)
- **Midterm**: Lecture 11 (5/5)
- **HW3 out**: Lecture 13 (5/12) | **due**: Lecture 16 (5/21)
- **HW4 out**: Lecture 17 (5/26) | **due**: Lecture 20 (6/4)
- **Final Presentations**: Lecture 20 (6/4)

---

## Academic Integrity

Using AI coding assistants is **permitted and encouraged** — this is a course about agentic programming. Students must understand and be able to explain every line of submitted code. The instructor reserves the right to conduct oral examinations. All external code, prompts, and AI-generated content must be attributed. Sharing solutions or using prior-offering work constitutes academic dishonesty.

- **Not cheating**: discussing broad ideas about assignments in groups, without sharing code.
- **Cheating**: looking at another student's solution, using solutions from previous offerings, or leaving your code visible in a public repository.
- **Penalties**: First offense — zero on the assignment; Second offense — F in the course.
