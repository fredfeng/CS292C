# CS292C Computer-Aided Reasoning for Software

This course is a graduate level introduction to formal program verification techniques, and their application in tools for the design, analysis, and construction of software. In the first half of the course, we will survey the automated side of program verification -- introducing the logical foundations and algorithms behind SAT and SMT **solvers**. However, as we will see, the automated approach is inherently limited by the undecidability problem. Thus, in the second half of the course, we will turn to manual side, which aims to prove the correctness of programs with *manual proofs* machine-checked by an **interactive theorem prover**.

# Office hour

Instructor : Yu Feng

- Office hour: 9am-10am, Tuesday, HFH 2157

Lecture Time: 1pm-2:50pm, T/TR, Phelps 3526

Slack: https://join.slack.com/t/cs292c-spr2025/shared_invite/zt-32f16k4ic-UFmQK9Sr6eGWBECoebHwRQ

| #   | Date  | Lecture                                                                 | Out                        | Due   |
| --- | ----- | ----------------------------------------------------------------------- | -------------------------- | ----- |
| 1   | 4/1   | [Overview & Motivation](https://cs292c-1-computer-aided--coq3g7p.gamma.site/)                        |      |       |
| 2   | 4/3   | [IMP: Syntax & Semantics](https://cs292c-2-computer-aided--djjky8d.gamma.site/)                      |                            |       |
| 3   | 4/8   | [Hoare Logic I](https://cs292c-3-computer-aided--jw6kwbl.gamma.site/)                                 |                            |       |
| 4   | 4/10  | [Ocaml in a Nutshell](https://ocaml-crash-course-f3bila9.gamma.site/)                         |                            |    |
| 5   | 4/15  | [Hoare Logic II + VCG](https://cs292c-4-computer-aided--xb19i4z.gamma.site/)                        | [hw1](./projects/proj1)     |       |
| 6   | 4/17  | [Hoare Logic II + VCG](https://cs292c-4-computer-aided--xb19i4z.gamma.site/)                            |                            |       |
| 7   | 4/22  | [SAT Basics: CNF, DPLL](https://cs292c-5-computer-aided--o4c5z7q.gamma.site/)        |                            |       |
| 8   | 4/24  | [SAT Solvers: CDCL](https://cs292c-6-computer-aided--1pq10d8.gamma.site/)          |                            |    |
| 9   | 4/29  | [Application of SAT](https://cs292c-7-computer-aided--igcai21.gamma.site/)                     |      [hw2](./projects/proj2)                      |  hw1     |
| 10  | 5/1   | [SMT Solvers and Theories](https://cs292c-8-computer-aided--328ag8m.gamma.site/)            |                         |       |
| 11  | 5/6   | [Nelson-Oppen Combination](https://cs292c-9-computer-aided--874veey.gamma.site/)    |                            |       |
| 12  | 5/8   | [DPLL(T): SMT Solver](https://cs292c-10-computer-aided-jpp64js.gamma.site/ )      |      |       |
| 13  | 5/13  | **Midterm** (In Class)                                                  |   [final project](https://github.com/fredfeng/CS292C/tree/master/projects/final)                           |  hw2     |
| 14  | 5/15  |  No Class (Out of Town)                |                            |       |
| 15  | 5/20  |  [Program Synthesis: Overview](https://cs292c-11-computer-aided-cylhkgo.gamma.site/)                                                 |                            |       |
| 16  | 5/22  | [Conflict-Driven Synthesis](https://cs292c-12-computer-aided-kjdrsmy.gamma.site/)                 |                          |       |
| 17  | 5/27  | [Symbolic Execution](https://cs292c-13-computer-aided-wov8soc.gamma.site/)     |                            |       |
| 18  | 5/29  | [Program Repair](https://cs292c-14-computer-aided-ax75p3i.gamma.site/)          |                            |       |
| 19  | 6/3   | [LLM/AI for Formal Methods](https://cs292c-15-computer-aided-fv7i6d6.gamma.site/) |                    |       |
| 20  | 6/5   | **Student Presentations + Wrap-up**                                      |                            |   final project |
| -   | 6/14  | **Quarter Ends**                                                         |                            |       |



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

- 2 programming projects: 24%
- Midterm (closed book, closed note): 40%
- Final project: 30%
   - Well-documented README: 10%
   - Complete, executable codebase: 13%
   - Lightning talk: 12%

## 🗂️ Course Outline

### Part I: Foundations of Program Reasoning (Weeks 1–2)
1. **Overview & Motivation**  
   Introduction to software verification, real-world motivation, course logistics

2. **IMP: Syntax & Semantics**  
   Big-step and small-step semantics for a simple imperative language

3. **Hoare Logic I**  
   Hoare triples, rules for sequencing, conditionals, and loops

4. **Hoare Logic II + Verification Condition Generation (VCG)**  
   Derivation rules, soundness, and VCG overview

📘 **Assignment 1**: Implement a Hoare-style verifier for a subset of IMP

---

### Part II: Logic & Solvers (Weeks 3–4)
5. **SAT Solving Basics: CNF, DPLL**  
   Propositional logic, SAT solving, DPLL algorithm

6. **CDCL and Practical SAT Solvers**  
   Conflict-driven clause learning, watched literals

7. **SMT Solvers Overview + Theories (EUF, Arrays)**  
   First-order logic, SMT solvers, uninterpreted functions

8. **SMT with Arithmetic: LIA, LRA, Bitvectors**  
   Numeric theories and solver support

📘 **Assignment 2**: Use Z3/CVC5 to solve verification tasks

---

### Part III: Programs + Solvers (Weeks 5–6)
9. **Guarded Commands & Weakest Preconditions (WP)**  
   Dijkstra’s weakest precondition calculus, symbolic reasoning

10. **Interprocedural Reasoning & Invariants**  
    Procedure summaries, loop invariants, invariant inference

11. **Nelson-Oppen Combination**  
    Combining theories in SMT solving

12. **DPLL(T): Architecture of Modern SMT Solvers**  
    How SAT and theory solvers interact in tools

📝 **Midterm** (Week 6): Covers Lectures 1–12

---

### Part IV: From Verification to Synthesis (Weeks 7–9)
13. **Introduction to Program Synthesis**  
    Syntax-guided synthesis (SyGuS), relation to verification

14. **CEGIS & Inductive Synthesis**  
    Counterexample-guided synthesis, invariant synthesis

15. **Solver-Aided Programming (Rosette)**  
    Symbolic execution for testing and synthesis

16. **Verification Tools in Practice**  
    Overview of Dafny, Why3, Frama-C, etc.

17. **Synthesis for Program Repair & Bug Finding**  
    Automated repair, angelic execution, fuzzing vs. synthesis

📘 **Assignment 3**: Use Rosette (or similar) to synthesize or repair a small program

---

### Part V: Final Presentations & Wrap-up (Week 10)
18. **Student Presentations I**  
    Project demos, paper talks, or tool evaluations

📘 **Final Project**   
Design a verifier, explore a synthesis/repair technique, or evaluate a tool on a real-world program

---

## 🧠 Learning Outcomes

By the end of this course, students will be able to:

- Reason about program correctness using formal methods  
- Encode verification conditions and solve them using SMT solvers  
- Build simple verifiers and synthesizers using modern tools  
- Understand and critique state-of-the-art verification research  

---

## 🛠 Tools & Resources

- [Z3 SMT Solver](https://github.com/Z3Prover/z3)  
- [Rosette](https://emina.github.io/rosette/)  
- [Dafny](https://github.com/dafny-lang/dafny)  
- [Why3](http://why3.lri.fr/)

---

## 📅 Key Dates

- **Midterm**: Week 6 (May TBD)  
- **Final Presentations**: Week 10 (June TBD)  
- **Assignment Deadlines**: To be posted on course page  



## Academic Integrity
- Cheating WILL be taken seriously. It is not fair toward honest students to take cheating lightly, nor is it fair to the cheater to let him/her go on thinking that cheating is a reasonable alternative in life.
- The following is not considered cheating:
   - discussing broad ideas about programming assignments in groups, without being at a computer (with code-writing and debugging done individually, later).
- The following is considered cheating:
   - discussing programming assignments with someone who has already completed the problem, or looking at their completed solution.
   - looking at anyone else’s solution
   - Previous versions of the class.
   - leaving your code (for example in an online repository) visible to others, leading others to look at your solution.
   - receiving, providing, or soliciting assistance from unauthorized sources during a test.
- Programming assignments are not intended to be grade-makers, but to prepare you for the tests, which are the grade-makers. Cheating on the programming assignment is not only unethical, but shows a fundamental misunderstanding of the purpose of these assignments.
- Penalties: First time: a zero for the assignment; Second time: an “F” in the course.





