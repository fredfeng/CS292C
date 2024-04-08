# CS292C Computer-Aided Reasoning for Software

This course is a graduate level introduction to formal program verification techniques, and their application in tools for the design, analysis, and construction of software. In the first half of the course, we will survey the automated side of program verification -- introducing the logical foundations and algorithms behind SAT and SMT **solvers**. However, as we will see, the automated approach is inherently limited by the undecidability problem. Thus, in the second half of the course, we will turn to manual side, which aims to prove the correctness of programs with *manual proofs* machine-checked by an **interactive theorem prover**.

# Office hour

Instructor : Yu Feng

- Office hour: TBD

TA/Tutorial Instructor: Junrui Liu (junrui@ucsb.edu)

- Office hour: 2pm-3pm, Friday, Place TBD

Lecture Time: 11am-12:50pm, M/W, Phelps 3526

Slack: https://join.slack.com/t/cs292c-spring24/shared_invite/zt-2g1hpa39v-OjeYeMBPG1uMa7fCGcujqQ


| #   | Date | Lecture                                               | Tutorial                                          | Out                            | Due |
| --- | ---- | ----------------------------------------------------- | ------------------------------------------------- | ------------------------------ | --- |
| 1   | 4/1  | [Overview](./lectures/lecture1.pdf)                   | Dafny ([demo.dfy](./tutorials/01-dafny/demo.dfy)) | [hw1](/homework/hw1/README.md) |
| 2   | 4/3  | [IMP: Syntax & Semantics](./lectures/lecture2.pdf)                               | OCaml: Basics, Data Types                         |
| 3   | 4/8  | [Hoare Logic 1](./lectures/lecture3.pdf)                                        | OCaml: Recursive Types                            |                                | hw1 |
| 4   | 4/10 | Hoare Logic 2                                         | OCaml: Refs, Modules                              |
| 5   | 4/15 | Guarded Commands, VC Gen                              | Project 1 Walkthrough, z3                         |
| 6   | 4/17 | SMT Solvers: Overview                                 |                                                   |
| 7   | 4/22 | SAT: Basics, DPLL                                     |                                                   |
| 8   | 4/24 | SAT: CDCL                                             |                                                   |
| 9   | 4/29 | SAT: Extensions & Applications; Theory of Bit-Vectors |                                                   |
| 10  | 5/1  | More Theories: Uninterpreted Functions, Arrays        |                                                   |
| 11  | 5/6  | More Theories: LIA, LRA                               |                                                   |
| 12  | 5/8  | Nelson-Oppen                                          |                                                   |
| 13  | 5/13 | DPLL(T)                                               |                                                   |
| 14  | 5/15 | (TBD)                                                 |                                                   |
| 15  | 5/20 |                                                       |                                                   |
| 16  | 5/22 | -                                                     | -                                                 |
| 17  | 5/27 | Symbolic Execution                                    |                                                   |
| 18  | 5/29 | Program Synthesis                                     |                                                   |
| 19  | 6/3  | Solver-Aided Programming                              |                                                   |
| 20  | 6/5  | (Research Topics)                                     | -                                                 |
| -   | 6/14 | (Quarter Ends)                                        |                                                   |


# Grading (No curving)

| Letter | Percentage |
| ------ | ---------- |
| A+     | 95–100%    |
| A      | 90–94%     |
| A-     | 85–89%     |
| B+     | 80–84%     |
| B      | 75–79%     |
| B-     | 70–74%     |
| C+     | 65–69%     |
| C      | 60–64%     |
| F      | <60%       |

- Weekly written assignments: 40%
   - Self-graded on **effort** on a scale of 0-2, but will be checked by the TA:
     - 0: problem not attempted at all
     - 1: problem attempted, but not fully solved, and all work shown
     - 2: problem fully solved
   - *A self-grade of 1 is enough to get full credit for a problem.*

- 3 programming projects: 60%



# Late Policy
You have a total of 10 late days to be used throughout the quarter. You can use them in any way you like.



# Academic Integrity
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



# References

- Rondon, Patrick M., Ming Kawaguci, and Ranjit Jhala. "Liquid types." PLDI'2008.

- Ali Sinan Köksal, Yewen Pu, Saurabh Srivastava, Rastislav Bodík, Jasmin Fisher, Nir Piterman. Synthesis of biological models from mutation experiments. Principles of Programming Languages (POPL). 2013. ACM DL

- Srivastava, Saurabh, Sumit Gulwani, and Jeffrey S. Foster. From program verification to program synthesis. POPL 2010.

- Jha, Susmit, et al. Oracle-guided component-based program synthesis. ICSE 2010.

- Gulwani, Sumit. Automating string processing in spreadsheets using input-output examples. POPL 2011.

- Phothilimthana, Phitchaya Mangpo, et al. "Scaling up superoptimization." ASPLOS 2016.

- Chandra, Kartik, and Rastislav Bodik. Bonsai: synthesis-based reasoning for type systems. POPL 2017.

- Bornholt, James, et al. Optimizing synthesis with metasketches. POPL 2016.

- Yaghmazadeh, Navid, et al. SQLizer: query synthesis from natural language. OOPSLA 2017. **Distinguished Paper Award**

- Deepcoder: Learning to write programs. Matej, et al. ICLR'16.

- Helgi Sigurbjarnarson, James Bornholt, Emina Torlak, and Xi Wang. Push-Button Verification of File Systems via Crash Refinement. OSDI 2016. **Best Paper Award**

- Shaon Barman, Sarah E. Chasins, Rastislav Bodik, Sumit Gulwani. Ringer: web automation by demonstration. OOPSLA 2016.

- Luke Nelson, Jacob Van Geffen, Emina Torlak, and Xi Wang. Specification and verification in the field: Applying formal methods to BPF just-in-time compilers in the Linux kernel. OSDI 2020.

- Chenming Wu, Haisen Zhao, Chandrakana Nandi, Jeff Lipton, Zachary Tatlock, Adriana Schulz. Carpentry Compiler. SIGGRAPH ASIA 2019.

- Permenev, Anton, et al. Verx: Safety verification of smart contracts. 2020 IEEE Symposium on Security and Privacy 2020.

- Chenglong Wang, Yu Feng, Ras Bodik, Alvin Cheung, Isil Dillig. Visualization by Example. POPL'2020.

- Beckett, Ryan, et al. Network configuration synthesis with abstract topologies. PLDI'2017.

- Dai, Wang-Zhou, et al. Bridging machine learning and logical reasoning by abductive learning. NIPS'2019.



