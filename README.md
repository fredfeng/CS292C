# CS292C Computer-Aided Reasoning for Software

This course is a graduate level introduction to automated reasoning techniques and their application in tools for the design, analysis, and construction of software. In the first half of the course, we will survey the logical foundations and algorithms behind SAT solvers and SMT solvers. In the second half of the course, we will apply these techniques to automatic bug finding, program verification, and program synthesis. As a student in this course, you will learn how solvers work, and how to use them to build cool programming tools!

# Office hour
Instructor : Yu Feng

Lecture Time: 1pm-2:30pm, M/W, Phelps 2510

Office hour: 2:30pm-3:30pm, Wed, PLSE Lab. Phelps 3523

Slack: https://join.slack.com/t/slack-bqf3594/shared_invite/zt-161uioa1i-uQFsfotbR6Hsv1yy~z7dqw


| Date  | Topic                                         | Slides | Read | Out | Due |
|-------|-----------------------------------------------|--------|------|-----|-----|
| 3/28  | Introduction                                  |  [lec1](lectures/lecture1.pdf)      |      |     |     |
| 3/30  | Solver-Aided Programming I (Rosette)          |  [lec2](lectures/lecture2.pdf)      |  R1    |  [HW1](hw1/HW1.md)   |     |
| 4/4  | Solver-Aided Programming II (Neo)             |  [lec3](lectures/lecture3.pdf)      |  R2    |     |     |
| 4/6  | SAT Solving Basics                            |  [lec4](lectures/lecture4.pdf)     |      |     | R1    |
| 4/11 | A Modern SAT Solver                           |  [lec5](lectures/lecture5.pdf)      |      |   [HW2](hw2/HW2.md)  |   HW1  |
| 4/13 | Applications of SAT                           |  [lec6](lectures/lecture6.pdf)      |  R3    |     |  R2   |
| 4/18 | SAT Modulo Theories                           |  [lec7](lectures/lecture7.pdf)      |      | HW3    |  HW2   |
| 4/20 | Combining Theories              | [lec8](lectures/lecture8.pdf)        |      |    |  R3   |
| 4/25 | The DPLL(T) Framework                             |  [lec9](lectures/lecture9.pdf)       |      |     |     |
| 4/27 | The DPLL(T) Framework II                       |  [lec10]       |  R4    |     |  Proposal (2 pages)   |
| 5/2  | Reasoning about Programs using Hoare logic I  | [lec11](lectures/lecture10.pdf)        |      | HW4    |  HW3   |
| 5/4  | Reasoning about Programs using Hoare logic II|        |      |     |     |
| 5/9  | Zero-knowledge Proofs in a nutshell (Brian) |        |      |     |  HW2   |
| 5/11 | Formal Verification for Zero-knowledge Proofs using Ecne (Franklyn)                     |         |       |     |   R4  |
| 5/16 | Formal Verification for Zero-knowledge Proofs using Rosette (Yanju)                |        |      |     |     |
| 5/18 | Attack Synthesis for Blockchain Security        |         |      |     |    |
| 5/23 | Invairant Generation  |         |      |     |     |
| 5/25  | TBD                                 |        |      |     |  HW3  |
| 6/1  | Virtual Poster Session                                 |        |      |     |  Final Report (8 pages)  |


# Grading (No curving)

1. Programming assignments: 40%
    1. 4 programming assignments, 10% each

2. Paper reviews: 20%
    1. 4 papers, 5% each
        
3. Final project: 40%
    1. Team formed by deadline: 5%
    2. 1-page project proposal: 10%
    3. Project presentation (Poster): 10%
    4. Executable code: 5%
    5. Final report: 10%

| Letter | Percentage |
|--------|------------|
| A+     | 95–100%    |
| A      | 90–94%     |
| A-     | 85–89%     |
| B+     | 80–84%     |
| B      | 75–79%     |
| B-     | 70–74%     |
| C+     | 65–69%     |
| C      | 60–64%     |
| F      | <60%       |

### Submission
1. Please submit your homework to gradescope: https://www.gradescope.com
2. All paper reviews should be in PDF.

# Homework

1. [Homework1](hw1/HW1.md)
2. [Homework2](hw2/HW2.md)
3. [Homework3](hw3/HW3.md)
3. [Homework4](hw4/HW4.md)

# Reading assignments
1. A Lightweight Symbolic Virtual Machine for Solver-Aided Host Languages. Emina Torlak and Rastislav Bodik. PLDI'14.
2. Program synthesis using conflict-driven learning. Yu Feng, Ruben Martins, Osbert Bastani, and Isil Dillig.  PLDI'18. **Distinguished Paper Award** 
3. Scaling symbolic evaluation for automated verification of systems code with Serval. Luke Nelson, James Bornholt, Ronghui Gu, Andrew Baumann, Emina Torlak, and Xi Wang. SOSP'2019. **Best Paper Award**
4. C. A. R. Hoare. An axiomatic basis for computer programming. Communications of the ACM, vol. 12, no. 10. 1969. ACM DL. **Turing Award**


Tips for writing paper [reviews](REVIEW.md).

Tips for writing a project [proposal](PROPOSAL.md).

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

