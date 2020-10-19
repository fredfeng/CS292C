# CS292C Computer-Aided Reasoning for Software

This course is a comprehensive introduction to solver-aided reasoning for software with a bit focus on program synthesis: an emerging area that sits at the intersection of systems, programming languages, HCI, and artificial intelligence. The goal of program synthesis is to generate programs automatically from high-level, potentially informal and incomplete descriptions. The course covers recent advances in synthesis techniques that differ in the kind of specifications (from input-output examples to formal correctness specifications), search strategies (enumerative, stochastic, or symbolic search), and information to guide the search (counter-example guided synthesis, type-driven synthesis, synthesis with machine learning). The course involves a project, 3 programming assignments, and reviewing research papers.

# Office hour
Instructor : Yu Feng

Gitter: https://gitter.im/CS292C/community


| Date  | Topic                                         | Slides | Read | Out | Due |
|-------|-----------------------------------------------|--------|------|-----|-----|
| 10/5  | Introduction                                  |  [lec1](lectures/lecture1.pdf)      |      |     |     |
| 10/7  | Solver-Aided Programming I (Rosette)          |  [lec2](lectures/lecture2.pdf)      |  R1    |  HW1   |     |
| 10/12  | Solver-Aided Programming II (Neo)             |  [lec3](lectures/lecture3.pdf)      |  R2    |     |     |
| 10/14  | SAT Solving Basics                            |  [lec4](lectures/lecture4.pdf)     |      |     | R1    |
| 10/19 | A Modern SAT Solver                           |  [lec5]      |      |     |     |
| 10/21 | Applications of SAT                           |  [lec6]      |  R3    |     |  HW1,R2   |
| 10/26 | SAT Modulo Theories                           |  [lec7]      |      |     |     |
| 10/28 | Combining Theories              | [lec8]        |      |  [HW2]  |  R3   |
| 11/2 | The DPLL(T) Framework                             |  [lec9]       |      |     | Proposal    |
| 11/4 | Reasoning about Programs using Hoare logic I                        |  [lec10]       |  R4    |     |     |
| 11/9  | Reasoning about Programs using Hoare logic II  | [lec11]        |      |     |     |
| 11/11  | No class |        |      |     |     |
| 11/16  | Presentation |        |      |     |  HW2   |
| 11/18 | Presentation                         |         |       | [HW3]    |   R4  |
| 11/23 | Presentation                 |        |      |     |     |
| 11/25 | Presentation        |         |      |     |    |
| 11/30 | Exploiting Android framework vulnerabilies. Sebastian and Alec (Google Security) |         |      |     |     |
| 12/2  | Autotuning for ML compiler optimizations. Mangpo Phothilimthana (Google Brain)                                 |        |      |     |  HW3  |
| 12/7  | Virtual Poster Session                                 |        |      |     |  Final Report  |


# Grading

1. Programming assignments: 15%
    1. 3 programming assignments, 5% each

2. Paper reviews: 20%
    1. 4 papers, 5% each
    
3. Paper presentation (30 mins): 10%
    
4. Final project: 50%
    1. Team formed by deadline: 5%
    2. 1-page project proposal: 15%
    3. Project presentation: 15%
    4. Final report: 15%
  
5. Class Participation: 5%

### Submission
1. Please submit your homework to gradescope: https://www.gradescope.com
2. All paper reviews should be in PDF.
3. Due at **9am** before the lecture starts.


# Homework

1. [Homework1](hw1/HW1.md)
2. [Homework2](hw2/HW2.md)
3. [Homework3](hw3/HW3.md)

# Reading assignments
1. A Lightweight Symbolic Virtual Machine for Solver-Aided Host Languages. Emina Torlak and Rastislav Bodik. PLDI'14.
2. Program synthesis using conflict-driven learning. Yu Feng, Ruben Martins, Osbert Bastani, and Isil Dillig.  PLDI'18. **Distinguished Paper Award** 
3. Scaling symbolic evaluation for automated verification of systems code with Serval. Luke Nelson, James Bornholt, Ronghui Gu, Andrew Baumann, Emina Torlak, and Xi Wang. SOSP'2019. **Best Paper Award**
4. C. A. R. Hoare. An axiomatic basis for computer programming. Communications of the ACM, vol. 12, no. 10. 1969. ACM DL. **Turing Award**


Tips for writing paper [reviews](REVIEW.md).

Tips for writing a project [proposal](PROPOSAL.md).

# Presentation list

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



