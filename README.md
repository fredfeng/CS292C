# CS292C Computer-Aided Reasoning for Software

This course is a comprehensive introduction to solvere-aided reasoning for software with a special focus on program synthesis: an emerging area that sits at the intersection of systems, programming languages, HCI, and artificial intelligence. The goal of program synthesis is to generate programs automatically from high-level, potentially informal and incomplete descriptions. The course covers recent advances in synthesis techniques that differ in the kind of specifications (from input-output examples to formal correctness specifications), search strategies (enumerative, stochastic, or symbolic search), and information to guide the search (counter-example guided synthesis, type-driven synthesis, synthesis with machine learning). The course involves a project, 3 programming assignments, and reviewing research papers.

# Office hour
Friday, 11am, HFH-2157

| Date  | Topic                                         | Slides | Read | Out | Due |
|-------|-----------------------------------------------|--------|------|-----|-----|
| 9/30  | Introduction                                  |  [lec1](lectures/lecture1.pdf)      |      |     |     |
| 10/2  | Solver-Aided Programming I (Rosette)          |  [lec2](lectures/lecture2.pdf)      |  R1    |     |     |
| 10/7  | Solver-Aided Programming II (Neo)             |        |  R2    | HW1    |     |
| 10/9  | SAT Solving Basics                            |        |      |     | R1    |
| 10/14 | A Modern SAT Solver                           |        |      |     |     |
| 10/16 | Applications of SAT                           |        |      |     |  HW1   |
| 10/21 | SAT Modulo Theories                           |        |      |     |     |
| 10/23 | TBD              |        |   R5   |     |     |
| 10/28 | Combining Theories                            |        |      |     | Proposal    |
| 10/30 | The DPLL(T) Framework                         |        |      |     |     |
| 11/4  | Reasoning about Programs using Hoare logic I  |        |      |     |     |
| 11/6  | Reasoning about Programs using Hoare logic II |        |      |     |     |
| 11/11 | Symbolic Execution I                          |        |   R6   |     |     |
| 11/13 | Symbolic Execution II                         |        |      |     |     |
| 11/18 | Program synthesis by Examples                 |        |      |     |     |
| 11/20 | Type-directed Program Synthesis               |        |   R3   |     |     |
| 11/25 | Program synthesis by natural language         |        |      |     |     |
| 11/27 | Thanksgiving break                            |        |      |     |     |
| 12/2  | Program Synthesis using deep learning         |        |  R4    |     |     |
| 12/4  | Project Demos                                 |        |      |     |  Final Report  |


# Grading

1. Programming assignments: 15%
    1. 3 programming assignments, 5% each

2. Paper reviews: 30%
    1. 6 papers, 5% each
    
3. Final project: 50%
    1. Team formed by deadline: 5%
    2. 1-page project proposal: 15%
    3. Project presentation: 15%
    4. Final report: 15%
  
4. Class Participation: 5%

# Homework

1. [Homework1](hw1/HW1.md)
2. Homework2
3. Homework3

# Reading list
1. A Lightweight Symbolic Virtual Machine for Solver-Aided Host Languages. Emina Torlak and Rastislav Bodik. PLDI'14.
2. Program synthesis using conflict-driven learning. Yu Feng, Ruben Martins, Osbert Bastani, and Isil Dillig.  PLDI'18. **Distinguished Paper Award** 
3. Stochastic superoptimization. 	Eric Schkufza, Rahul Sharma, and Alex Aiken. ASPLOS'13
4. Deepcoder: Learning to write programs. Matej, et al. ICLR'16.
5. Combinatorial sketching for finite programs. 	Armando Solar-Lezama, Liviu Tancau, Rastislav Bodik, Sanjit Seshia, Vijay Saraswat. ASPLOS'06.
6. KLEE: Unassisted and Automatic Generation of High-Coverage Tests for Complex Systems Programs. Cristian Cadar, Daniel Dunbar, Dawson Engler. OSDI'08

Tips for writing paper [reviews](REVIEW.md).

# Other references

[1] Aaron Bradley and Zohar Manna. The Calculus of Computation. 2010. 

[2] Joao Marques-Silva, Ines Lynce, and Sharad Malik. Chapter 4: Conflict-Driven Clause Learning SAT Solvers. Handbook of Satisfiability. 2008. 

[3] Edmund Clarke, Daniel Kroening, and Flavio Lerda. A Tool for Checking ANSI-C Programs. Tools and Algorithms for the Construction and Analysis of Systems (TACAS). 2004. Springer

[4] Leonardo de Moura and Nikolaj Bjorner. Satisfiability Modulo Theories: Introduction and Applications. Communications of the ACM, vol. 54, no. 9. 2011. 

[5] Clark Barrett, Roberto Sebastiani, Sanjit A. Seshia, and Cesare Tinelli. Chapter 12: Satisfiability Modulo Theories. Handbook of Satisfiability. 2008. 

[6] C. A. R. Hoare. An axiomatic basis for computer programming. Communications of the ACM, vol. 12, no. 10. 1969. ACM DL. **Turing Award**

[7] Roberto Baldoni, Emilio Coppa, Daniele Cono D’elia, Camil Demetrescu, and Irene Finocchi. A Survey of Symbolic Execution Techniques. ACM Computing Surveys (CSUR). 2018. ACM DL

[8] Ali Sinan Köksal, Yewen Pu, Saurabh Srivastava, Rastislav Bodík, Jasmin Fisher, Nir Piterman. Synthesis of biological models from mutation experiments. Principles of Programming Languages (POPL). 2013. ACM DL

[9] Sumit Gulwani, Oleksandr Polozov, and Rishabh Singh. Program Synthesis. Foundations and Trends in Programming Languages. 2017. 

[10] Srivastava, Saurabh, Sumit Gulwani, and Jeffrey S. Foster. From program verification to program synthesis. POPL 2010.

[11] Jha, Susmit, et al. Oracle-guided component-based program synthesis. ICSE 2010.

[12] Gulwani, Sumit. Automating string processing in spreadsheets using input-output examples. POPL 2011.

[13] Feng, Yu, et al. Component-based synthesis for complex APIs. POPL 2017.

[14] Phothilimthana, Phitchaya Mangpo, et al. "Scaling up superoptimization." ASPLOS 2016.

[15] Chandra, Kartik, and Rastislav Bodik. Bonsai: synthesis-based reasoning for type systems. POPL 2017.

[16] Bornholt, James, et al. Optimizing synthesis with metasketches. POPL 2016.

[17] Bielik, Pavol, Veselin Raychev, and Martin Vechev. Programming with big code: Lessons, techniques and applications. 1st Summit on Advances in Programming Languages (SNAPL 2015). Schloss Dagstuhl-Leibniz-Zentrum fuer Informatik, 2015.

[18] Yaghmazadeh, Navid, et al. SQLizer: query synthesis from natural language. OOPSLA 2017. **Distinguished Paper Award**

[19] Helgi Sigurbjarnarson, James Bornholt, Emina Torlak, and Xi Wang. Push-Button Verification of File Systems via Crash Refinement. OSDI 2016. **Best Paper Award**

[20] Shaon Barman, Sarah E. Chasins, Rastislav Bodik, Sumit Gulwani. Ringer: web automation by demonstration. OOPSLA 2016.




