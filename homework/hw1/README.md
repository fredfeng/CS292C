# CS292C Homework 1

**Due: 4/8/2019 11:59pm**



## Instructions

1. Compose your answers and code in a PDF file.
2. On the first page of the PDF file, include a table that contains a self-grade (0, 1, or 2) for each problem. See the [course syllabus](/README.md) for the self-grading rubric.
3. Submit your PDF file to Gradescope.




### Problem 1

Install Dafny by following [these instructions](https://dafny.org/dafny/Installation). We recommend simply installing the [Dafny VSCode extension](https://dafny.org/dafny/Installation#Visual-Studio-Code). If you're on macOS or Linux, you will be prompted in VSCode to install .NET 6.0 once you open a `.dfy` file. Simply follow the link in the prompt to install it.

You should install Dafny 4. If you're prompted by VSCode to upgrade from Dafny 3 to Dafny 4, you should let it automatically upgrade.

The whole process should be fairly quick, taking no more than 5 minutes.

Once you're done, run Dafny on the [demo file](/tutorials/01-dafny/demo.dfy) we covered during the tutorial, and attach the output to your submission PDF.




### Problem 2

In [min.dfy](./min.dfy), you will find a Dafny method that finds the minimum of a 2D array. Your tasks are:
1. State the correctness property of this method in terms of pre-condition(s) (using the `requires` keyword) and post-condition(s) (using the `ensures` keyword). 
    
    Your pre-condition(s) should allow Dafny to prove that there is no out-of-bound array access. 

2. Annotate each of the two loops with appropriate invariants that allow Dafny to verify the overall correctness of the method.

   > *Hints*: 
   > - The invariant for the outer should be very similar to your post-condition.
   > - For the inner loop, you may need to provide *two* different invariants:
   >   - the first invariant talks about *all* elements from sub-arrays `a[0]` up to `a[i-1]` inclusive, and
   >   - the second invariant specifically looks at the sub-array `a[i]` and talks about its elements between `0` and `j-1` inclusive.
   > 
   > It may help draw a dummy 2D array on paper, and mark the elements that have been processed so far when the loop is at (i,j)-th position. Those processed elements will be the ones (and the only ones) that are mentioned in the invariants.


3. Attach your code with the annotations in your submission. Also, informally explain what your pre- and post-conditions, and loop invariants mean in plain English.

You should *not* change the implementation code in any way.



### Problem 3

The file [binary_search.dfy](./binary_search.dfy) contains a method `BinarySearch` that performs binary search on a sorted array. The sorted-ness is guaranteed by the `Ordered(a)` predicate, which is just a formula that asserts `a[i] <= a[j]` for all `i <= j`. The post-condition is provided, which says that the method returns `true` if and only if the key `x` is contained in the array. Also, note that the while-loop is annotated with `decreases hi - lo`, which enables Dafny to prove that the loop terminates because the quantifier `(hi - lo)` monotonically decreases in each iteration of the loop.

Your task is to replace `invariant true` in the while-loop of `BinarySearch` with an appropriate loop invariant that allows Dafny to verify the correctness of the method. 

> *Hint*: Your invariant needs to talk about where `x` *cannot* be found in the array based on the current values of `lo` and `hi`.

Attach your code and a brief explanation of your invariant in your submission.



### Problem 4

Immediately below `BinarySearch`, we duplicated its implementation into another method called `BuggyBinarySearch`. The only change we made is to make the index variables (`lo`, `mid`, `hi`, etc.) into 4-bit integers (unsigned), whereas in Dafny `int` is the default infinite-precision integer.

Copy and paste the (working) invariant you wrote for `BinarySearch` into `BuggyBinarySearch` and see if Dafny can verify the correctness of the method. Note that to make the invariant well-typed, you may need to do some conversion from `int` to `bv4` using the syntax `x as bv4` which converts a variable of type `int` to `bv4`.

After that, you shall see that Dafny cannot verify the correctness of `BuggyBV4BinarySearch`. Your tasks are to:
1. locate the exact line where Dafny reports an error,
2. explain why Dafny cannot verify the correctness of the method
3. patch *only one line of implementation code* in the loop body to make verification succeed.

Include your answers to the above questions in your submission. You should also attach the modified code with the fix in your submission.

*Hint*: The answers to the above questions can be found in the Wikipedia page for binary search, under the section Implementation Issues.



### Problem 5

Implement bubble sort in Dafny, and prove its correctness. There are multiple levels you can aim for in terms of the complexity of your implementation and the strength of your correctness proof:
- Your bubble sort outputs an ordered list
- Your bubble sort outputs an ordered list whose elements form the same *set* as the input list
- Your bubble sort outputs an ordered list whose elements form the same *multiset* as the input list

You may choose to aim for any of the above levels, but you should clearly state which level you are aiming for in your submission.

You may find this tutorial on [verifying selection sort in Dafny](https://dafny.org/blog/2023/10/11/insertion-sort/) helpful.

Attach your implementation, including all necessary annotations, in your submission. You should also informally explain in plain English the meaning of your pre- and post-conditions, and the loop invariants you used. 