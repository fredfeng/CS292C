# CS292C Homework 4

**Due: May 15th, 11:59pm**


## Instructions

1. Provide your answers in *.v files.
2. Enter a self-grade for each exercise in [self-grading.txt](./self-grading.txt).
3. Submit the following files to Gradescope:
   - `Induction.v`
   - `List.v`
   - `Poly.v`
   - `HW4Extra.v`
   - `self-grading.txt`



## Part 0


### Installing Coq

Starting from this HW, a local installation of Coq is required. We recommend installing it locally with `opam`:
```
opam pin add coq 8.18.0
```
as well as the [VsCoq](https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq) extension for VSCode. In addition to the extension itself, you also need to install the language server with
```bash
opam install vscoq-language-server
```

### Download and Compiling Software Foundations

1. Go to this [link](https://softwarefoundations.cis.upenn.edu/lf-current/index.html) and click the "Download" button to download the latest version of Software Foundations. Unzip the archive.
2. Run the following commands:
   ```bash
   coq_makefile -f _CoqProject *.v -o Makefile
   make
   ```
   which will compile all the `.v` files in the directory. You can also compile individual files by running `make <filanem>.vo`, **NOT `make <filename>.v`**!
3. You will be modifying `Induction.v`, `Lists.v`, and `Poly.v` in this HW. You must compile at least `Basics.v` using `make` first before you can do the exercises in `Induction.v`. (If you wish to compile just `Basics.v`, you can run `make Basics.vo`, NOT `make Basics.v`.)


### Installing Coq using docker (NOT recommended)

If you *genuinely* have difficulty installing Coq on your machine with `opam`, please instead follow the instructions for "Using Coq with VSCode and Docker" in the [Preface chapter of Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/Preface.html). Important notes:
- **The [.devcontainer](./.devcontainer) folder is already provided in this HW directory.** You SHOULD NOT use the `.devcontainer` folder shipped with Software Foundations, which points to an outdated docker image that WILL NOT WORK.
- If you go for this route, proof checking can be VERY slow which is why we recommend installing Coq locally if possible. 
- In VSCode User Preferences, you should set `Vscoq > Proof: Mode` to `Manual` instead of `Continuous` to alleviate the slowness a bit.


### Part 1

- Read the [Induction](https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html) chapter of Software Foundations. You can skip the section "Formal vs. Informal Proof".
  - Do all exercises in sections:
    - **Nat to Bin and Back to Nat**
    - **Bin to Nat and Back to Bin (Advanced)**

- Read the [Lists](https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html) chapter.
  - Do the following exercises:
    - `involution_injective`
    - `rev_injective`
    - All three exercises in the **Partial Map** section.

- Read the [Poly](https://softwarefoundations.cis.upenn.edu/lf-current/Poly.html) chapter. You only need to read through the **Polymorphism** section. We'll cover **Functions as Data** next week.
  - Do the following exercises:
    - `mumble_grumble`
    - `combine_checks`
    - `split`


### Part 2

In [`HW4Extra.v`](./HW4Extra.v), replace all `Admitted` with your own code.