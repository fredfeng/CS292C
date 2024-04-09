

# Setting up OCaml

> Adapted from [this guide](https://github.com/fredfeng/CS162/blob/winter-2021/sections/section1/install_ocaml.md) written by Bryan Tan.


## Step1. Installing `opam`

First, you need to install `opam`, OCaml's package manager, which allows you to install OCaml-related tools.


#### macOS
Make sure you have [homebrew](https://brew.sh/). Then run
```
brew install opam
```


#### Windows
Windows users are recommended to instead use [Windows Subsystem for Linux (WSL)](https://learn.microsoft.com/en-us/windows/wsl/install) or CSIL (as a last resort), since OCaml doesn't work too well on Windows based on our past experience.


#### CSIL

Log onto a CSIL machine. Download the `opam` binary using:
```bash
curl -LR 'https://github.com/ocaml/opam/releases/download/2.1.4/opam-2.1.4-x86_64-linux' -o opam
```

Then make sure the downloaded binary is executable, and move it to `~/bin/opam`:
```bash
chmod +x opam
mkdir -p ~/bin/
mv opam ~/bin/opam
```
Check to make sure it's on `PATH`:
```
[junrui@csilvm-01 ~]$ opam --version
2.1.4
```


#### Non-CSIL Linux
Follow [these step](https://opam.ocaml.org/doc/Install.html#Binary-distribution), under the "Binary distribution" section.




## Step 2. Installing OCaml, for real


After installing `opam`, you need to initialize the environment. 

> **Note 1:** Use the commands below one-by-one, read the instructions on the screen and proceed accordingly, since some of the commands below are interactive.
>
> **Note 2:**  Keep in mind that the initialization process will take **30-40 minutes**. Thus, do not wait until the last minute to install OCaml. 
> 
> **Note 3:** If you had an unsuccessful initialization of `opam`, please run `rm -rf ~/.opam` to clean up partial installation before retrying the steps below.
>
> **Note 4:** If you're on CSIL, you'll need at least **3GB** of available disk space. Otherwise the initialization will fail with a weird error message:
> 
> ```
> Failed to extract archive /tmp/opam-xxxx-xxx/index.tar.gz ...
> ```
> To confirm how much space is already used on your CSIL account, run `quota -s`. The number in the `space` column shows how much has been used. Subtracting this number from the `quota` column tells you how much free space you have.
>   - If you have less than 2GB, you can run `du -h -d 1` to see which directories are taking up the most space, and delete some files to free up space.
>   - Very rarely, the initialization will fail because you have too many files in your home directory. In this case, you can run `/cs/faculty/pconrad/bin/countfiles` to see how many files you have, and delete some files to free up space. Try to keep the number under 30K.
>   - Please refer to [this guide](https://ucsb-cs56-pconrad.github.io/topics/csil_disk_quota/) for detailed guide on diagnosing and fixing disk space and file count issues.


*If you're working over an SSH connection*, in order to prevent a disconnection from interrupting the ongoing initialization and corrupting your environment, we recommend you run this command inside a `screen` session. To start a `screen` session, run `screen` (and then press `Enter` to dismiss the welcome message if you see any). Then, run the following command:

```bash
opam init -vv -y --shell-setup --bare
```

You should see something like this:

```bash
<><> Fetching repository information ><><><><><><><><><><><><><><><><><><><><><>
Processing  1/1: [default: http]
```

This screen will seem to "get stuck" for a while. This is normal. You can leave it running and safely disconnect the current SSH session by pressing `Ctrl-a` and then `d`. You can then safely log out of CSIL. To reconnect to the `screen` session, run `screen -r`.

The initialization is **not** done **unless** you see a new bash prompt in which you can enter new commands. Do not force kill or quit the session if you only see a message like "Done" but don't see a new prompt, which means the initialization is still running.

Once the initialization is done, you can exit the `screen` session by pressing `Ctrl-a` and then `k`.


Type the following command so you can have the OCaml tools in your current shell session:

```bash
eval $(opam env)
```

Now, you are ready to install the OCaml compiler. Use the following command to create a development environment with OCaml compiler version 5.1.1:

```bash
opam switch create 292c ocaml-base-compiler.5.1.1
```

After the command above is done, you need to tell your shell where OCaml is again:

```
eval $(opam env)
```

At this point, if everything went well, you should see a prompt like this when you type `ocaml`:

```bash
OCaml version 5.1.1
Enter #help;; for help.

#
```


## Step 3. Installing `dune` and `utop`.

`dune` is a build system for OCaml, similar `make` for C. `utop` is an enhanced OCaml interpreter with features like autocompletion. Install them using

```
opam install dune utop
```

After this, `utop` should be available as a command. You can run as a REPL interpreter by entering a few OCaml expressions, e.g.,

```ocaml
1 + 2;;
```

You should see
```ocaml
- : int = 3
```
as a response. That is, OCaml infers that the expression we entered has type `int`, and it evaluates the expression to `3`.

In REPL mode (i.e. using the interpreter interactively), every expression needs to be terminated with `;;` before you hit the enter key. Otherwise, you'll just start a new line by hitting enter, and `utop` will patiently wait for you to type `;;` before it can start interpreting the expression. This contrasts with file mode, in which you do not have to terminate every expression with `;;`.

Lastly, note that this homework will be the only time you need to manually install dependencies using `opam install <package-name>`. For all homework assignments, we will have provided you with a project file that lists all dependencies that can be automatically installed at once using a single command.


## Loading an OCaml file in `utop`

Make a new file called `hello.ml` containing the following line:
```
print_endline "hello!"
```

Now, open `utop` and load `hello.ml` with
```
#use "hello.ml";;
```

You should see `hello!` printed on your console, along with
```ocaml
- : unit = ()
```
indicating that the result of evaluating `print_endline "hello!"` is the unit value `()`, whose type is the unit type. (The unit type is usually used to indicate that the expression has some side effect without procuding a concrete value.)

## Step 4. Setting up the development environment

For future assignments, you can use any text editor you like. We recommend [VSCode](https://code.visualstudio.com/) with the [OCaml Platform plugin](https://marketplace.visualstudio.com/items?itemName=ocamllabs.ocaml-platform). This plugin works very well with the OCaml language serve, which can be installed with `opam install ocaml-lsp-server`. It will provide you will real-time type checking, auto-formatting and autocompletion suggestions, making your life *much* easier.

In addition, if you are working remotely with CSIL, you might want to install the [remote SSH plugin](https://code.visualstudio.com/docs/remote/ssh-tutorial) on your laptop to avoid having to manually sync files between your computer and CSIL.


