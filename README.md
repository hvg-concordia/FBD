# Functional Block Diagrams (FBD) Formalization in HOL4

FBD HOL4 Theorems and mathematical formulations are currently supported for Linux users only

"-----------------------------------------  Installing HOL4 in Linux ---------------------------------------------------"

1- Make sure that the GCC compiler is properly installed, if not then open the terminal and use the following command.
sudo apt-get update
sudo apt-get install build-essential

2- Download the PolyML 5.7 
(Download Link: https://osdn.net/frs/g_redir.php?m=kent&f=polyml%2Fpolyml%2F5.7%2Fpolyml-5.7.tar.gz). 
Untar the package into any directory of your choice.

3- Open the terminal and enter into the package directory using cd command. e.g.
Abdelghany@ubuntu:~ cd /Downloads/polyml-5.7$

4- In the PolyML directory, type the following commands one by one;
./configure --prefix=/usr
make
sudo make install

5- The latest HOL-kananankis-12 (HOL4) can be download from GitHub (https://github.com/HOL-Theorem-Prover/HOL)
Once the download finished and enter into the HOL package directory using cd command. e.g.
Abdelghany@ubuntu:~/Downloads/HOL$

6- Type the following command in terminal,
poly < tools/smart-configure.sml

Wait for configuration to complete!

7- Type the following command in terminal,
bin/build

The installation of HOL begins if the above procedure is followed correctly, and after some time, it will complete the installation.

8- Install the Emacs by using the following command in the terminal.
sudo apt-get install emacs

After completion of Emacs installation, open emacs, and load the file “hol-mode.el” from HOL directory. e.g.

a) At Emacs, Press ALT-x and type “load-file” then press enter
b) A cursor appears at the bottom, type the path “~/Downloads/HOL/tools/hol-mode.el” then press enter
c) Press ALT-h 3 (it will split the Emacs screen into two columns and the HOL shell is running on the right screen)
d) The tab “HOL”, at the top of Emacs bar, contains several shortcuts to interact with HOL shell.

A more detail description of the Emacs HOL commands can be found in https://hol-theorem-prover.org/hol-mode.html.


"-----------------------------------------  Installing ET Code ----------------------------------------------"

To use the FBD theorems and mathematical formulations, load all the necessary files
in the HOL4 shell as follows: 

The tab “HOL”, at the top of Emacs bar ==> Misc ==> Load file ==> ETree.sml  ==> FBD.sml 

Now all FBD theorems are proved in the HOL4 shell and ready to be used!

"--------------------------------------------  FBD Theorems  -------------------------------------------------"

All theorems are stored under a specific different name as follows: store_thm("name")"

Entre the name of any theorem exist at the file "FBD.sml", for instance, "CONSECUTIVE_CARTESIAN_SPLIT" 

in the HOL4 shell, the HOL4 will load this theorem directly for use without reproof it again.         

"--------------------------- Nuclear Power Plant Application  -------------------------------------------"

We applied our FBD theorems on a real-world application Nuclear Power Plant System to show the capability of 

the FBD formal step-analysis to obtain a component-level reliability/failure expression easily.  

"----------------------------------------   Contacts ---------------------------------------------------------"

Mohamed Abdelghany  (m_eldes@ece.concordia.ca)

Prof. Sofiene Tahar (tahar@ece.concordia.ca)

