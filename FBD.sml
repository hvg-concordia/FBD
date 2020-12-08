(* ========================================================================= *)
(* File Name: FBD.sml	          	                                     *)
(*---------------------------------------------------------------------------*)
(*          Description: Formalization of Functional Block Diagrams in       *)
(*                       Higher-order Logic                                  *)
(*                                                                           *)
(*          HOL4-Kananaskis 13 		 			     	     *)
(*									     *)
(*	    Author : Mohamed Abdelghany             		     	     *)
(*                                              			     *)
(* 	    Department of Electrical and Computer Engineering (ECE)          *)
(*	    Concordia University                                             *)
(*          Montreal, Quebec, Canada, 2020                                   *)
(*                                                                           *)
(* ========================================================================= *)

app load ["arithmeticTheory", "realTheory", "prim_recTheory", "seqTheory",
          "pred_setTheory","res_quanTheory", "res_quanTools", "listTheory", "real_probabilityTheory",
	  "numTheory", "dep_rewrite", "transcTheory", "rich_listTheory", "pairTheory",
          "combinTheory","limTheory","sortingTheory", "realLib", "optionTheory","satTheory",
          "util_probTheory", "extrealTheory", "real_measureTheory","real_sigmaTheory",
	  "indexedListsTheory", "listLib", "bossLib", "metisLib", "realLib", "numLib", "combinTheory",
          "arithmeticTheory","boolTheory", "listSyntax", "ETreeTheory"];

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory
     real_probabilityTheory seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools
     listTheory transcTheory rich_listTheory pairTheory combinTheory realLib  optionTheory
     dep_rewrite util_probTheory extrealTheory real_measureTheory real_sigmaTheory indexedListsTheory
     listLib satTheory numTheory bossLib metisLib realLib numLib combinTheory arithmeticTheory
     boolTheory listSyntax ETreeTheory;

val _ = new_theory "FBD";
(*---------------------------------------------------------------------------------------------------*)

(*----------------------------*)  
(*        Definitions         *)
(*----------------------------*)

val ALL_SCENARIOS_DEF = Define
`ALL_SCENARIOS X L  = MAP (\a. X INTER a ) L `;

val CARTESIAN_PRODUCT_DEF  = Define
`CARTESIAN_PRODUCT L1 L2 = FLAT (MAP (\a. ALL_SCENARIOS a L2) L1)`;

val FBLOCK_DEF = Define
`FBLOCK (S::L) = FOLDR (\ a b. CARTESIAN_PRODUCT a b) S L `;

val FBLOCK_N_DEF = Define 
`FBLOCK_N SI = FBLOCK (MAP (\a. FBLOCK a) SI)`;

val PARTITIONING_DEF = Define
`PARTITIONING N L = MAP (\a. EL a L) N`;

val FBLOCK_ET_DEF = Define
`FBLOCK_ET WJ = ETREE (NODE (EVENT_TREE_LIST WJ))`;

val FBLOCK_ET_LIST_DEF = Define
`(FBLOCK_ET_LIST [] = []) /\ (FBLOCK_ET_LIST (h::t) = FBLOCK_ET h::FBLOCK_ET_LIST t)`;

val LIST_EVENT_OUTCOME_SPACE_CONDS_DEF = Define
`(LIST_EVENT_OUTCOME_SPACE_CONDS [] <=> T) /\
 (LIST_EVENT_OUTCOME_SPACE_CONDS (h::t) <=> 
  ALL_DISTINCT h /\ disjoint (set h) /\ LIST_EVENT_OUTCOME_SPACE_CONDS t)`;
(*---------------------------------------------------------------------------------------------------*)

(*----------------------------*)  
(*      Sybmols Unicode       *)
(*----------------------------*)

val CART_PROD =  U 0x02297;
val F 	  =  U 0x1D4D5;
val B	  =  U 0x1D4D1;
val N     =  U 0x0039D;
val BOX_PART =  U 0x0229E;
val E     =  U 0x1D46C;
val T     =  U 0x1D47B;
val OMEGA =  U 0x003A9;
val TRUE  =  U 0x022A8;

val _ = Unicode.unicode_version {tmnm = "CARTESIAN_PRODUCT", u = CART_PROD};
val _ = Unicode.unicode_version {tmnm = "FBLOCK", u = F^B};
val _ = Unicode.unicode_version {tmnm = "FBLOCK_N", u = F^B^N};
val _ = Unicode.unicode_version {tmnm = "PARTITIONING", u = BOX_PART};
val _ = Unicode.unicode_version {tmnm = "FBLOCK_ET", u = F^B^E^T};
val _ = Unicode.unicode_version {tmnm = "FBLOCK_ET_LIST", u = F^B^E^T^N};
val _ = Unicode.unicode_version {tmnm = "LIST_EVENT_OUTCOME_SPACE_CONDS", u = OMEGA^L^TRUE};
(*-------------------------------------------------------------------------------------------------*)

val ETREE_NODE_SPLIT = store_thm("ETREE_NODE_SPLIT",
  ``! X Y. ETREE (NODE ( X ++ Y )) = ETREE (NODE X) UNION ETREE (NODE Y)``,
Induct_on `X`
>-(rw [ETREE_DEF])
\\ rw [APPEND, ETREE_DEF, UNION_ASSOC]);
(*-------------------------------------------------------------------------------------------------*)

val EVENT_TREE_SPLIT = store_thm("EVENT_TREE_SPLIT",
``!X Y. EVENT_TREE_LIST (X ++ Y) = EVENT_TREE_LIST X ++ EVENT_TREE_LIST Y``,
Induct_on `X`
>-(rw [EVENT_TREE_LIST_DEF])
\\ rw [APPEND, EVENT_TREE_LIST_DEF]);
(*-------------------------------------------------------------------------------------------------*)

val EVENT_TREE_LIST_SPLIT = store_thm("EVENT_TREE_LIST_SPLIT",
  ``! X Y Z.  ETREE (NODE (EVENT_TREE_LIST
           (FLAT (MAP (λa. (ALL_SCENARIOS a X ++ ALL_SCENARIOS a Y)) Z)))) =
	    ETREE (NODE (EVENT_TREE_LIST (FLAT (MAP (λa. (ALL_SCENARIOS a X)) Z)) ++
	    EVENT_TREE_LIST (FLAT (MAP (λa. (ALL_SCENARIOS a Y)) Z))))``,
rw []
\\ Induct_on `Z`
>-( rw [EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF] 
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ sg `!a b c. a ++ b ++ c = a ++ (b ++ c) `
   >-( rw [])
\\ fs []
\\ rw [ETREE_NODE_SPLIT]
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val EVENT_TREE_LIST_SPLIT_TRIPLE = store_thm("EVENT_TREE_LIST_SPLIT_TRIPLE",
  ``! X Y Z S.  ETREE (NODE (EVENT_TREE_LIST
                (FLAT (MAP (λa. (ALL_SCENARIOS a X ++ ALL_SCENARIOS a Y ++ ALL_SCENARIOS a S)) Z)))) =
	    	ETREE (NODE (EVENT_TREE_LIST (FLAT (MAP (λa. (ALL_SCENARIOS a X)) Z)) ++
	   	EVENT_TREE_LIST (FLAT (MAP (λa. (ALL_SCENARIOS a Y)) Z)) ++
		EVENT_TREE_LIST (FLAT (MAP (λa. (ALL_SCENARIOS a S)) Z))))``,
rw []
\\ Induct_on `Z`
>-( rw [EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF] 
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ sg `!a b c d. a ++ b ++ c ++ d = a ++ (b ++ c ++ d) `
   >-( rw [])
\\ fs []
\\ rw [ETREE_NODE_SPLIT]
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val CONSECUTIVE_ALL_SCENARIOS = store_thm("CONSECUTIVE_ALL_SCENARIOS",
  ``! h h' LN L. ALL_SCENARIOS h (ALL_SCENARIOS h' (𝓕𝓑 (LN::L))) =
                 ALL_SCENARIOS (h INTER h') (𝓕𝓑 (LN::L))``,
Induct_on `L`
>-( rw [FBLOCK_DEF]
    \\ Induct_on `LN`
       >-(rw [ALL_SCENARIOS_DEF])
    \\ rw [ALL_SCENARIOS_DEF]
       >-(rw [INTER_ASSOC])
    \\ rw [GSYM ALL_SCENARIOS_DEF])
\\ rw [FBLOCK_DEF]
\\ rw [GSYM FBLOCK_DEF]
\\ Induct_on `h`
   >-( rw [CARTESIAN_PRODUCT_DEF]
       \\ rw [ALL_SCENARIOS_DEF])
\\ rw [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [INTER_ASSOC]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]);
(*-------------------------------------------------------------------------------------------------*)

val INTER_ETREE_BRANCH = store_thm("INTER_ETREE_BRANCH",
  ``! X LN. X ∩ ETREE (BRANCH (X) (EVENT_TREE_LIST LN)) =
            ETREE (BRANCH (X) (EVENT_TREE_LIST LN))``,
Induct_on `LN`
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [INTER_ASSOC]);
(*-------------------------------------------------------------------------------------------------*)

val ETREE_NODE_ALL_SCENARIOS_EQ_BRANCH = store_thm("ETREE_NODE_ALL_SCENARIOS_EQ_BRANCH",
  ``! h' h LN. 𝓕𝓑𝑬𝑻 (ALL_SCENARIOS h' (ALL_SCENARIOS h LN)) =
               h' ∩ ETREE (BRANCH h (EVENT_TREE_LIST LN))``,
once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct_on `LN`
>-( rw [EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF, ETREE_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF, UNION_OVER_INTER, INTER_ASSOC]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ALL_SCENARIOS_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ETREE_DEF, INTER_ASSOC, BRANCH_EQ_INTER_NODE, INTER_ASSOC]
\\ rw [EXTENSION]
\\ EQ_TAC
   >-(metis_tac [])
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val TWO_ALL_SCENARIOS_SPLITS = store_thm("TWO_ALL_SCENARIOS_SPLITS",
  ``! h h' L. ALL_SCENARIOS h (ALL_SCENARIOS h' L) = ALL_SCENARIOS (h INTER h') L``,
Induct_on `L`
>-(rw [ALL_SCENARIOS_DEF])
\\ rw [ALL_SCENARIOS_DEF]
   >-(rw [INTER_ASSOC])
\\ rw [GSYM ALL_SCENARIOS_DEF]); 
(*-------------------------------------------------------------------------------------------------*)

val ALL_SCENARIOS_CARTESIAN_PRODUCT_EQ_BRANCH_TWO_N_STAIRS = store_thm(
   "ALL_SCENARIOS_CARTESIAN_PRODUCT_EQ_BRANCH_TWO_N_STAIRS",
  ``!h h' h'' LN L.
      h' ∩ 𝓕𝓑𝑬𝑻 (ALL_SCENARIOS h'' ($⊗ h (𝓕𝓑 (LN::L)))) =
      ETREE (BRANCH (h' ∩ h'') (ETREE_TWO_STAIR h (ETREE_N_STAIR (EVENT_TREE_LIST LN) L)))``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ once_rewrite_tac [BRANCH_EQ_INTER_NODE]
\\ once_rewrite_tac [GSYM INTER_ASSOC]
\\ once_rewrite_tac [GSYM BRANCH_EQ_INTER_NODE]
\\ sg `∀h h' h'' LN L.
        ETREE  (NODE (EVENT_TREE_LIST (ALL_SCENARIOS h''
               (CARTESIAN_PRODUCT h (FBLOCK (LN::L)))))) =
       h'' ∩ ETREE (NODE (ETREE_TWO_STAIR h (ETREE_N_STAIR (EVENT_TREE_LIST LN) L)))`      
  >-( Induct_on `L`
      >-( rw [FBLOCK_DEF, ETREE_N_STAIR_DEF]
       	  \\ Induct_on `h`
       	     >-( rw [CARTESIAN_PRODUCT_DEF, EVENT_TREE_LIST_DEF, ETREE_TWO_STAIR_DEF,
	             ALL_SCENARIOS_DEF, ETREE_DEF])
          \\ rw [CARTESIAN_PRODUCT_DEF]
      	  \\ rw [GSYM CARTESIAN_PRODUCT_DEF]
       	  \\ rw [EVENT_TREE_LIST_DEF, ETREE_TWO_STAIR_DEF]
       	  \\ rw [GSYM EVENT_TREE_LIST_DEF]
       	  \\ rw [ALL_SCENARIOS_DEF]
       	  \\ rw [GSYM ALL_SCENARIOS_DEF]
       	  \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
       	  \\ rw [GSYM EVENT_TREE_LIST_DEF]
       	  \\ rw [UNION_OVER_INTER, ETREE_NODE_SPLIT]
	  \\ rw [GSYM FBLOCK_ET_DEF]
       	  \\ sg `𝓕𝓑𝑬𝑻 (ALL_SCENARIOS h'' (ALL_SCENARIOS h' LN)) =
       	         h'' ∩ ETREE (BRANCH h' (EVENT_TREE_LIST LN))`
	     >-(rw [ETREE_NODE_ALL_SCENARIOS_EQ_BRANCH])
          \\ fs [])
     \\ rw [FBLOCK_DEF]
     \\ rw [GSYM FBLOCK_DEF]
     \\ rw [ETREE_N_STAIR_DEF]
     \\ rw [GSYM ETREE_N_STAIR_DEF]
     \\ Induct_on `h'`
        >-( rw [ETREE_TWO_STAIR_DEF, CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF,
	        EVENT_TREE_LIST_DEF, ETREE_DEF])
     \\ rw [CARTESIAN_PRODUCT_DEF]
     \\ rw [GSYM CARTESIAN_PRODUCT_DEF]
     \\ rw [ETREE_TWO_STAIR_DEF, ETREE_DEF, ALL_SCENARIOS_DEF]
     \\ rw [GSYM ALL_SCENARIOS_DEF]
     \\ rw [EVENT_TREE_LIST_DEF]
     \\ rw [GSYM EVENT_TREE_LIST_DEF]
     \\ rw [ETREE_NODE_SPLIT, TWO_ALL_SCENARIOS_SPLITS, UNION_OVER_INTER,
            BRANCH_EQ_INTER_NODE, INTER_ASSOC])
\\ fs [BRANCH_EQ_INTER_NODE]);
(*-------------------------------------------------------------------------------------------------*)

val INTER_NODE_ALL_SCENARIOS_FB_EQ_BRANCH_INTER_N_STAIR =store_thm(
   "INTER_NODE_ALL_SCENARIOS_FB_EQ_BRANCH_INTER_N_STAIR",
``!h h' LN L. h ∩  𝓕𝓑𝑬𝑻 (ALL_SCENARIOS h' (𝓕𝓑 (LN::L))) =
      	      ETREE (BRANCH (h ∩ h') (ETREE_N_STAIR (EVENT_TREE_LIST LN) L))``,
rw [FBLOCK_ET_DEF]
\\ Induct_on `L`
>-( rw [FBLOCK_DEF, ETREE_N_STAIR_DEF]
    \\ Induct_on `LN`
       >-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, ETREE_DEF])
    \\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF]
    \\ rw [GSYM EVENT_TREE_LIST_DEF]
    \\ rw [ALL_SCENARIOS_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
    \\ rw [GSYM EVENT_TREE_LIST_DEF]
    \\ rw [GSYM ALL_SCENARIOS_DEF]
    \\ rw [UNION_OVER_INTER, INTER_ASSOC]
    \\ metis_tac [INTER_ETREE_BRANCH])
\\ rw [FBLOCK_DEF, ETREE_N_STAIR_DEF]
\\ rw [GSYM FBLOCK_DEF]
\\ rw [GSYM ETREE_N_STAIR_DEF]
\\ rw [GSYM FBLOCK_ET_DEF]
\\ metis_tac [ALL_SCENARIOS_CARTESIAN_PRODUCT_EQ_BRANCH_TWO_N_STAIRS]);
(*-------------------------------------------------------------------------------------------------*)

val ETREE_NODE_ALL_SCENARIOS = store_thm("ETREE_NODE_ALL_SCENARIOS",
  ``!L h. h ∩ 𝓕𝓑𝑬𝑻 (ALL_SCENARIOS h L) = 𝓕𝓑𝑬𝑻 (ALL_SCENARIOS h L)``,
Induct
>-( rw [ALL_SCENARIOS_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, FBLOCK_ET_DEF])
\\ rw [ALL_SCENARIOS_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [EVENT_TREE_LIST_DEF, FBLOCK_ET_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ETREE_DEF, UNION_OVER_INTER, INTER_ASSOC]
\\ rw [GSYM FBLOCK_ET_DEF]);
(*-------------------------------------------------------------------------------------------------*)

val BRANCH_N_STAIR_EQ_NODE_ALL_SCENARIOS_FB = store_thm("BRANCH_N_STAIR_EQ_NODE_ALL_SCENARIOS_FB",
  ``!h LN L. ETREE (BRANCH h (ETREE_N_STAIR (EVENT_TREE_LIST LN) L)) =
       	     𝓕𝓑𝑬𝑻 (ALL_SCENARIOS h (FBLOCK (LN::L)))``,
	     
once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct_on `L`
   >-( rw [FBLOCK_DEF, ETREE_N_STAIR_DEF]
       \\ Induct_on `LN`
       	  >-( rw [EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF, ETREE_DEF])
       \\ rw [EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF]
       \\ rw [GSYM EVENT_TREE_LIST_DEF]
       \\ rw [GSYM ALL_SCENARIOS_DEF]
       \\ rw [ETREE_DEF, UNION_OVER_INTER]
       \\ sg `h ∩ ETREE (NODE (EVENT_TREE_LIST (ALL_SCENARIOS h LN))) =
       	      ETREE (NODE (EVENT_TREE_LIST (ALL_SCENARIOS h LN)))`
	  >-( POP_ORW
	      \\ Induct_on `LN`
	      	 >-( rw [ALL_SCENARIOS_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF])
              \\ rw [ALL_SCENARIOS_DEF]
	      \\ rw [GSYM ALL_SCENARIOS_DEF]
	      \\ rw [EVENT_TREE_LIST_DEF]
	      \\ rw [GSYM EVENT_TREE_LIST_DEF]
	      \\ rw [ETREE_DEF, UNION_OVER_INTER, INTER_ASSOC])
        \\ fs [])
\\ rw [FBLOCK_DEF, ETREE_N_STAIR_DEF]
\\ rw [GSYM FBLOCK_DEF]
\\ rw [GSYM ETREE_N_STAIR_DEF]
\\ Induct_on `h`
   >-( rw [ETREE_TWO_STAIR_DEF, CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF,
           EVENT_TREE_LIST_DEF, ETREE_DEF])
\\ rw [CARTESIAN_PRODUCT_DEF, ETREE_TWO_STAIR_DEF]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ rw [ETREE_DEF, ALL_SCENARIOS_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ETREE_NODE_SPLIT, UNION_OVER_INTER]
\\ Q.ABBREV_TAC ` X = ETREE  (NODE (EVENT_TREE_LIST (ALL_SCENARIOS h'
                             (CARTESIAN_PRODUCT h (FBLOCK (LN::L))))))`
\\ sg `h' ∩  ETREE (NODE (EVENT_TREE_LIST (ALL_SCENARIOS h'' (FBLOCK (LN::L))))) =
        ETREE (NODE (EVENT_TREE_LIST (ALL_SCENARIOS h' (ALL_SCENARIOS h'' (FBLOCK (LN::L))))))` 
   >-( ntac 2 POP_ORW
       \\ sg `ALL_SCENARIOS h' (ALL_SCENARIOS h'' (FBLOCK (LN::L))) =
       	      ALL_SCENARIOS (h' INTER h'') (FBLOCK (LN::L))`
	  >-(metis_tac [CONSECUTIVE_ALL_SCENARIOS])
       \\ fs []
       \\ POP_ORW
       \\ first_x_assum (mp_tac o Q.SPECL [`h' ∩ h''`,`LN`])
       \\ rw []
       \\ sg `ETREE (NODE (EVENT_TREE_LIST (ALL_SCENARIOS (h' ∩ h'') (FBLOCK (LN::L))))) =
              ETREE (BRANCH (h' ∩ h'') (ETREE_N_STAIR (EVENT_TREE_LIST LN) L))`
	  >-(metis_tac [])
       \\ fs []
       \\ REPEAT POP_ORW
       \\ rw [GSYM FBLOCK_ET_DEF]
       \\ rw [INTER_NODE_ALL_SCENARIOS_FB_EQ_BRANCH_INTER_N_STAIR])
\\ fs []
\\ Q.UNABBREV_TAC `X`
\\ rw [GSYM FBLOCK_ET_DEF]
\\ metis_tac [ETREE_NODE_ALL_SCENARIOS]);
(*-------------------------------------------------------------------------------------------------*)

(*----------------*)  
(*   PROPERTY 1   *)
(*----------------*)

val FBLOCK_EQ_ETREE_N_STAIR = store_thm("FBLOCK_EQ_ETREE_N_STAIR",
  ``!L LN. 𝓕𝓑𝑬𝑻 (FBLOCK (LN::L)) = ETREE (NODE (⊗Ν𝑳 (EVENT_TREE_LIST LN) L))``,
  
once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [FBLOCK_DEF, FBLOCK_DEF, ETREE_N_STAIR_DEF])
\\ rw [FBLOCK_DEF, ETREE_N_STAIR_DEF]
\\ rw [GSYM FBLOCK_DEF]
\\ rw [GSYM ETREE_N_STAIR_DEF]
\\ Induct_on `h`
   >-( rw [ETREE_TWO_STAIR_DEF, CARTESIAN_PRODUCT_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF])
\\ rw [ETREE_TWO_STAIR_DEF, CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ETREE_DEF]
\\ Q.ABBREV_TAC `x = EVENT_TREE_LIST (CARTESIAN_PRODUCT h (FBLOCK (LN::L)))`
\\ rw [ETREE_NODE_SPLIT]
\\ rw [GSYM FBLOCK_ET_DEF]
\\ metis_tac [BRANCH_N_STAIR_EQ_NODE_ALL_SCENARIOS_FB]);
(*-------------------------------------------------------------------------------------------------*)

(*----------------*)  
(*   PROPERTY 2   *)
(*----------------*)

val CARTESIAN_PRODUCT_COMMUTATIVE = store_thm("CARTESIAN_PRODUCT_COMMUTATIVE",
``! Y X. 𝓕𝓑𝑬𝑻 ($⊗ X Y) = 𝓕𝓑𝑬𝑻  ($⊗ Y X)``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [CARTESIAN_PRODUCT_DEF, EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF, ETREE_DEF]
    \\ Induct_on `X`
       >-(  rw [CARTESIAN_PRODUCT_DEF, EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF, ETREE_DEF])
    \\  rw [CARTESIAN_PRODUCT_DEF, EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF, ETREE_DEF])
\\ rw [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF]
\\ Induct_on `X`
   >-( rw [CARTESIAN_PRODUCT_DEF, EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF, ETREE_DEF]
       \\ POP_ORW
       \\ Induct_on `Y`
       	  >-(  rw [CARTESIAN_PRODUCT_DEF, EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF, ETREE_DEF])
       \\  rw [CARTESIAN_PRODUCT_DEF, EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF, ETREE_DEF])
\\ rw [CARTESIAN_PRODUCT_DEF, EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ETREE_DEF, ETREE_NODE_SPLIT]
\\ POP_ASSUM MP_TAC
\\ fs [EVENT_TREE_LIST_DEF]
\\ fs [GSYM EVENT_TREE_LIST_DEF]
\\ fs [ETREE_NODE_SPLIT]
\\ fs [GSYM ALL_SCENARIOS_DEF]
\\ sg `ETREE (NODE (EVENT_TREE_LIST (FLAT (MAP (λa. a ∩ h'::ALL_SCENARIOS a X) Y)))) =
       ETREE (NODE (EVENT_TREE_LIST (ALL_SCENARIOS h' Y))) ∪
       ETREE (NODE (EVENT_TREE_LIST (FLAT (MAP (λa. ALL_SCENARIOS a X) Y)))) `
   >-( sg `ETREE (NODE (EVENT_TREE_LIST ($⊗ X Y))) =
           ETREE (NODE (EVENT_TREE_LIST ($⊗ Y X))) `
       >-( first_x_assum (mp_tac o Q.SPECL [`(X)`])
       	   \\ metis_tac [])
       \\ first_x_assum (mp_tac o Q.SPECL [`(h'::X)`])
       \\ rw []
       \\ fs [CARTESIAN_PRODUCT_DEF, EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF,
              ETREE_DEF, ETREE_NODE_SPLIT]
       \\ fs [GSYM ALL_SCENARIOS_DEF]
       \\ fs [GSYM EVENT_TREE_LIST_DEF]
       \\ sg `ETREE
               (NODE (EVENT_TREE_LIST (FLAT (MAP (λa. a ∩ h'::ALL_SCENARIOS a X) Y)))) =
	       ETREE (NODE (EVENT_TREE_LIST (ALL_SCENARIOS h' Y))) ∪
               ETREE (NODE (EVENT_TREE_LIST (FLAT (MAP (λa. ALL_SCENARIOS a Y) X))))`
	  >-( metis_tac [])
        \\ fs []) 
\\ rw []
\\ sg `h' ∩ h =  h ∩ h'`
   >-( metis_tac [INTER_COMM])
\\ fs []
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val CARTESIAN_PRODUCT_ALL_SCENARIOS = store_thm("CARTESIAN_PRODUCT_ALL_SCENARIOS",
``!Z X h.  𝓕𝓑𝑬𝑻 ($⊗ (ALL_SCENARIOS h X) Z) = 𝓕𝓑𝑬𝑻 ($⊗ X (ALL_SCENARIOS h Z))``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
  >-( rw [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF, MAP, FLAT]
      \\ Induct_on `X`
	 >-( rw [])
      \\ rw [])
\\ rw [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF, MAP, FLAT]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ sg ` (MAP (λa. a ∩ (h' ∩ h)::ALL_SCENARIOS a (ALL_SCENARIOS h' Z)) X) =
        (MAP (λa. ALL_SCENARIOS a [h' ∩ h] ++ ALL_SCENARIOS a (ALL_SCENARIOS h' Z)) X)`
   >-( rw [APPEND, ALL_SCENARIOS_DEF])
\\ POP_ORW
\\ rw [EVENT_TREE_LIST_SPLIT, ETREE_NODE_SPLIT]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ sg `(MAP (λa. a ∩ h::ALL_SCENARIOS a Z) (ALL_SCENARIOS h' X)) =
       (MAP (λa. ALL_SCENARIOS a [h] ++ ALL_SCENARIOS a Z) (ALL_SCENARIOS h' X))`
   >-( rw [APPEND, ALL_SCENARIOS_DEF])
\\ POP_ORW
\\ rw [EVENT_TREE_LIST_SPLIT, ETREE_NODE_SPLIT]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ sg `ETREE (NODE (EVENT_TREE_LIST ($⊗ (ALL_SCENARIOS h' X) [h]))) =
       ETREE (NODE (EVENT_TREE_LIST ($⊗ X [h' ∩ h])))`
   >-( rw [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF, MAP, FLAT]
       \\ POP_ORW
       \\ Induct_on `X`
          >-( rw [])
       \\ rw []
       \\ rw [EVENT_TREE_LIST_DEF]
       \\ rw [GSYM EVENT_TREE_LIST_DEF]
       \\ rw [ETREE_DEF]
       \\ sg `h' ∩ h'' ∩ h = h'' ∩ (h' ∩ h) `
          >-( rw [EXTENSION]
	      \\ metis_tac [])
       \\ POP_ORW
       \\ metis_tac [])
\\ POP_ORW
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val DOUBLE_ALL_SCENARIOS = store_thm("DOUBLE_ALL_SCENARIOS",
``!Y h' h''. ALL_SCENARIOS h' (ALL_SCENARIOS h'' Y) = ALL_SCENARIOS (h' ∩ h'') Y``,

Induct
>-( rw [ALL_SCENARIOS_DEF])
\\ rw [ALL_SCENARIOS_DEF]
    >-( rw [EXTENSION]
       	\\ metis_tac [])
\\ rw [GSYM ALL_SCENARIOS_DEF]);
(*-------------------------------------------------------------------------------------------------*)

val CARTESIAN_PRODUCT_ALL_SCENARIOS_OF_FB = store_thm("CARTESIAN_PRODUCT_ALL_SCENARIOS_OF_FB",
``!Y Z X h. 𝓕𝓑𝑬𝑻 ($⊗ (ALL_SCENARIOS h (𝓕𝓑 (X::Y))) Z) = 𝓕𝓑𝑬𝑻 ($⊗ X (ALL_SCENARIOS h (𝓕𝓑 (Z::Y))))``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [FBLOCK_DEF]
    \\ rw [GSYM FBLOCK_ET_DEF]
    \\ metis_tac [CARTESIAN_PRODUCT_ALL_SCENARIOS])
\\ rw [FBLOCK_DEF]
\\ rw [GSYM FBLOCK_DEF]
\\ Induct_on `h`
   >-( rw [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF, MAP, FLAT]
       \\ Induct_on `X`
          >-( rw [])
       \\ rw [])
\\ rw [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF, MAP, FLAT]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ rw [EVENT_TREE_LIST_SPLIT, ETREE_NODE_SPLIT]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ sg `ETREE
          (NODE
             (EVENT_TREE_LIST
                ($⊗ X (ALL_SCENARIOS h' ($⊗ h (𝓕𝓑 (Z::Y))))))) =
      ETREE
          (NODE
             (EVENT_TREE_LIST
                ($⊗ (ALL_SCENARIOS h' ($⊗ h (𝓕𝓑 (X::Y)))) Z)))`
   >-( metis_tac [])
\\ POP_ORW
\\ rw [EVENT_TREE_SPLIT, ETREE_NODE_SPLIT]
\\ POP_ORW
\\ sg `ETREE
          (NODE
             (EVENT_TREE_LIST
                ($⊗ (ALL_SCENARIOS h' (ALL_SCENARIOS h'' (𝓕𝓑 (X::Y)))) Z))) =
       ETREE
          (NODE
             (EVENT_TREE_LIST
                ($⊗ X (ALL_SCENARIOS h' (ALL_SCENARIOS h'' (𝓕𝓑 (Z::Y)))))))`
   >-( sg `ALL_SCENARIOS h' (ALL_SCENARIOS h'' (𝓕𝓑 (X::Y))) =
           ALL_SCENARIOS (h' ∩ h'') (𝓕𝓑 (X::Y))`
       >-( metis_tac [DOUBLE_ALL_SCENARIOS])
       \\ POP_ORW
       \\ rw [DOUBLE_ALL_SCENARIOS])
\\ POP_ORW
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

(*----------------*)  
(*   PROPERTY 3   *)
(*----------------*)

val FBLOCK_ASSOCIATIVE_AND_COMMUTATIVE = store_thm("FBLOCK_ASSOCIATIVE_AND_COMMUTATIVE",
``! Y X Z. 𝓕𝓑𝑬𝑻 ($⊗ (𝓕𝓑 (X::Y)) Z) = 𝓕𝓑𝑬𝑻 ($⊗ X (𝓕𝓑 (Z::Y)))``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [FBLOCK_DEF])
\\ rw [FBLOCK_DEF]
\\ rw [GSYM FBLOCK_DEF]
\\ Induct_on `h`
   >-( rw [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF, MAP, FLAT]
       \\ POP_ORW
       \\ Induct_on `X`
       	  >-( rw [])
       \\ rw [MAP, FLAT])
\\ rw [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ rw [EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ fs [ETREE_NODE_SPLIT, EVENT_TREE_LIST_SPLIT]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ POP_ORW
\\ rw [GSYM FBLOCK_ET_DEF]
\\ metis_tac [CARTESIAN_PRODUCT_ALL_SCENARIOS_OF_FB]);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA1 = store_thm("LEMMA1",
``!YS X Z. 𝓕𝓑𝑬𝑻 (ALL_SCENARIOS X (FLAT (MAP (λa. [Z ∩ a]) YS))) = X ∩ Z ∩ 𝓕𝓑𝑬𝑻 YS``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [INTER_ASSOC, UNION_OVER_INTER]);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA2 = store_thm("LEMMA2",
``!XS Y Z. 𝓕𝓑𝑬𝑻 ($⊗ XS [Y ∩ Z]) = Y ∩ 𝓕𝓑𝑬𝑻 (FLAT (MAP (λa. [Z ∩ a]) XS))``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF] 
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`Y`, `Z`])
\\ rw []
\\ fs [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF]
\\ rw [UNION_OVER_INTER, INTER_ASSOC]
\\ sg `h ∩ Y ∩ Z = Y ∩ Z ∩ h `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA3 = store_thm("LEMMA3",
`` !XS Z h. 𝓕𝓑𝑬𝑻 ($⊗ XS [Z ∩ h]) = h ∩ 𝓕𝓑𝑬𝑻 (FLAT (MAP (λa. [Z ∩ a]) XS))``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct 
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, CARTESIAN_PRODUCT_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF, CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ETREE_NODE_SPLIT]
\\ fs [CARTESIAN_PRODUCT_DEF]
\\ rw [EVENT_TREE_LIST_DEF, ALL_SCENARIOS_DEF, ETREE_DEF, CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [UNION_OVER_INTER, INTER_ASSOC]
\\ sg `h ∩ Z ∩ h' = h' ∩ Z ∩ h `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA4 = store_thm("LEMMA4",
`` !YS XS Z. 𝓕𝓑𝑬𝑻 ($⊗ XS (FLAT (MAP (λa. [Z ∩ a]) YS))) =
       	     𝓕𝓑𝑬𝑻 YS ∩ 𝓕𝓑𝑬𝑻 (FLAT (MAP (λa. [Z ∩ a]) XS))``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF]
    \\ Induct_on `XS`
       >-( rw [ETREE_DEF])
    \\  rw [ETREE_DEF])
\\  rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ sg `(MAP (λa. a ∩ (Z ∩ h):: ALL_SCENARIOS a (FLAT (MAP (λa. [Z ∩ a]) YS))) XS) =
       (MAP (λa. ALL_SCENARIOS a [Z ∩ h] ++ ALL_SCENARIOS a (FLAT (MAP (λa. [Z ∩ a]) YS))) XS)`
   >-( rw [APPEND, ALL_SCENARIOS_DEF])
\\ POP_ORW
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [EVENT_TREE_LIST_SPLIT, ETREE_NODE_SPLIT]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ sg ` (h ∪ ETREE (NODE (EVENT_TREE_LIST YS))) ∩
        ETREE (NODE (EVENT_TREE_LIST (FLAT (MAP (λa. [Z ∩ a]) XS)))) =
	ETREE (NODE (EVENT_TREE_LIST (FLAT (MAP (λa. [Z ∩ a]) XS)))) ∩
	(h ∪ ETREE (NODE (EVENT_TREE_LIST YS)))`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ rw [UNION_OVER_INTER, INTER_COMM]
\\ sg ` ETREE (NODE (EVENT_TREE_LIST ($⊗ XS [Z ∩ h]))) =
        h ∩ ETREE (NODE (EVENT_TREE_LIST (FLAT (MAP (λa. [Z ∩ a]) XS))))`
   >-( rw [GSYM FBLOCK_ET_DEF]
       \\ metis_tac [LEMMA3])
\\ POP_ORW
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA5 = store_thm("LEMMA5",
``! ZS X Y.  𝓕𝓑𝑬𝑻 (ALL_SCENARIOS X (ALL_SCENARIOS Y ZS)) = 𝓕𝓑𝑬𝑻 (ALL_SCENARIOS X ZS) ∩ Y ``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF])
\\  rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [INTER_COMM, UNION_OVER_INTER]
\\ sg ` X ∩ (Y ∩ h) = Y ∩ (X ∩ h) `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA6 = store_thm("LEMMA6",
``!YS Z ZS h X.
       𝓕𝓑𝑬𝑻 (ALL_SCENARIOS X (FLAT (MAP (λa. ALL_SCENARIOS a [Z; h] ⧺ ALL_SCENARIOS a ZS) YS))) =
       X ∩ Z ∩ 𝓕𝓑𝑬𝑻 YS ∪ X ∩ h ∩ 𝓕𝓑𝑬𝑻 YS ∪ 𝓕𝓑𝑬𝑻 (ALL_SCENARIOS X ZS) ∩ 𝓕𝓑𝑬𝑻 YS``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF])
\\  rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [ETREE_NODE_SPLIT]
\\ rw [INTER_COMM, UNION_OVER_INTER]
\\ rw [INTER_ASSOC, UNION_ASSOC]
\\ sg ` (MAP (λa. Z ∩ a::a ∩ h'::ALL_SCENARIOS a ZS) YS) =
        (MAP (λa. ALL_SCENARIOS a [Z; h'] ⧺ ALL_SCENARIOS a ZS) YS)`
   >-( rw [APPEND, ALL_SCENARIOS_DEF]
       \\ rw [INTER_COMM])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`Z`, `ZS`, `h'`, `X`])
\\ rw [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [LEMMA5]
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA7 = store_thm("LEMMA7",
``!XS Z Y h. 𝓕𝓑𝑬𝑻 (FLAT (MAP (λa. ALL_SCENARIOS a [Y ∩ Z; Y ∩ h]) XS)) =
       	     𝓕𝓑𝑬𝑻 ($⊗ XS [Z; h]) ∩ Y``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`Z`, `Y`, `h'`])
\\ rw []
\\ fs [ALL_SCENARIOS_DEF]
\\ rw [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF]
\\ rw [INTER_COMM, UNION_OVER_INTER]
\\ rw [INTER_ASSOC, UNION_ASSOC]
\\ sg `h ∩ Y ∩ Z = Y ∩ Z ∩ h `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg ` h ∩ Y ∩ h' = Y ∩ h ∩ h'`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA8 = store_thm("LEMMA8",
``! XS ZS Y. 𝓕𝓑𝑬𝑻 (FLAT (MAP (λa. ALL_SCENARIOS a (ALL_SCENARIOS Y ZS)) XS)) = 𝓕𝓑𝑬𝑻 ($⊗ XS ZS) ∩ Y``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`ZS`, `Y`])
\\ rw [ETREE_NODE_SPLIT]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM FBLOCK_ET_DEF]
\\ rw [LEMMA5]
\\ rw [INTER_COMM, UNION_OVER_INTER]
\\ rw [UNION_ASSOC, INTER_ASSOC]);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA9 = store_thm("LEMMA9",
``!ZS X Y. 𝓕𝓑𝑬𝑻 (MAP (λa. a ∩ X) (MAP (λa. a ∩ Y) ZS)) = Y ∩ 𝓕𝓑𝑬𝑻 (MAP (λa. a ∩ X) ZS)``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [UNION_OVER_INTER, INTER_ASSOC]
\\ sg `h ∩ Y ∩ X =  Y ∩ h ∩ X`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA10 = store_thm("LEMMA10",
``!YS ZS Z h S.
       𝓕𝓑𝑬𝑻
          (ALL_SCENARIOS h
                   (FLAT
                      (MAP
                         (λa.
                              ALL_SCENARIOS a [Z] ⧺ ALL_SCENARIOS a [S] ⧺
                              ALL_SCENARIOS a ZS) YS))) =
	𝓕𝓑𝑬𝑻 YS ∩ Z ∩ h ∪ 𝓕𝓑𝑬𝑻 YS ∩ h ∩ S ∪ 𝓕𝓑𝑬𝑻 YS ∩ 𝓕𝓑𝑬𝑻 (MAP (λa. a ∩ h) ZS)``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`ZS`, `Z`, `h'`, `S'`])
\\ rw [ETREE_NODE_SPLIT]
\\ rw [INTER_COMM, UNION_OVER_INTER]
\\ rw [UNION_ASSOC, INTER_ASSOC]
\\ fs [ALL_SCENARIOS_DEF, INTER_COMM]
\\ rw [INTER_COMM, UNION_OVER_INTER]
\\ rw [UNION_ASSOC, INTER_ASSOC]
\\ sg `h' ∩ Z ∩ ETREE (NODE (EVENT_TREE_LIST YS)) = Z ∩ h' ∩ ETREE (NODE (EVENT_TREE_LIST YS)) `
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `(h ∪ ETREE (NODE (EVENT_TREE_LIST YS))) ∩ ETREE (NODE (EVENT_TREE_LIST (MAP (λa. a ∩ h') ZS))) =
       ETREE (NODE (EVENT_TREE_LIST (MAP (λa. a ∩ h') ZS)))  ∩ (h ∪ ETREE (NODE (EVENT_TREE_LIST YS)))`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ rw [INTER_COMM, UNION_OVER_INTER]
\\ rw [UNION_ASSOC, INTER_ASSOC]
\\ sg `ETREE (NODE (EVENT_TREE_LIST (MAP (λa. a ∩ h') (MAP (λa. a ∩ h) ZS)))) =
       h ∩ ETREE (NODE (EVENT_TREE_LIST (MAP (λa. a ∩ h') ZS)))`
   >-( rw [GSYM FBLOCK_ET_DEF]
       \\ metis_tac [LEMMA9])
\\ POP_ORW
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA11 = store_thm("LEMMA11",
``!XS ZS YS Z h.
            𝓕𝓑𝑬𝑻 (FLAT
                   (MAP
                      (λa.
                           ALL_SCENARIOS a
                             (FLAT
                                (MAP
                                   (λa. ALL_SCENARIOS a [Z; h] ⧺ ALL_SCENARIOS a ZS)
                                   YS))) XS)) =
        𝓕𝓑𝑬𝑻 ($⊗ XS ZS) ∩ 𝓕𝓑𝑬𝑻 YS ∪ 𝓕𝓑𝑬𝑻 ($⊗ XS [Z; h]) ∩ 𝓕𝓑𝑬𝑻 YS``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`ZS`, `YS`, `Z`, `h'`])
\\ rw [ETREE_NODE_SPLIT]
\\ fs [GSYM CARTESIAN_PRODUCT_DEF]
\\ fs [ALL_SCENARIOS_DEF, INTER_COMM]
\\ fs [GSYM ALL_SCENARIOS_DEF]
\\ rw [UNION_OVER_INTER, INTER_COMM]
\\ rw [UNION_ASSOC, INTER_ASSOC]
\\ sg `ETREE
          (NODE
             (EVENT_TREE_LIST
                (MAP (λa. a ∩ h)
                   (FLAT (MAP (λa. Z ∩ a::a ∩ h'::ALL_SCENARIOS a ZS) YS))))) =
       ETREE
          (NODE
             (EVENT_TREE_LIST
                (ALL_SCENARIOS h 
                   (FLAT (MAP (λa. ALL_SCENARIOS a [Z] ++ ALL_SCENARIOS a [h'] ++ ALL_SCENARIOS a ZS) YS)))))`
    >-( rw [APPEND, ALL_SCENARIOS_DEF]
    	\\ rw [INTER_COMM])
\\ POP_ORW
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ sg `(MAP (λa. [Z ∩ a; a ∩ h']) XS) = (MAP (λa. ALL_SCENARIOS a [Z;h']) XS) `
   >-( rw [ALL_SCENARIOS_DEF]
       \\ rw [INTER_COMM])
\\ POP_ORW
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [LEMMA10]
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

(*----------------*)  
(*   PROPERTY 4   *)
(*----------------*)

val CONSECUTIVE_CARTESIAN_SPLIT = store_thm("CONSECUTIVE_CARTESIAN_SPLIT",
``!ZS Z XS X YS Y.
    𝓕𝓑𝑬𝑻 ($⊗ (X::XS) ($⊗ (Y::YS) (Z::ZS))) = 𝓕𝓑𝑬𝑻 (Y::YS) INTER 𝓕𝓑𝑬𝑻 ($⊗ (X::XS) (Z::ZS))``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF]
    \\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF]
    \\ rw [GSYM EVENT_TREE_LIST_DEF]
    \\ rw [GSYM ALL_SCENARIOS_DEF]
    \\ rw [GSYM CARTESIAN_PRODUCT_DEF]
    \\ sg `!a b c d. (a UNION b) INTER (c UNION d) =
                     (a INTER c) UNION (a INTER d) UNION (b INTER c)  UNION (b INTER d)`
       >-( rw [EXTENSION]
       	   \\ metis_tac [])
    \\ fs []
    \\ rw [ETREE_NODE_SPLIT]
    \\ sg `(MAP (λa. a ∩ (Y ∩ Z):: ALL_SCENARIOS a (FLAT (MAP (λa. [a ∩ Z]) YS))) XS) =
           (MAP (λa. ALL_SCENARIOS a [Y ∩ Z] ++  ALL_SCENARIOS a (FLAT (MAP (λa. [a ∩ Z]) YS))) XS)`
       >-( rw [APPEND, ALL_SCENARIOS_DEF])
    \\ POP_ORW
    \\ fs [EVENT_TREE_LIST_SPLIT]
    \\ rw [GSYM CARTESIAN_PRODUCT_DEF]
    \\ rw [ETREE_NODE_SPLIT, INTER_COMM]
    \\ POP_ORW
    \\ sg `X ∩ (Y ∩ Z) = Y ∩ (X ∩ Z) `
       >-( rw [EXTENSION]
       	   \\ metis_tac [])
    \\ POP_ORW
    \\ rw [UNION_ASSOC]
    \\ sg `ETREE (NODE (EVENT_TREE_LIST (ALL_SCENARIOS X (FLAT (MAP (λa. [Z ∩ a]) YS))))) =
            X ∩ Z ∩ ETREE (NODE (EVENT_TREE_LIST YS))`
       >-( rw [GSYM FBLOCK_ET_DEF]
       	   \\ metis_tac [LEMMA1])
    \\ POP_ORW
    \\ rw [INTER_ASSOC]
    \\ sg `ETREE (NODE (EVENT_TREE_LIST ($⊗ XS [Y ∩ Z]))) =
           Y ∩ ETREE (NODE (EVENT_TREE_LIST (FLAT (MAP (λa. [Z ∩ a]) XS))))`
       >-( rw [GSYM FBLOCK_ET_DEF]
       	   \\ metis_tac [LEMMA2])
    \\ POP_ORW
    \\ sg `ETREE (NODE (EVENT_TREE_LIST ($⊗ XS (FLAT (MAP (λa. [Z ∩ a]) YS))))) =
           ETREE (NODE (EVENT_TREE_LIST YS)) ∩
   	   ETREE (NODE (EVENT_TREE_LIST (FLAT (MAP (λa. [Z ∩ a]) XS))))`
         >-( rw [GSYM FBLOCK_ET_DEF]
	     \\ metis_tac [LEMMA4])
    \\ POP_ORW
    \\ rw [EXTENSION]
    \\ metis_tac [])
\\ rw [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ rw [UNION_OVER_INTER, INTER_ASSOC, ETREE_NODE_SPLIT, UNION_ASSOC]
\\ sg ` (MAP (λa. a ∩ Z::a ∩ h::ALL_SCENARIOS a ZS) YS) =
         (MAP (λa. ALL_SCENARIOS a [Z;h] ++ ALL_SCENARIOS a ZS) YS)`
   >-( rw [APPEND, ALL_SCENARIOS_DEF])
\\ POP_ORW
\\ sg ` (MAP (λa. a ∩ Z::a ∩ h::ALL_SCENARIOS a ZS) XS) =
         (MAP (λa. ALL_SCENARIOS a [Z;h] ++ ALL_SCENARIOS a ZS) XS)`
   >-( rw [APPEND, ALL_SCENARIOS_DEF])
\\ POP_ORW
\\ rw [EVENT_TREE_LIST_SPLIT, ETREE_NODE_SPLIT]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ rw [INTER_COMM, UNION_OVER_INTER]
\\ rw [INTER_ASSOC, UNION_ASSOC]
\\ sg `(MAP (λa. Z ∩ Y ∩ a::h ∩ Y ∩ a:: (ALL_SCENARIOS a (ALL_SCENARIOS Y ZS) ⧺
       ALL_SCENARIOS a (FLAT (MAP (λa. ALL_SCENARIOS a [Z; h] ⧺ ALL_SCENARIOS a ZS) YS)))) XS) =
       (MAP (λa. ALL_SCENARIOS a [Z ∩ Y; h ∩ Y] ++ (ALL_SCENARIOS a (ALL_SCENARIOS Y ZS) ⧺
       ALL_SCENARIOS a (FLAT (MAP (λa. ALL_SCENARIOS a [Z; h] ⧺ ALL_SCENARIOS a ZS) YS)))) XS)`
   >-( rw [APPEND, ALL_SCENARIOS_DEF]
       \\ rw [INTER_COMM])
\\ POP_ORW
\\ rw [EVENT_TREE_LIST_SPLIT, ETREE_NODE_SPLIT, EVENT_TREE_LIST_SPLIT_TRIPLE]
\\ rw [INTER_COMM, UNION_OVER_INTER, UNION_ASSOC]
\\ sg `(Y ∪ ETREE (NODE (EVENT_TREE_LIST YS))) ∩ ETREE (NODE (EVENT_TREE_LIST ($⊗ XS [Z; h]))) =
      ETREE (NODE (EVENT_TREE_LIST ($⊗ XS [Z; h]))) ∩ (Y ∪ ETREE (NODE (EVENT_TREE_LIST YS)))`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ rw [UNION_OVER_INTER, UNION_ASSOC, INTER_ASSOC]
\\ sg ` ETREE (NODE (EVENT_TREE_LIST (ALL_SCENARIOS X (ALL_SCENARIOS Y ZS)))) =
        ETREE (NODE (EVENT_TREE_LIST (ALL_SCENARIOS X ZS))) ∩ Y `
   >-( rw [GSYM FBLOCK_ET_DEF]
       \\ metis_tac [LEMMA5])
\\ POP_ORW
\\ sg `ETREE
          (NODE
             (EVENT_TREE_LIST
                (ALL_SCENARIOS X
                   (FLAT (MAP (λa. ALL_SCENARIOS a [Z; h] ⧺ ALL_SCENARIOS a ZS) YS))))) =
       X ∩ Z ∩ ETREE (NODE (EVENT_TREE_LIST YS)) ∪
       X ∩ h ∩ ETREE (NODE (EVENT_TREE_LIST YS)) ∪
       ETREE (NODE (EVENT_TREE_LIST (ALL_SCENARIOS X ZS))) ∩ ETREE (NODE (EVENT_TREE_LIST YS))`
   >-( rw [GSYM FBLOCK_ET_DEF]
       \\ metis_tac [LEMMA6])
\\ POP_ORW
\\ rw [UNION_ASSOC]
\\ sg `ETREE
          (NODE
             (EVENT_TREE_LIST
                (FLAT (MAP (λa. ALL_SCENARIOS a [Y ∩ Z; Y ∩ h]) XS)))) =
       ETREE (NODE (EVENT_TREE_LIST ($⊗ XS [Z; h]))) ∩ Y`
   >-( rw [GSYM FBLOCK_ET_DEF]
       \\ metis_tac [LEMMA7])
\\ POP_ORW
\\ sg `ETREE
          (NODE
             (EVENT_TREE_LIST
                (FLAT (MAP (λa. ALL_SCENARIOS a (ALL_SCENARIOS Y ZS)) XS)))) =
        ETREE (NODE (EVENT_TREE_LIST ($⊗ XS ZS))) ∩ Y`
   >-( rw [GSYM FBLOCK_ET_DEF]
       \\ metis_tac [LEMMA8])
\\ POP_ORW
\\ sg `ETREE
          (NODE
             (EVENT_TREE_LIST
                (FLAT
                   (MAP
                      (λa.
                           ALL_SCENARIOS a
                             (FLAT
                                (MAP
                                   (λa. ALL_SCENARIOS a [Z; h] ⧺ ALL_SCENARIOS a ZS)
                                   YS))) XS)))) =
       ETREE (NODE (EVENT_TREE_LIST ($⊗ XS ZS))) ∩ ETREE (NODE (EVENT_TREE_LIST YS)) ∪
       ETREE (NODE (EVENT_TREE_LIST ($⊗ XS [Z; h]))) ∩ ETREE (NODE (EVENT_TREE_LIST YS))`
   >-( rw [GSYM FBLOCK_ET_DEF]
       \\ metis_tac [LEMMA11])
\\ POP_ORW
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA12 = store_thm("LEMMA12",
``! X L Y. ETREE (BRANCH Y (⊗𝑳 X (EVENT_TREE_LIST L))) = Y ∩ ETREE (NODE (⊗𝑳 X (EVENT_TREE_LIST L)))``,

Induct
>-( rw [ETREE_TWO_STAIR_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF])
\\ rw [ETREE_TWO_STAIR_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [UNION_OVER_INTER, INTER_ASSOC]);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA13 = store_thm("LEMMA13",
``!Y X. 𝓕𝓑𝑬𝑻 (ALL_SCENARIOS X Y) =  X ∩ 𝓕𝓑𝑬𝑻 Y``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF])
\\ rw [EVENT_TREE_LIST_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [INTER_COMM, UNION_OVER_INTER]);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA14 = store_thm("LEMMA14",
``!X Y. 𝓕𝓑𝑬𝑻 ($⊗ X Y) = 𝓕𝓑𝑬𝑻 X ∩ 𝓕𝓑𝑬𝑻 Y``,   

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [CARTESIAN_PRODUCT_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF])
\\ rw [CARTESIAN_PRODUCT_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ETREE_NODE_SPLIT]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [LEMMA13]
\\ rw [INTER_COMM, UNION_OVER_INTER, INTER_ASSOC]
\\ metis_tac [INTER_COMM]);
(*-------------------------------------------------------------------------------------------------*)

val LEMMA15 = store_thm("LEMMA15",
``∀X Y Z.   𝓕𝓑𝑬𝑻 ($⊗ X ($⊗ Y Z)) = 𝓕𝓑𝑬𝑻 X ∩ 𝓕𝓑𝑬𝑻 Y ∩ 𝓕𝓑𝑬𝑻 Z``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ Induct
>-( rw [CARTESIAN_PRODUCT_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF])
\\ rw [CARTESIAN_PRODUCT_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ETREE_NODE_SPLIT]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [LEMMA13]
\\ first_x_assum (mp_tac o Q.SPECL [`Y`, `Z`])
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER, INTER_ASSOC]
\\ fs [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [LEMMA14]
\\ rw [UNION_OVER_INTER, INTER_ASSOC]
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val N_FBLOCKS_EQ_CARTESIAN_FBS= store_thm("N_FBLOCKS_EQ_CARTESIAN_FBS",
``!L X XS Y YS.  𝓕𝓑𝑬𝑻 (𝓕𝓑Ν ((X::XS)::(Y::YS)::L)) = 𝓕𝓑𝑬𝑻 ($⊗ (𝓕𝓑Ν ((Y::YS)::L)) (𝓕𝓑 (X::XS)))``,

Induct
>-( rw [FBLOCK_N_DEF, FBLOCK_DEF]
    \\ rw [FBLOCK_DEF, FBLOCK_ET_DEF])
\\ rw [FBLOCK_N_DEF, FBLOCK_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`X`, `XS`, `Y`, `YS`])
\\ rw []
\\ fs [GSYM FBLOCK_DEF]
\\ DEP_REWRITE_TAC [LEMMA14]
\\ fs [FBLOCK_N_DEF]
\\ fs [FBLOCK_DEF]
\\ fs [LEMMA14]
\\ fs [GSYM FBLOCK_DEF]
\\ fs [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ sg `𝓕𝓑𝑬𝑻 (𝓕𝓑 (Y::YS)) ∩ 𝓕𝓑𝑬𝑻 (𝓕𝓑 h) ∩ 𝓕𝓑𝑬𝑻 (𝓕𝓑 (𝓕𝓑 (X::XS)::MAP (λa. 𝓕𝓑 a) L)) =
       𝓕𝓑𝑬𝑻 (𝓕𝓑 h) ∩ (𝓕𝓑𝑬𝑻 (𝓕𝓑 (Y::YS)) ∩ 𝓕𝓑𝑬𝑻 (𝓕𝓑 (𝓕𝓑 (X::XS)::MAP (λa. 𝓕𝓑 a) L)))`
   >-(rw [EXTENSION]
      \\ metis_tac [])
\\ POP_ORW
\\ fs []
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

(*----------------*)  
(*   PROPERTY 5   *)
(*----------------*)

val FBLOCK_N_SPLIT= store_thm("FBLOCK_N_SPLIT",
``!L X XS Y YS.   𝓕𝓑𝑬𝑻 (𝓕𝓑Ν ((X::XS)::(Y::YS)::L)) =
                  ETREE (BRANCH (𝓕𝓑𝑬𝑻 (𝓕𝓑 (X::XS))) (EVENT_TREE_LIST (𝓕𝓑Ν ((Y::YS)::L))))``,

rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ DEP_REWRITE_TAC [N_FBLOCKS_EQ_CARTESIAN_FBS]
\\ rw [LEMMA14]
\\ rw [GSYM FBLOCK_ET_DEF]
\\ rw [GSYM FBLOCK_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [FBLOCK_N_DEF, FBLOCK_DEF]
\\ DEP_REWRITE_TAC [BRANCH_EQ_INTER_NODE]
\\ rw [GSYM FBLOCK_ET_DEF]
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val FB_ET_ALL_SCENARIOS_IN_EVENTS = store_thm("FB_ET_ALL_SCENARIOS_IN_EVENTS",
``!p Y h. (prob_space p) /\ (!y. MEM y (h::Y) ==> y IN events p) ==>
          𝓕𝓑𝑬𝑻 (ALL_SCENARIOS h Y) ∈ events p``, 

once_rewrite_tac [FBLOCK_ET_DEF]
\\ GEN_TAC
\\ Induct
   >-( rw [ETREE_DEF, ALL_SCENARIOS_DEF, EVENT_TREE_LIST_DEF]
       \\ metis_tac [EVENTS_EMPTY])
\\ rw [ETREE_DEF, ALL_SCENARIOS_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ pop_assum mp_tac
\\ first_x_assum (mp_tac o Q.SPECL [`h'`])
\\ rw []
\\ sg `(∀y. y = h' ∨ MEM y Y ⇒ y ∈ events p) `
   >-( metis_tac [])
\\ FULL_SIMP_TAC std_ss[]
\\ sg `ETREE (NODE (EVENT_TREE_LIST (ALL_SCENARIOS h' Y))) ∈ events p `
   >-( metis_tac [])
\\ fs []
\\ rw []
\\ metis_tac [EVENTS_UNION, EVENTS_INTER]);
(*-------------------------------------------------------------------------------------------------*)

val CARTESIAN_PRODUCT_IN_EVENTS = store_thm("CARTESIAN_PRODUCT_IN_EVENTS",
``!p X Y. (prob_space p) /\ (!y. MEM y (FLAT [X ++ Y]) ==> y IN events p) ==>
           𝓕𝓑𝑬𝑻 ($⊗ X Y) ∈ events p``, 
once_rewrite_tac [FBLOCK_ET_DEF]
\\ rw []
\\ Induct_on `X`
   >-( rw [CARTESIAN_PRODUCT_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, EVENTS_EMPTY])
\\ rw [CARTESIAN_PRODUCT_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ rw [ETREE_NODE_SPLIT]
\\ sg `ETREE (NODE (EVENT_TREE_LIST ($⊗ X Y))) ∈ events p `
   >-( metis_tac [])
\\ sg ` ETREE (NODE (EVENT_TREE_LIST (ALL_SCENARIOS h Y))) ∈ events p `
   >-( rw [GSYM FBLOCK_ET_DEF]
       \\ DEP_REWRITE_TAC [FB_ET_ALL_SCENARIOS_IN_EVENTS]
       \\ fs []
       \\ metis_tac [])
\\ metis_tac [EVENTS_UNION]);
(*-------------------------------------------------------------------------------------------------*)

(*----------------*)  
(*   PROPERTY  6  *)
(*----------------*)

val PROB_PATH_INTER_NODE = store_thm("PROB_PATH_INTER_NODE",
``!p Y X.   (prob_space p) /\ (!y. MEM y (X ++ Y) ==> y IN events p)  /\ ~NULL X /\
            (MUTUAL_INDEP p (X ++ Y)) ==>
	    prob p (PATH p X ∩ 𝓕𝓑𝑬𝑻 Y) =
            prob p (PATH p X) * prob p (𝓕𝓑𝑬𝑻 Y)``,
	    
once_rewrite_tac [FBLOCK_ET_DEF]
\\ GEN_TAC
\\ Induct
   >-( rw [ETREE_DEF, ALL_SCENARIOS_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [PROB_EMPTY]
       \\ disj2_tac
       \\ rw [PROB_SUM_DEF])
\\ rw [ETREE_DEF, ALL_SCENARIOS_DEF, EVENT_TREE_LIST_DEF, PROB_SUM_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [UNION_OVER_INTER]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ rw []
   >-( metis_tac [PATH_IN_EVENTS, EVENTS_INTER])
   >-( metis_tac [PATH_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
   >-( metis_tac [NODE_IN_EVENTS])
\\ sg `prob p (PATH p X ∩ ETREE (NODE (EVENT_TREE_LIST Y))) =
       prob p (PATH p X) * prob p (ETREE (NODE (EVENT_TREE_LIST Y)))`   
   >-(  first_x_assum (match_mp_tac)
   	\\ rw []
	   >-( metis_tac [])
	   >-( metis_tac [])
        \\ irule MUTUAL_INDEP_FRONT_APPEND
	\\ Q.EXISTS_TAC `[h]`
	\\ once_rewrite_tac[APPEND_ASSOC]
       	\\ irule MUTUAL_INDEP_APPEND1
	\\ sg `X ⧺ [h] ⧺ Y =  X ⧺ h::Y`
	   >-( rw [APPEND])
	\\ rw [])
\\ POP_ORW
\\ rw [INTER_ASSOC]
\\ sg `PATH p X ∩ h ∩ PATH p X = PATH p X ∩ h`
   >-( rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `PATH p X ∩ h =  PATH p (h::X)`
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_COMM])
\\ POP_ORW
\\ sg `h ∩ ETREE (NODE (EVENT_TREE_LIST Y)) = PATH p [h] ∩ ETREE (NODE (EVENT_TREE_LIST Y)) `
   >-( rw [PATH_DEF]
       \\ rw [INTER_COMM]
       \\ sg ` h ∩ p_space p = h`
       	  >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ metis_tac [INTER_COMM])
\\ POP_ORW
\\ sg `prob p (PATH p [h] ∩ ETREE (NODE (EVENT_TREE_LIST Y))) =
       prob p h * prob p (ETREE (NODE (EVENT_TREE_LIST Y))) `
  >-(  first_x_assum (mp_tac o Q.SPECL [`[h]`])
       \\ rw []
       \\ sg `(∀y. y = h ∨ MEM y Y ⇒ y ∈ events p) `
          >-( metis_tac [])
       \\ sg `MUTUAL_INDEP p (h::Y) `
          >-( irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `X`
	      \\ rw [])
       \\ sg `prob p (PATH p [h] ∩ ETREE (NODE (EVENT_TREE_LIST Y))) =
              prob p (PATH p [h]) * prob p (ETREE (NODE (EVENT_TREE_LIST Y))) `
	  >-( metis_tac [])
       \\ POP_ORW
       \\ DEP_REWRITE_TAC [PROB_PATH]
       \\ rw []
          >-( irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `Y`
	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND_SYM
       	      \\ rw [])
       \\ disj2_tac
       \\ rw [PROD_LIST_DEF, PROB_LIST_DEF])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`(h::X)`])
\\ rw []
\\ fs []
\\ sg `(∀y. (y = h ∨ MEM y X) ∨ MEM y Y ⇒ y ∈ events p) `
   >-(metis_tac [])
\\ sg `MUTUAL_INDEP p (h::(X ⧺ Y)) `
   >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg `X ⧺ [h] ⧺ Y = X ⧺ h::Y`
	  >-( rw [APPEND])
       \\ rw [])
\\ sg `prob p (PATH p (h::X) ∩ ETREE (NODE (EVENT_TREE_LIST Y))) =
       prob p (PATH p (h::X)) * prob p (ETREE (NODE (EVENT_TREE_LIST Y)))`
   >-(metis_tac [])
\\ POP_ORW
\\ sg `prob p (PATH p (h::X)) = ∏ (PROB_LIST p (h::X)) `
   >-( DEP_REWRITE_TAC [PROB_PATH]
       \\ rw []
       	  >-( metis_tac [])
   	  >-( metis_tac [])
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `Y`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw [])
\\ POP_ORW
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `Y`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw []
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `[h]`
       \\ rw [])
\\ REAL_ARITH_TAC);
(*-------------------------------------------------------------------------------------------------*)

(*----------------*)  
(*   PROPERTY 7   *)
(*----------------*)

val PROB_ETREE_NODE_ALL_SCENARIOS= store_thm("PROB_ETREE_NODE_ALL_SCENARIOS",
``!p Y X.   (prob_space p) /\
    	    (!y. MEM y (X::Y) ==> y IN events p)  /\ ALL_DISTINCT Y /\ disjoint (set Y) /\
	    (MUTUAL_INDEP p (X::Y)) ==>
	    prob p (𝓕𝓑𝑬𝑻  (ALL_SCENARIOS X Y)) = (prob p X) *  ∑𝑷𝑹𝑶𝑩 p Y``, 

rw [LEMMA13]
\\ sg `X ∩ 𝓕𝓑𝑬𝑻 Y  = PATH p [X] ∩ 𝓕𝓑𝑬𝑻 Y`
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH_INTER_NODE]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
\\ rw [PATH_DEF]
\\ sg `X ∩ p_space p = X `
   >-( metis_tac [INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ rw [FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

(*----------------*)  
(*   PROPERTY 8   *)
(*----------------*)

val PROB_PATH_NODE_CARTESIAN= store_thm("PROB_PATH_NODE_CARTESIAN",
``!p Y X L. (prob_space p) /\
    	    (!y. MEM y (L ++ X ++ Y) ==> y IN events p)  /\  ~NULL L /\ ALL_DISTINCT X /\
            disjoint (set X) /\  ALL_DISTINCT Y /\ disjoint (set Y) /\
	    (MUTUAL_INDEP p (L ++ X ++ Y)) ==> 
	    prob p (PATH p L ∩ 𝓕𝓑𝑬𝑻 ($⊗ X Y)) =
	    prob p (PATH p L) * prob p (𝓕𝓑𝑬𝑻 X) * prob p (𝓕𝓑𝑬𝑻 Y)``,

DEP_REWRITE_TAC [LEMMA14]
\\ GEN_TAC
\\ Induct
   >-( rw [FBLOCK_ET_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [PROB_EMPTY])
\\ rw [FBLOCK_ET_DEF, ETREE_DEF, ALL_SCENARIOS_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM ALL_SCENARIOS_DEF]
\\ rw [UNION_OVER_INTER]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ rw []
   >-( metis_tac [PATH_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
   >-( metis_tac [PATH_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
   >-( metis_tac [PATH_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
\\ sg `PATH p L ∩ (ETREE (NODE (EVENT_TREE_LIST X)) ∩ h) =
       PATH p (h::L) ∩ (ETREE (NODE (EVENT_TREE_LIST X)))`
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ rw [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [PROB_PATH_INTER_NODE]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `Y`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw []
       \\ sg ` L ⧺ X ⧺ [h] ⧺ Y = L ⧺ X ⧺ h::Y`
          >-( rw [APPEND])
       \\ rw [])
\\ rw [FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `X`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `Y`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw []
       \\ sg `L ⧺ X ⧺ [h] ⧺ Y =  L ⧺ X ⧺ h::Y`
          >-( rw [APPEND])
       \\ rw [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `X ⧺ h::Y`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw []
   >-( fs [disjoint]
       \\ metis_tac [])
\\ fs [FBLOCK_ET_DEF]
\\ sg `prob p
              (PATH p L ∩
               (ETREE (NODE (EVENT_TREE_LIST X)) ∩
                ETREE (NODE (EVENT_TREE_LIST Y)))) =
            prob p (PATH p L) * prob p (ETREE (NODE (EVENT_TREE_LIST X))) *
            prob p (ETREE (NODE (EVENT_TREE_LIST Y))) `
   >-( first_x_assum (mp_tac o Q.SPECL [`X`, `L`])
       \\ rw []
       \\ sg `(∀y. (MEM y L ∨ MEM y X) ∨ MEM y Y ⇒ y ∈ events p) `
       	  >-(metis_tac [])
       \\ sg `disjoint (set Y) `
          >-(  fs [disjoint]
       	       \\ metis_tac [])
       \\ sg `MUTUAL_INDEP p (L ⧺ X ⧺ Y) `
          >-( irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `[h]`
       	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ sg `L ⧺ X ⧺ [h] ⧺ Y =  L ⧺ X ⧺ h::Y`
              	 >-( rw [APPEND])
              \\ rw [])
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw []
   >-( fs [disjoint]
       \\ metis_tac [])
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `X ⧺ h::Y`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw [])
\\ sg `h ∩ ETREE (NODE (EVENT_TREE_LIST Y)) = PATH p [h] ∩ ETREE (NODE (EVENT_TREE_LIST Y)) `
   >-( rw [PATH_DEF]
       \\ rw [INTER_COMM]
       \\ sg `h ∩ p_space p = h `
       	  >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ metis_tac [INTER_COMM])
\\ POP_ORW
\\ rw [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [PROB_PATH_INTER_NODE]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `L ⧺ X `
       \\ rw [])
\\ rw [FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `L ⧺ X `
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `Y`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw []
       \\ sg `L ⧺ X ⧺ [h] ⧺ Y =  L ⧺ X ⧺ h::Y`
          >-( rw [APPEND])
       \\ rw [])
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw []
   >-( fs [disjoint]
       \\ metis_tac [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ sg `PATH p (h::L) ∩ ETREE (NODE (EVENT_TREE_LIST X)) ∩
           (PATH p L ∩
            (ETREE (NODE (EVENT_TREE_LIST X)) ∩
             ETREE (NODE (EVENT_TREE_LIST Y)))) =
	     PATH p (h::L) ∩ ETREE (NODE (EVENT_TREE_LIST X)) ∩
             ETREE (NODE (EVENT_TREE_LIST Y))`
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ first_x_assum (mp_tac o Q.SPECL [`X`, `(h::L)`])
\\ rw []
\\ sg `(∀y. ((y = h ∨ MEM y L) ∨ MEM y X) ∨ MEM y Y ⇒ y ∈ events p) `
   >-(metis_tac [])
\\ sg `disjoint (set Y) `
   >-( fs [disjoint]
       \\ metis_tac [])
\\ sg ` MUTUAL_INDEP p (h::(L ⧺ X ⧺ Y))`
   >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg `L ⧺ X ⧺ [h] ⧺ Y =  L ⧺ X ⧺ h::Y`
          >-( rw [APPEND])
       \\ rw [])
\\ sg `prob p
          (PATH p (h::L) ∩
           (ETREE (NODE (EVENT_TREE_LIST X)) ∩
            ETREE (NODE (EVENT_TREE_LIST Y)))) =
        prob p (PATH p (h::L)) * prob p (ETREE (NODE (EVENT_TREE_LIST X))) *
        prob p (ETREE (NODE (EVENT_TREE_LIST Y))) `
   >-( metis_tac [])
\\ rw [GSYM INTER_ASSOC]
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw []
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `X ++ Y`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw [])
\\ rw [PROD_LIST_DEF, PROB_LIST_DEF]
\\ REAL_ARITH_TAC);
(*-------------------------------------------------------------------------------------------------*)

(*----------------*)  
(*   PROPERTY  9  *)
(*----------------*)

val PROB_CARTESIAN_SPLIT= store_thm("PROB_CARTESIAN_SPLIT",
``!p X Y.   (prob_space p) /\
    	    (!y. MEM y (FLAT [X;Y]) ==> y IN events p)  /\  ALL_DISTINCT X /\
            disjoint (set X) /\  ALL_DISTINCT Y /\ disjoint (set Y) /\
	    (MUTUAL_INDEP p (FLAT [X;Y])) ==> 
    	    (prob p (𝓕𝓑𝑬𝑻 ($⊗ X Y)) = prob p (𝓕𝓑𝑬𝑻 X) * prob p (𝓕𝓑𝑬𝑻 Y))``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ GEN_TAC
\\ Induct
   >-( rw [ETREE_DEF, EVENT_TREE_LIST_DEF, CARTESIAN_PRODUCT_DEF]
       \\ rw [PROB_SUM_DEF, PROB_EMPTY])
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF, CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ETREE_NODE_SPLIT]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ rw []
   >-( rw [GSYM FBLOCK_ET_DEF]
       \\ DEP_REWRITE_TAC [FB_ET_ALL_SCENARIOS_IN_EVENTS]
       \\ rw []
          >-( metis_tac [])
       \\ metis_tac [])
   >-( rw [GSYM FBLOCK_ET_DEF]
       \\ DEP_REWRITE_TAC [CARTESIAN_PRODUCT_IN_EVENTS]
       \\ fs []
       \\ metis_tac [])
   >-( metis_tac [NODE_IN_EVENTS])
\\ rw [GSYM FBLOCK_ET_DEF]   
\\ DEP_REWRITE_TAC [LEMMA13]
\\ rw [FBLOCK_ET_DEF]
\\ sg `h ∩ ETREE (NODE (EVENT_TREE_LIST Y)) = PATH p [h] ∩ ETREE (NODE (EVENT_TREE_LIST Y))`
   >-( rw [PATH_DEF]
       \\ metis_tac [INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ rw [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [PROB_PATH_INTER_NODE]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `X`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw [])
\\ rw [PATH_DEF, FBLOCK_ET_DEF]
\\ sg `h ∩ p_space p = h `
   >-( metis_tac [INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ sg ` prob p (ETREE (NODE (EVENT_TREE_LIST Y))) =  ∑𝑷𝑹𝑶𝑩 p Y`
   >-( DEP_REWRITE_TAC [PROB_NODE]
       \\ rw [])
\\ POP_ORW
\\ sg ` prob p (ETREE (NODE (EVENT_TREE_LIST X))) =  ∑𝑷𝑹𝑶𝑩 p X`
   >-( DEP_REWRITE_TAC [PROB_NODE]
       \\ rw []
       \\ fs [disjoint]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p (ETREE (NODE (EVENT_TREE_LIST ($⊗ X Y)))) =
       prob p (ETREE (NODE (EVENT_TREE_LIST X))) *
       prob p (ETREE (NODE (EVENT_TREE_LIST Y)))`
   >-(  first_x_assum (match_mp_tac)
   	\\ rw []
	   >-( metis_tac [])
	   >-( metis_tac [])
	   >-( fs [disjoint]
	       \\ metis_tac [])
	\\ irule MUTUAL_INDEP_FRONT_APPEND
	\\ Q.EXISTS_TAC `[h]`
	\\ rw [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw []
   >-( fs [disjoint]
       \\ metis_tac [])
\\ sg `h ∩ ETREE (NODE (EVENT_TREE_LIST Y)) ∩
            ETREE (NODE (EVENT_TREE_LIST ($⊗ X Y))) =
       PATH p [h] ∩ ETREE (NODE (EVENT_TREE_LIST ($⊗ X Y)))`
   >-( rw [PATH_DEF]
       \\ sg `h ∩ p_space p = h `
       	  >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [GSYM FBLOCK_ET_DEF]
       \\ DEP_REWRITE_TAC [LEMMA14]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg`h ∩ ETREE (NODE (EVENT_TREE_LIST X)) = PATH p [h] ∩ ETREE (NODE (EVENT_TREE_LIST X)) `
   >-( rw [PATH_DEF]
       \\ sg `h ∩ p_space p = h `
       	  >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ metis_tac [])
\\ POP_ORW
\\ rw [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [PROB_PATH_NODE_CARTESIAN]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [disjoint]
       \\ metis_tac [])
\\ DEP_REWRITE_TAC [PROB_PATH_INTER_NODE]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `Y`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw [])
\\ rw [FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ rw []
   >-(  fs [disjoint]
       \\ metis_tac [])
\\ rw [PATH_DEF]
\\ sg `h ∩ p_space p = h `
   >-( metis_tac [INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ REAL_ARITH_TAC);
(*-------------------------------------------------------------------------------------------------*)

val PROB_CARTESIAN_EQ_PROD_OF_SUM= store_thm("PROB_CARTESIAN_EQ_PROD_OF_SUM",
``!p X Y.   (prob_space p) /\
    	    (!y. MEM y (FLAT [X;Y]) ==> y IN events p)  /\  ALL_DISTINCT X /\
            disjoint (set X) /\  ALL_DISTINCT Y /\ disjoint (set Y) /\
	    (MUTUAL_INDEP p (FLAT [X;Y])) ==> 
    (prob p (𝓕𝓑𝑬𝑻 ($⊗ X Y)) =  ∑𝑷𝑹𝑶𝑩 p X *  ∑𝑷𝑹𝑶𝑩 p Y)``,

rw []
\\ DEP_REWRITE_TAC [PROB_CARTESIAN_SPLIT]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
\\ rw [FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [PROB_NODE]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val ALL_SCENARIOS_IN_EVENTS = store_thm("ALL_SCENARIOS_IN_EVENTS",
``!p Y X y. prob_space p /\ (∀y. y = X ∨ MEM y Y ⇒ y ∈ events p) ==>
            (MEM y (ALL_SCENARIOS X Y) ==> y ∈ events p)``,

GEN_TAC
\\ Induct
   >-( rw [ALL_SCENARIOS_DEF])
\\ rw [ALL_SCENARIOS_DEF]
   >-( metis_tac [EVENTS_INTER])
\\ fs [GSYM ALL_SCENARIOS_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`X`, `y`])
\\ rw []
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val MEM_CARTESIAN_PRODUCT_IN_EVENTS = store_thm("MEM_CARTESIAN_PRODUCT_IN_EVENTS",
``!p X Y y. prob_space p /\ (∀y. MEM y X ∨ MEM y Y ⇒ y ∈ events p) ==>
            (MEM y ($⊗ X Y) ==> y ∈ events p)``,

GEN_TAC
\\ Induct
   >-( rw [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF])
\\ rw [CARTESIAN_PRODUCT_DEF, ALL_SCENARIOS_DEF] 
\\ fs [GSYM ALL_SCENARIOS_DEF]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
   >-( metis_tac [ALL_SCENARIOS_IN_EVENTS])
\\ fs [GSYM CARTESIAN_PRODUCT_DEF]
\\ first_x_assum (mp_tac o Q.SPECL [`Y`, `y`])
\\ rw []
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val FBLOCK_IN_EVENTS = store_thm("FBLOCK_IN_EVENTS",
``!p L X y. prob_space p /\ (∀y. MEM y X ∨ MEM y (FLAT L) ⇒ y ∈ events p) ==>
            (MEM y (𝓕𝓑 (X::L)) ==> y ∈ events p)``,

GEN_TAC
\\ Induct
   >-( rw [FBLOCK_DEF])
\\ rw [FBLOCK_DEF]
\\ fs [GSYM FBLOCK_DEF]
\\ rw []
\\ DEP_REWRITE_TAC [MEM_CARTESIAN_PRODUCT_IN_EVENTS]
\\ rw []
\\ Q.EXISTS_TAC `h `
\\ Q.EXISTS_TAC `𝓕𝓑 (X::L)`
\\ rw []
   >-(metis_tac [])
\\ first_x_assum (mp_tac o Q.SPECL [`X`, `y'`])
\\ rw []
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

(*----------------*)  
(*   PROPERTY 10  *)
(*----------------*)

val PROB_FB_ET_PATH = store_thm("PROB_FB_ET_PATH",
``!p L L2 L1.
            (prob_space p) /\
    	    (!y. MEM y (FLAT (L1::L2::L)) ==> y IN events p)  /\ ~NULL L2 /\
	    (MUTUAL_INDEP p (FLAT (L1::L2::L))) ==>
  prob p (𝓕𝓑𝑬𝑻 (𝓕𝓑 (L1::L)) ∩ PATH p L2) =  prob p (𝓕𝓑𝑬𝑻 (𝓕𝓑 (L1::L))) * prob p (PATH p L2)``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ GEN_TAC
\\ Induct
   >-(  rw [FBLOCK_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
   	\\ rw [GSYM EVENT_TREE_LIST_DEF]
	\\ rw [INTER_COMM]
	\\ rw [GSYM FBLOCK_ET_DEF]
	\\ DEP_REWRITE_TAC [PROB_PATH_INTER_NODE]
	\\ rw []
	   >-( metis_tac [])
	   >-( metis_tac [])
	   >-( irule MUTUAL_INDEP_APPEND_SYM
	       \\ rw [])
        \\ REAL_ARITH_TAC)
\\ Induct_on `h`
   >-( rw [CARTESIAN_PRODUCT_DEF, FBLOCK_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [PROB_EMPTY])
\\ rw [CARTESIAN_PRODUCT_DEF, FBLOCK_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM CARTESIAN_PRODUCT_DEF]
\\ rw [GSYM FBLOCK_DEF ]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [ETREE_NODE_SPLIT, INTER_COMM, UNION_OVER_INTER]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ rw []
   >-( metis_tac [ALL_SCENARIOS_IN_EVENTS, FBLOCK_IN_EVENTS, PATH_IN_EVENTS,
                  NODE_IN_EVENTS, EVENTS_INTER])
   >-( sg `ETREE (NODE (EVENT_TREE_LIST ($⊗ h (𝓕𝓑 (L1::L))))) ∈ events p`
       >-( DEP_REWRITE_TAC [NODE_IN_EVENTS]
       	   \\ rw []
	   \\ DEP_REWRITE_TAC [MEM_CARTESIAN_PRODUCT_IN_EVENTS]
	   \\ rw []
	   \\ Q.EXISTS_TAC `h`
	   \\ Q.EXISTS_TAC `𝓕𝓑 (L1::L)`
	   \\ rw []
	      >-( metis_tac [])
           \\ metis_tac [FBLOCK_IN_EVENTS])
       \\ metis_tac [PATH_IN_EVENTS, EVENTS_INTER])
   >-( metis_tac [ALL_SCENARIOS_IN_EVENTS, FBLOCK_IN_EVENTS, PATH_IN_EVENTS,
                  NODE_IN_EVENTS, EVENTS_INTER])
   >-( DEP_REWRITE_TAC [NODE_IN_EVENTS]
       \\ rw []
       \\ DEP_REWRITE_TAC [MEM_CARTESIAN_PRODUCT_IN_EVENTS]
       \\ rw []
       \\ Q.EXISTS_TAC `h`
       \\ Q.EXISTS_TAC `𝓕𝓑 (L1::L)`
       \\ rw []
          >-( metis_tac [])
       \\ metis_tac [FBLOCK_IN_EVENTS])
\\ rw [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [LEMMA13]
\\ rw [INTER_ASSOC]
\\ fs [FBLOCK_DEF]
\\ fs [GSYM FBLOCK_DEF]
\\ sg `PATH p L2 ∩ h' = PATH p (h'::L2) `
   >-( metis_tac [PATH_DEF, INTER_COMM])
\\ POP_ORW
\\ rw [FBLOCK_ET_DEF]
\\ sg ` prob p
          (PATH p (h'::L2) ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L))))) =
        prob p (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L))))) *
        prob p (PATH p (h'::L2))`
   >-( sg `PATH p (h'::L2) ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) =
           ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ PATH p (h'::L2)`
       >-( metis_tac [INTER_COMM])
       \\ POP_ORW
       \\ ntac 5 (pop_assum mp_tac)
       \\ first_x_assum (mp_tac o Q.SPECL [`(h'::L2)`, `L1`])
       \\ rw []
       \\ sg `(∀y.
             ((MEM y L1 ∨ y = h' ∨ MEM y L2) ∨ MEM y h) ∨ MEM y (FLAT L)  ⇒ y ∈ events p)`
          >-( metis_tac [])
       \\ sg ` MUTUAL_INDEP p (L1 ⧺ h'::L2 ⧺ FLAT L)`
       	  >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
	      \\ irule MUTUAL_INDEP_FRONT_APPEND
	      \\ Q.EXISTS_TAC `h`
	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
       	      \\ sg `L1 ++ L2 ⧺ [h'] ⧺ h ⧺ FLAT L =  L1 ⧺ L2 ⧺ h'::(h ⧺ FLAT L)`
	         >-( rw [APPEND])
	      \\ rw [])
        \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       \\ irule MUTUAL_INDEP_APPEND_SYM     
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `L1`
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h ⧺ FLAT L`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw []
       \\ sg `L1 ⧺ L2 ⧺ [h'] ⧺ h ⧺ FLAT L =  L1 ⧺ L2 ⧺ h'::(h ⧺ FLAT L)`
	  >-( rw [APPEND])
       \\ rw [])
    >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `L1`
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `  h'::(h ⧺ FLAT L)`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw [])
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
\\ sg `prob p
          (PATH p L2 ∩
           ETREE (NODE (EVENT_TREE_LIST ($⊗ h (𝓕𝓑 (L1::L)))))) =
       prob p (ETREE (NODE (EVENT_TREE_LIST ($⊗ h (𝓕𝓑 (L1::L)))))) * prob p (PATH p L2)`
   >-( sg `PATH p L2 ∩
           ETREE (NODE (EVENT_TREE_LIST ($⊗ h (𝓕𝓑 (L1::L))))) =  
	   ETREE (NODE (EVENT_TREE_LIST ($⊗ h (𝓕𝓑 (L1::L))))) ∩ PATH p L2`
       >-( metis_tac [INTER_COMM])
       \\ POP_ORW
       \\ first_x_assum (mp_tac o Q.SPECL [`L2`, `L1`])
       \\ rw []
       \\ sg `(∀y.
             ((MEM y L1 ∨ MEM y L2) ∨ MEM y h) ∨ MEM y (FLAT L) ⇒ y ∈ events p) `
          >-( metis_tac [])
       \\ sg `MUTUAL_INDEP p (L1 ⧺ L2 ⧺ h ⧺ FLAT L) `
          >-( once_rewrite_tac[GSYM APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_FRONT_APPEND
	      \\ Q.EXISTS_TAC `[h']`
	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
       	      \\ sg `L1 ++ L2 ⧺ [h'] ⧺ h ⧺ FLAT L =  L1 ⧺ L2 ⧺ h'::(h ⧺ FLAT L)`
	         >-( rw [APPEND])
	      \\ rw [])
       \\ metis_tac [])
\\ POP_ORW
\\ sg ` PATH p (h'::L2) ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩
        PATH p L2 ∩ ETREE (NODE (EVENT_TREE_LIST ($⊗ h (𝓕𝓑 (L1::L))))) =
	ETREE (NODE (EVENT_TREE_LIST ($⊗ h (𝓕𝓑 (L1::L))))) ∩ PATH p (h'::L2)`
   >-( rw [GSYM FBLOCK_ET_DEF]
       \\ rw  [LEMMA14]
       \\ rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p
              (ETREE (NODE (EVENT_TREE_LIST ($⊗ h (𝓕𝓑 (L1::L))))) ∩
               PATH p (h'::L2)) =
            prob p
              (ETREE (NODE (EVENT_TREE_LIST ($⊗ h (𝓕𝓑 (L1::L)))))) *
            prob p (PATH p (h'::L2)) `
   >-( first_x_assum (mp_tac o Q.SPECL [`(h'::L2)`, `L1`])
       \\ rw []
       \\ sg `(∀y.
             ((MEM y L1 ∨ y = h' ∨ MEM y L2) ∨ MEM y h) ∨ MEM y (FLAT L) ⇒
             y ∈ events p) `
          >-(metis_tac [])
       \\ sg `MUTUAL_INDEP p (L1 ⧺ h'::L2 ⧺ h ⧺ FLAT L) `
          >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
      	      \\ sg `L1 ++ L2 ⧺ [h'] ⧺ h ⧺ FLAT L =  L1 ⧺ L2 ⧺ h'::(h ⧺ FLAT L)`
	         >-( rw [APPEND])
	      \\ rw [])	    
        \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
    >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `L1`
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `  h'::(h ⧺ FLAT L)`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw [])
   >-( metis_tac [])
   >-( metis_tac [])      
   >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       \\ irule MUTUAL_INDEP_APPEND_SYM     
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `L1`
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h ⧺ FLAT L`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw []
       \\ sg `L1 ⧺ L2 ⧺ [h'] ⧺ h ⧺ FLAT L =  L1 ⧺ L2 ⧺ h'::(h ⧺ FLAT L)`
	  >-( rw [APPEND])
       \\ rw [])
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
\\ sg `h' ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) =
       ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ PATH p [h']`
   >-( rw [PATH_DEF]
       \\ sg `h' ∩ p_space p = h' `
       	  >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ metis_tac [INTER_COMM])
\\ POP_ORW
\\ sg `prob p
              (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ PATH p [h']) =
            prob p (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L))))) *
            prob p (PATH p [h']) `
   >-( ntac 5 (pop_assum mp_tac)
       \\ first_x_assum (mp_tac o Q.SPECL [`[h']`, `L1`])
       \\ rw []
       \\ sg `(∀y. (MEM y L1 ∨ y = h') ∨ MEM y (FLAT L) ⇒ y ∈ events p) `
       	  >-( metis_tac []) 
       \\ sg `MUTUAL_INDEP p (L1 ⧺ [h'] ⧺ FLAT L) `
          >-( irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `h`
	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `L2`
	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ sg `L1 ⧺ L2 ⧺ [h'] ⧺ h ⧺ FLAT L =  L1 ⧺ L2 ⧺ h'::(h ⧺ FLAT L)`
	      	 >-( rw [APPEND])
              \\ rw [])
       \\ metis_tac [])
\\ POP_ORW
\\ rw [PATH_DEF]
\\ sg `h' ∩ p_space p = h' `
   >-( metis_tac [INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ sg `ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ h' ∩
            ETREE (NODE (EVENT_TREE_LIST ($⊗ h (𝓕𝓑 (L1::L))))) =
       ETREE (NODE (EVENT_TREE_LIST ($⊗ h (𝓕𝓑 (L1::L))))) ∩ PATH p [h']`
   >-( rw [GSYM FBLOCK_ET_DEF]
       \\ rw [LEMMA14]
       \\ rw [PATH_DEF]
       \\ sg `h' ∩ p_space p = h' `
       	  >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p
           (ETREE (NODE (EVENT_TREE_LIST ($⊗ h (𝓕𝓑 (L1::L))))) ∩
            PATH p [h']) =
       prob p
              (ETREE (NODE (EVENT_TREE_LIST ($⊗ h (𝓕𝓑 (L1::L)))))) *
            prob p (PATH p [h'])`
   >-( first_x_assum (mp_tac o Q.SPECL [`[h']`, `L1`])
       \\ rw []
       \\ sg `(∀y. ((MEM y L1 ∨ y = h') ∨ MEM y h) ∨ MEM y (FLAT L) ⇒ y ∈ events p) `
          >-(metis_tac [])
       \\ sg `MUTUAL_INDEP p (L1 ⧺ [h'] ⧺ h ⧺ FLAT L)  `
          >-( once_rewrite_tac[GSYM APPEND_ASSOC]
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `L2`
	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ sg `L1 ⧺ L2 ⧺ [h'] ⧺ h ⧺ FLAT L =  L1 ⧺ L2 ⧺ h'::(h ⧺ FLAT L)`
	      	 >-( rw [APPEND])
              \\ rw [])
       \\ metis_tac [])
\\ POP_ORW
\\ rw [PATH_DEF]
\\ sg `h' ∩ p_space p = h' `
   >-( metis_tac [INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ REAL_ARITH_TAC);
(*-------------------------------------------------------------------------------------------------*)

(*----------------*)  
(*   PROPERTY 11  *)
(*----------------*)

val PROB_FB_ET_PATH_FB_ET = store_thm("PROB_FB_ET_PATH_FB_ET",
``!p L L2 L3 L1.
            (prob_space p) /\
    	    (!y. MEM y (FLAT (L3::L2::L1::L)) ==> y IN events p)  /\ ~NULL L2 /\
	    (LIST_EVENT_OUTCOME_SPACE_CONDS (L1::L3::L)) /\
	    (MUTUAL_INDEP p (FLAT (L3::L2::L1::L))) ==>
            prob p (𝓕𝓑𝑬𝑻 (𝓕𝓑 (L1::L)) ∩ PATH p L2 ∩ 𝓕𝓑𝑬𝑻 L3) =
	    prob p (𝓕𝓑𝑬𝑻 (𝓕𝓑 (L1::L))) * prob p (PATH p L2) * prob p (𝓕𝓑𝑬𝑻 L3)``,
	    
once_rewrite_tac [FBLOCK_ET_DEF]
\\ GEN_TAC
\\ Induct
   >-(  rw [FBLOCK_DEF]
	\\ sg `ETREE (NODE (EVENT_TREE_LIST L1)) ∩ PATH p L2 ∩
               ETREE (NODE (EVENT_TREE_LIST L3)) =
	       PATH p L2 ∩ ETREE (NODE (EVENT_TREE_LIST ($⊗ L1 L3)))`
	   >-( rw [GSYM FBLOCK_ET_DEF]
	       \\ rw [LEMMA14]
	       \\ rw [INTER_ASSOC]
	       \\ rw [EXTENSION]
	       \\ metis_tac [])
	\\ POP_ORW
	\\ fs [LIST_EVENT_OUTCOME_SPACE_CONDS_DEF]
	\\ rw [GSYM FBLOCK_ET_DEF]
	\\ DEP_REWRITE_TAC [PROB_PATH_NODE_CARTESIAN]
	\\ rw []
	   >-( metis_tac [])
	   >-( metis_tac [])
	   >-( metis_tac [])
	   >-( irule MUTUAL_INDEP_APPEND_SYM
	       \\ rw [])
        \\ disj2_tac
	\\ REAL_ARITH_TAC)
\\ Induct_on `h`
   >-( rw [FBLOCK_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [GSYM EVENT_TREE_LIST_DEF]
       \\ rw [GSYM FBLOCK_DEF]
       \\ rw [GSYM FBLOCK_ET_DEF]
       \\ rw [LEMMA14]
       \\ rw [ETREE_DEF, FBLOCK_ET_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [PROB_EMPTY])
\\ rw [FBLOCK_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM FBLOCK_DEF]
\\ fs [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [LEMMA14]
\\ fs [FBLOCK_ET_DEF]
\\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [INTER_COMM]
\\ rw [INTER_ASSOC]
\\ rw [UNION_OVER_INTER]
\\ rw [INTER_COMM]
\\ rw [UNION_OVER_INTER]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ rw []
   >-( metis_tac [FBLOCK_IN_EVENTS, PATH_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
   >-( metis_tac [FBLOCK_IN_EVENTS, PATH_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
\\ rw [INTER_ASSOC]
\\ sg `ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ h' ∩ PATH p L2 ∩
       ETREE (NODE (EVENT_TREE_LIST L3))  =
       ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ PATH p (h'::L2) ∩
       ETREE (NODE (EVENT_TREE_LIST L3))`
   >-( rw [PATH_DEF]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p
          (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ PATH p (h'::L2) ∩
           ETREE (NODE (EVENT_TREE_LIST L3))) =
       prob p (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L))))) *
       prob p (PATH p (h'::L2)) * prob p (ETREE (NODE (EVENT_TREE_LIST L3)))`
   >-( ntac 6 (pop_assum mp_tac)
       \\ first_x_assum (mp_tac o Q.SPECL [`(h'::L2)`, `L3`, `L1`])
       \\ rw []
       \\ sg `(∀y.
             MEM y L3 ∨ y = h' ∨ (MEM y L2 ∨ MEM y L1) ∨ MEM y (FLAT L) ⇒
             y ∈ events p)`
       	  >-( metis_tac [])
       \\ sg ` Ω𝑳⊨ (L1::L3::L) `
       	  >-( fs [LIST_EVENT_OUTCOME_SPACE_CONDS_DEF])
       \\ sg `MUTUAL_INDEP p (L3 ⧺ h'::(L2 ⧺ L1 ⧺ FLAT L))`
       	  >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
	      \\ Q.ABBREV_TAC `X = L3 ⧺ (L2 ⧺ L1) ⧺ [h']`
	      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `h`
	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ Q.UNABBREV_TAC`X`
       	      \\ sg `L3 ⧺ L2 ⧺ L1 ⧺ [h'] ⧺ h ⧺ FLAT L =  L3 ⧺ L2 ⧺ L1 ⧺ h'::(h ⧺ FLAT L)`
	         >-( rw [APPEND])
	      \\ rw [])
	\\ sg `MUTUAL_INDEP p (L3 ⧺ h'::L2 ⧺ L1 ⧺ FLAT L)  `
           >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
	       \\ once_rewrite_tac[APPEND_ASSOC]
	       \\ sg `L3 ⧺ [h'] ⧺ L2 ⧺ L1 ⧺ FLAT L =  L3 ⧺ h'::(L2 ⧺ L1 ⧺ FLAT L)`
	          >-(rw [APPEND] )
               \\ rw [])
        \\ metis_tac [])
\\ POP_ORW
\\ sg `ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩
           ETREE (NODE (EVENT_TREE_LIST h)) ∩ PATH p L2 ∩
           ETREE (NODE (EVENT_TREE_LIST L3))  =
           ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::h::L)))) ∩ PATH p L2 ∩
           ETREE (NODE (EVENT_TREE_LIST L3)) `
   >-( rw [FBLOCK_DEF]
       \\ rw [GSYM FBLOCK_DEF]
       \\ rw [GSYM FBLOCK_ET_DEF]
       \\ rw [LEMMA14]
       \\ rw [EXTENSION]
       \\ metis_tac [FBLOCK_DEF])
\\ POP_ORW
\\ sg ` prob p
              (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::h::L)))) ∩
               PATH p L2 ∩ ETREE (NODE (EVENT_TREE_LIST L3))) =
            prob p (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::(h::L)))))) *
            prob p (PATH p L2) * prob p (ETREE (NODE (EVENT_TREE_LIST L3))) `
   >-( first_x_assum (mp_tac o Q.SPECL [`L2`, `L3`, `L1`])
       \\ rw []
       \\ fs [FBLOCK_DEF]
       \\ rw [GSYM FBLOCK_ET_DEF]
       \\ fs [LEMMA14]
       \\ fs [GSYM FBLOCK_DEF]
       \\ sg `(∀y.
             (((MEM y L3 ∨ MEM y L2) ∨ MEM y L1) ∨ MEM y h) ∨ MEM y (FLAT L) ⇒
             y ∈ events p) `
          >-( metis_tac [])
       \\ sg `Ω𝑳⊨ (L1::L3::h::L) `
          >-( fs [LIST_EVENT_OUTCOME_SPACE_CONDS_DEF]
       	      \\ fs [disjoint]
       	      \\ metis_tac [])
       \\ sg `MUTUAL_INDEP p (L3 ⧺ L2 ⧺ L1 ⧺ h ⧺ FLAT L)  `
       	  >-( once_rewrite_tac[GSYM APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `[h']`
       	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
       	      \\ rw []
       	      \\ sg `L3 ⧺ L2 ⧺ L1 ⧺ [h'] ⧺ h ⧺ FLAT L =  L3 ⧺ L2 ⧺ L1 ⧺ h'::(h ⧺ FLAT L)`
	      	 >-( rw [APPEND])
              \\ rw [])
       \\ fs[GSYM FBLOCK_ET_DEF]
       \\ fs [LEMMA14]
       \\ metis_tac [])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       \\ irule MUTUAL_INDEP_APPEND_SYM     
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `L3`
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h ⧺ FLAT L`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw []
       \\ sg `L3 ⧺ L2 ⧺ L1 ⧺ [h'] ⧺ h ⧺ FLAT L =  L3 ⧺ L2 ⧺ L1 ⧺ h'::(h ⧺ FLAT L)`
	  >-( rw [APPEND])
       \\ rw [])
    >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `L3`
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC ` L1 ⧺ h'::(h ⧺ FLAT L)`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw [])
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
\\ sg `ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ PATH p (h'::L2) ∩
           ETREE (NODE (EVENT_TREE_LIST L3)) ∩
           ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩
           ETREE (NODE (EVENT_TREE_LIST h)) ∩ PATH p L2 ∩
           ETREE (NODE (EVENT_TREE_LIST L3)) =
       	   ETREE (NODE (EVENT_TREE_LIST h)) ∩
           ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ PATH p (h'::L2) ∩
           ETREE (NODE (EVENT_TREE_LIST L3))`
   >-( rw [PATH_DEF]
       \\ rw [INTER_ASSOC]
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p
          (ETREE (NODE (EVENT_TREE_LIST h)) ∩
           ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ PATH p (h'::L2) ∩
           ETREE (NODE (EVENT_TREE_LIST L3))) =
      prob p
              (ETREE (NODE (EVENT_TREE_LIST h)) ∩
               ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L))))) *
            prob p (PATH p (h'::L2)) * prob p (ETREE (NODE (EVENT_TREE_LIST L3))) `
    >-( first_x_assum (mp_tac o Q.SPECL [`(h'::L2)`, `L3`, `L1`])
       \\ rw []
       \\ sg `(∀y.
             (((MEM y L3 ∨ y = h' ∨ MEM y L2) ∨ MEM y L1) ∨ MEM y h) ∨
             MEM y (FLAT L) ⇒
             y ∈ events p)`
          >-(metis_tac [])
       \\ sg `Ω𝑳⊨ (L1::L3::h::L) `
          >-( fs [LIST_EVENT_OUTCOME_SPACE_CONDS_DEF]
	      \\ fs [disjoint]
	      \\ metis_tac [])
       \\ sg `MUTUAL_INDEP p (L3 ⧺ h'::L2 ⧺ L1 ⧺ h ⧺ FLAT L)  `
          >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ once_rewrite_tac [GSYM APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ once_rewrite_tac[APPEND_ASSOC]
	      \\ once_rewrite_tac [GSYM APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
	      \\ once_rewrite_tac [GSYM APPEND_ASSOC]
	      \\ once_rewrite_tac [GSYM APPEND_ASSOC]
	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
      	      \\ sg `L3 ⧺ L2 ⧺ L1 ⧺ [h'] ⧺ h ⧺ FLAT L =  L3 ⧺ L2 ⧺ L1 ⧺ h'::(h ⧺ FLAT L)`
	       	  >-( rw [APPEND])
              \\ rw [])
	\\ fs [GSYM FBLOCK_ET_DEF]
	\\ fs [LEMMA14]
	\\ fs [FBLOCK_DEF]
	\\ fs [LEMMA14]
	\\ fs [GSYM FBLOCK_DEF]
        \\ metis_tac [])
\\ fs [FBLOCK_ET_DEF]
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_PATH]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       \\ irule MUTUAL_INDEP_APPEND_SYM     
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `L1`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `L3`
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h ⧺ FLAT L`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw []
       \\ sg `L3 ⧺ L2 ⧺ L1 ⧺ [h'] ⧺ h ⧺ FLAT L =  L3 ⧺ L2 ⧺ L1 ⧺ h'::(h ⧺ FLAT L)`
	  >-( rw [APPEND])
       \\ rw [])
\\ rw [PROB_LIST_DEF, PROD_LIST_DEF]
\\ sg `(h' ∪ ETREE (NODE (EVENT_TREE_LIST h))) ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) =
        ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L))))  ∩ (h' ∪ ETREE (NODE (EVENT_TREE_LIST h)))`
   >-(metis_tac [INTER_COMM])
\\ POP_ORW
\\ rw [UNION_OVER_INTER]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ rw []
   >-(metis_tac [FBLOCK_IN_EVENTS, PATH_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
   >-(metis_tac [FBLOCK_IN_EVENTS, PATH_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
\\ sg `ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ h' ∩
            (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩
             ETREE (NODE (EVENT_TREE_LIST h))) =
       ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ PATH p [h'] ∩
       ETREE (NODE (EVENT_TREE_LIST h))`
   >-( rw [PATH_DEF]
       \\ sg `h' ∩ p_space p = h' `
       	  >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ sg `prob p
          (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ PATH p [h'] ∩
           ETREE (NODE (EVENT_TREE_LIST h))) =
        prob p (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L))))) *
        prob p (PATH p [h']) * prob p (ETREE (NODE (EVENT_TREE_LIST h))) `
   >-( ntac 6 (pop_assum mp_tac)
       \\ first_x_assum (mp_tac o Q.SPECL [`[h']`, `h`, `L1`])
       \\ rw []
       \\ sg `(∀y. ((MEM y h ∨ y = h') ∨ MEM y L1) ∨ MEM y (FLAT L) ⇒ y ∈ events p) `
       	  >-(metis_tac [])
       \\ sg `Ω𝑳⊨ (L1::h::L)`
       	  >-( fs [LIST_EVENT_OUTCOME_SPACE_CONDS_DEF]
       	      \\ fs [disjoint]
       	      \\ metis_tac [])
       \\ sg ` MUTUAL_INDEP p (h ⧺ [h'] ⧺ L1 ⧺ FLAT L) `
       	  >-( once_rewrite_tac[GSYM APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
       	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
       	      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `L3 ++ L2`
       	      \\ rw []
       	      \\ sg `L3 ⧺ L2 ⧺ L1 ⧺ [h'] ⧺ h ⧺ FLAT L =  L3 ⧺ L2 ⧺ L1 ⧺ h'::(h ⧺ FLAT L)`
	      	 >-( rw [APPEND])
              \\ rw [])
       \\ metis_tac [])
\\ POP_ORW
\\ rw [PATH_DEF]
\\ sg `h' ∩ p_space p = h' `
   >-( metis_tac [INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ sg `ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ h' =
       ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ PATH p [h']`
   >-( rw [PATH_DEF]
       \\  sg `h' ∩ p_space p = h' `
       	   >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [])
\\ POP_ORW
\\ rw [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [PROB_FB_ET_PATH]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])
   >-(metis_tac [])
   >-(  once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `L3 ⧺ L2`
       \\ rw []
       \\ sg `L3 ⧺ L2 ⧺ L1 ⧺ [h'] ⧺ h ⧺ FLAT L =  L3 ⧺ L2 ⧺ L1 ⧺ h'::(h ⧺ FLAT L)`
	  >-( rw [APPEND])
       \\ rw [])
\\ rw [PATH_DEF]
\\ sg `h' ∩ p_space p = h' `
   >-( metis_tac [INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ rw [INTER_COMM]
\\ ntac 5 (pop_assum mp_tac)
\\ POP_ORW
\\ rw [FBLOCK_ET_DEF]
\\ sg `ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::h::L)))) =
       ETREE (NODE (EVENT_TREE_LIST h)) ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L))))`
   >-( rw [FBLOCK_DEF]
       \\ rw [GSYM FBLOCK_ET_DEF]
       \\ rw [LEMMA14])
\\ POP_ORW
\\ sg `prob p (ETREE (NODE (EVENT_TREE_LIST h)) ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L))))) =
       prob p (ETREE (NODE (EVENT_TREE_LIST h))) * prob p (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))))`
   >-( Induct_on `h`
       >-(  rw [FBLOCK_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
       	    \\ rw [PROB_EMPTY])
       \\ rw [ETREE_DEF, EVENT_TREE_LIST_DEF]
       \\ rw [GSYM EVENT_TREE_LIST_DEF]
       \\ sg `(h'' ∪ ETREE (NODE (EVENT_TREE_LIST h))) ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) =
              ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ (h'' ∪ ETREE (NODE (EVENT_TREE_LIST h)))`
	  >-(metis_tac [INTER_COMM])
       \\ POP_ORW
       \\ rw [UNION_OVER_INTER]
       \\ sg `(∀y.
             ((MEM y L3 ∨ MEM y L2) ∨ MEM y L1) ∨ y = h' ∨ MEM y h ∨
             MEM y (FLAT L) ⇒
             y ∈ events p) `
          >-( metis_tac [])
       \\ sg `Ω𝑳⊨ (L1::L3::(h'::h)::L) `
          >-( fs [LIST_EVENT_OUTCOME_SPACE_CONDS_DEF]
	      \\ fs [disjoint]
	      \\ metis_tac [])
       \\ sg `MUTUAL_INDEP p (L3 ⧺ L2 ⧺ L1 ⧺ h'::(h ⧺ FLAT L)) `
          >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `[h'']`
       	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      \\ irule MUTUAL_INDEP_APPEND1
	      \\ rw []
	      \\ sg `L3 ⧺ L2 ⧺ L1 ⧺ [h'] ⧺ [h''] ⧺ h ⧺ FLAT L =  L3 ⧺ L2 ⧺ L1 ⧺ h'::h''::(h ⧺ FLAT L)`
	      	 >-( rw [APPEND])
              \\ rw [])
        \\ DEP_REWRITE_TAC [PROB_A_UNION_B]
	\\ rw []
	   >-(metis_tac [FBLOCK_IN_EVENTS, PATH_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
	   >-(metis_tac [FBLOCK_IN_EVENTS, PATH_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
	   >-(metis_tac [FBLOCK_IN_EVENTS, PATH_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])   
	\\ sg `prob p
           (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ ETREE (NODE (EVENT_TREE_LIST h)))  =
            prob p (ETREE (NODE (EVENT_TREE_LIST h))) * prob p (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))))`
           >-( rw [INTER_COMM]
	       \\ metis_tac [FBLOCK_IN_EVENTS, PATH_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
	\\ POP_ORW
	\\ rw [INTER_COMM]
	\\ sg `prob p (h'' ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L))))) =
	       prob p h'' * prob p ( ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))))`
           >-( sg `h'' ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) =
	           ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ PATH p [h''] `
               >-( rw [PATH_DEF]
	       	   \\ sg `h'' ∩ p_space p = h''`
   		      >-( metis_tac [INTER_COMM, INTER_PSPACE])
                   \\ POP_ORW
		   \\ metis_tac [INTER_COMM])
               \\ POP_ORW
	       \\ rw [GSYM FBLOCK_ET_DEF]
	       \\ DEP_REWRITE_TAC [PROB_FB_ET_PATH]
	       \\ rw []
	       	  >-( metis_tac [])
		  >-( metis_tac [])
		  >-( metis_tac [])
		  >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
		      \\ once_rewrite_tac[APPEND_ASSOC]
		      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      	      \\ Q.EXISTS_TAC `h`
       	      	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      	      \\ irule MUTUAL_INDEP_APPEND1
		      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
		      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
		      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      	      \\ Q.EXISTS_TAC `[h']`
       	      	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      	      \\ irule MUTUAL_INDEP_APPEND1
		      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      	      \\ Q.EXISTS_TAC `L3 ⧺ L2`
		      \\ rw []
		      \\ sg `L3 ⧺ L2 ⧺ L1 ⧺ [h'] ⧺ [h''] ⧺ h ⧺ FLAT L =
		              L3 ⧺ L2 ⧺ L1 ⧺ h'::h''::(h ⧺ FLAT L)`
	      	          >-( rw [APPEND])
                      \\ rw [])
                \\ rw [PATH_DEF]
		\\ sg `h'' ∩ p_space p = h'' `
   		   >-( metis_tac [INTER_COMM, INTER_PSPACE])
                \\ POP_ORW
		\\ REAL_ARITH_TAC)
	\\ POP_ORW
	\\ sg `h'' ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩
              (ETREE (NODE (EVENT_TREE_LIST h)) ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L))))) =
	      ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ PATH p [h''] ∩
              ETREE (NODE (EVENT_TREE_LIST h))`
           >-( rw [PATH_DEF]
	       \\ sg `h'' ∩ p_space p = h'' `
   	       	  >-( metis_tac [INTER_COMM, INTER_PSPACE])
               \\ POP_ORW
	       \\ rw [EXTENSION]
	       \\ metis_tac [])
	\\ POP_ORW
	\\ first_x_assum (mp_tac o Q.SPECL [`[h'']`, `h`, `L1`])
        \\ rw []
	\\ sg `(∀y. ((MEM y h ∨ y = h'') ∨ MEM y L1) ∨ MEM y (FLAT L) ⇒ y ∈ events p) `
           >-(metis_tac [])
        \\ sg ` Ω𝑳⊨ (L1::h::L) `
          >-( fs [LIST_EVENT_OUTCOME_SPACE_CONDS_DEF]
	      \\ fs [disjoint]
	      \\ metis_tac [])
        \\ sg `MUTUAL_INDEP p (h ⧺ [h''] ⧺ L1 ⧺ FLAT L) `
	   >-( irule MUTUAL_INDEP_APPEND1
	       \\ once_rewrite_tac[APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ once_rewrite_tac[APPEND_ASSOC]
	       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ once_rewrite_tac[GSYM APPEND_ASSOC]
	       \\ irule MUTUAL_INDEP_FRONT_APPEND
       	       \\ Q.EXISTS_TAC `[h']`
       	       \\ once_rewrite_tac[APPEND_ASSOC]
       	       \\ irule MUTUAL_INDEP_APPEND1
	       \\ irule MUTUAL_INDEP_FRONT_APPEND
	       \\ Q.EXISTS_TAC `L3 ⧺ L2`
	       \\ rw []
	       \\ sg `L3 ⧺ L2 ⧺ L1 ⧺ [h'] ⧺ [h''] ⧺ h ⧺ FLAT L =
		      L3 ⧺ L2 ⧺ L1 ⧺ h'::h''::(h ⧺ FLAT L)`
	          >-( rw [APPEND])
               \\ rw [])
         \\ sg ` prob p
                 (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L)))) ∩ PATH p [h''] ∩
           	 ETREE (NODE (EVENT_TREE_LIST h))) =
           	 prob p (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (L1::L))))) *
           	 prob p (PATH p [h'']) * prob p (ETREE (NODE (EVENT_TREE_LIST h))) `
             >-(metis_tac [])
	\\ POP_ORW
	\\ rw [PATH_DEF]
	\\ sg `h'' ∩ p_space p = h'' `
   	    >-( metis_tac [INTER_COMM, INTER_PSPACE])
        \\ POP_ORW
	\\ sg `h'' ∩ ETREE (NODE (EVENT_TREE_LIST h)) =
	       PATH p [h''] ∩ ETREE (NODE (EVENT_TREE_LIST h))`
	   >-( rw [PATH_DEF]
	       \\ sg `h'' ∩ p_space p = h'' `
   	       	  >-( metis_tac [INTER_COMM, INTER_PSPACE])
               \\ POP_ORW
	       \\ rw [EXTENSION]
	       \\ metis_tac [])
	\\ POP_ORW
	\\ rw [GSYM FBLOCK_ET_DEF]
	\\ DEP_REWRITE_TAC [PROB_PATH_INTER_NODE]
	\\ rw []
           >-(metis_tac [])
	   >-(metis_tac [])
	   >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
	       \\ irule MUTUAL_INDEP_APPEND_SYM
	       \\ irule MUTUAL_INDEP_FRONT_APPEND
       	       \\ Q.EXISTS_TAC `L1 ⧺ FLAT L`
       	       \\ irule MUTUAL_INDEP_APPEND_SYM
       	       \\ rw [])
        \\ rw [PATH_DEF]
	\\ sg `h'' ∩ p_space p = h'' `
   	    >-( metis_tac [INTER_COMM, INTER_PSPACE])
        \\ POP_ORW
	\\ REAL_ARITH_TAC)
\\ POP_ORW
\\ REAL_ARITH_TAC);
(*-------------------------------------------------------------------------------------------------*)

(*----------------*)  
(*   PROPERTY 12  *)
(*----------------*)

val PROB_ADD_FB_ET_TO_EXIST_FB_ET_FB = store_thm("PROB_ADD_FB_ET_TO_EXIST_FB_ET_FB",
``!p Y X L. (prob_space p) /\
    	    (!y. MEM y (FLAT (Y::X::L)) ==> y IN events p)  /\ Ω𝑳⊨ (X::Y::L) /\
	    (MUTUAL_INDEP p (FLAT (Y::X::L))) ==>
            prob p ((𝓕𝓑𝑬𝑻 Y) ∩ 𝓕𝓑𝑬𝑻 (𝓕𝓑 (X::L))) =
	    prob p (𝓕𝓑𝑬𝑻 Y) * prob p (𝓕𝓑𝑬𝑻 (𝓕𝓑 (X::L)))``, 	     

once_rewrite_tac [FBLOCK_ET_DEF]
\\ GEN_TAC
\\ Induct
   >-(  rw [FBLOCK_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
   	\\ rw [PROB_EMPTY])
\\ rw [FBLOCK_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ sg `(h ∪ ETREE (NODE (EVENT_TREE_LIST Y))) ∩
           ETREE (NODE (EVENT_TREE_LIST (FOLDR (λa b. $⊗ a b) X L))) =
       ETREE (NODE (EVENT_TREE_LIST (FOLDR (λa b. $⊗ a b) X L)))  ∩
       (h ∪ ETREE (NODE (EVENT_TREE_LIST Y)))`
   >-( metis_tac [INTER_COMM])         
\\ POP_ORW
\\ rw [GSYM FBLOCK_DEF]
\\ rw [UNION_OVER_INTER]
\\ DEP_REWRITE_TAC [PROB_A_UNION_B]
\\ rw []
   >-( rw [GSYM FBLOCK_DEF]
       \\ metis_tac [FBLOCK_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
   >-( rw [GSYM FBLOCK_DEF]
       \\ metis_tac [FBLOCK_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
   >-( metis_tac [FBLOCK_IN_EVENTS, NODE_IN_EVENTS, EVENTS_INTER])
\\ sg `h ∩ ETREE (NODE (EVENT_TREE_LIST Y)) = PATH p [h] ∩ ETREE (NODE (EVENT_TREE_LIST Y))`
   >-( rw [PATH_DEF]
       \\ rw [INTER_COMM]
       \\ sg `h ∩ p_space p = h `
          >-( metis_tac [INTER_COMM, INTER_PSPACE])
       \\ POP_ORW
       \\ rw [EXTENSION]
       \\ metis_tac [])
\\ POP_ORW
\\ rw [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [PROB_PATH_INTER_NODE]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `X ⧺ FLAT L`
       \\ irule MUTUAL_INDEP_APPEND_SYM
       \\ rw [])  
\\ rw [PATH_DEF]
\\ sg `h ∩ p_space p = h `
   >-( metis_tac [INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ rw [FBLOCK_ET_DEF]
\\ sg `prob p
          (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (X::L)))) ∩
           ETREE (NODE (EVENT_TREE_LIST Y))) =
       prob p (ETREE (NODE (EVENT_TREE_LIST Y))) *
       prob p (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (X::L)))))` 
   >-( rw [INTER_COMM]
       \\ first_x_assum (mp_tac o Q.SPECL [`X`, `L`])
       \\ rw []
       \\ sg `(∀y. (MEM y Y ∨ MEM y X) ∨ MEM y (FLAT L) ⇒ y ∈ events p) `
          >-( metis_tac [])
       \\ sg `MUTUAL_INDEP p (Y ⧺ X ⧺ FLAT L) `
          >-( irule MUTUAL_INDEP_FRONT_APPEND
       	      \\ Q.EXISTS_TAC `[h]`
       	      \\ rw [])
       \\ sg `Ω𝑳⊨ (X::Y::L) `
          >-( fs [LIST_EVENT_OUTCOME_SPACE_CONDS_DEF]
	      \\ fs [disjoint]
	      \\ metis_tac [])
       \\ metis_tac [])
\\ POP_ORW
\\ rw [INTER_COMM]
\\ sg `prob p (h ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (X::L))))) =
	       prob p h * prob p ( ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (X::L)))))`
           >-( sg `h ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (X::L)))) =
	           ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (X::L)))) ∩ PATH p [h] `
               >-( rw [PATH_DEF]
	       	   \\ sg `h ∩ p_space p = h`
   		      >-( metis_tac [INTER_COMM, INTER_PSPACE])
                   \\ POP_ORW
		   \\ metis_tac [INTER_COMM])
               \\ POP_ORW
	       \\ rw [GSYM FBLOCK_ET_DEF]
	       \\ DEP_REWRITE_TAC [PROB_FB_ET_PATH]
	       \\ rw []
	       	  >-( metis_tac [])
		  >-( metis_tac [])
		  >-( metis_tac [])
		  >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
		      \\ once_rewrite_tac[APPEND_ASSOC]
		      \\ irule MUTUAL_INDEP_APPEND1
		      \\ once_rewrite_tac[GSYM APPEND_ASSOC]
		      \\ irule MUTUAL_INDEP_FRONT_APPEND
       	      	      \\ Q.EXISTS_TAC `Y`
       	      	      \\ once_rewrite_tac[APPEND_ASSOC]
       	      	      \\ irule MUTUAL_INDEP_APPEND1
		      \\ sg `[h] ⧺ Y ⧺ (X ⧺ FLAT L) = h::(Y ⧺ X ⧺ FLAT L)`
	      	          >-( rw [APPEND])
                      \\ rw [])
                \\ rw [PATH_DEF]
		\\ sg `h ∩ p_space p = h `
   		   >-( metis_tac [INTER_COMM, INTER_PSPACE])
                \\ POP_ORW
		\\ REAL_ARITH_TAC)
\\ POP_ORW
\\ sg `h ∩ ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (X::L)))) ∩
           (ETREE (NODE (EVENT_TREE_LIST Y)) ∩
            ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (X::L))))) =
       ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (X::L))))  ∩ PATH p [h]  ∩
       (ETREE (NODE (EVENT_TREE_LIST Y))) `
   >-(  rw [PATH_DEF]
	\\ sg `h ∩ p_space p = h`
   	   >-( metis_tac [INTER_COMM, INTER_PSPACE])
        \\ POP_ORW
	\\ rw [EXTENSION]
	\\ metis_tac [])
\\ POP_ORW
\\ fs [LIST_EVENT_OUTCOME_SPACE_CONDS_DEF]
\\ rw [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [PROB_FB_ET_PATH_FB_ET]
\\ rw []
   >-(metis_tac [])
   >-(metis_tac [])	
   >-(metis_tac [])
   >-(metis_tac [])
   >-( fs [LIST_EVENT_OUTCOME_SPACE_CONDS_DEF]
       \\ fs [disjoint]
       \\ metis_tac [])
   >-( once_rewrite_tac[(prove(``!a b c. b::c = [b]++c``,rw[]))]
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ sg `([h] ⧺ Y ⧺ (X ⧺ FLAT L)) = h::(Y ⧺ X ⧺ FLAT L)`
	   >-( rw [APPEND])
       \\ rw [])
\\ rw [PATH_DEF]
\\ sg `h ∩ p_space p = h `
   >-( metis_tac [INTER_COMM, INTER_PSPACE])
\\ POP_ORW
\\ REAL_ARITH_TAC);
(*-------------------------------------------------------------------------------------------------*)

val FB_ETN_IN_EVENTS = store_thm("FB_ETN_IN_EVENTS",
``!p L1 L. (prob_space p) /\ (!y. MEM y (FLAT (L1::L)) ==> y IN events p) ==>
               (!x'. MEM x' (𝓕𝓑𝑬𝑻Ν (L1::L)) ==> x' ∈ events p)``,

rw []
\\ Induct_on `L`
   >-( rw [FBLOCK_ET_LIST_DEF]
       \\ rw [FBLOCK_ET_DEF]
       \\ metis_tac [NODE_IN_EVENTS])
\\ rw [FBLOCK_ET_LIST_DEF]
   >-(metis_tac [FBLOCK_ET_DEF, NODE_IN_EVENTS])
   >-(metis_tac [FBLOCK_ET_DEF, NODE_IN_EVENTS])
\\ fs [FBLOCK_ET_LIST_DEF]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

val FBLOCK_SPLIT  = store_thm("FBLOCK_SPLIT",
``! p L X Y. ET_PATH p [(𝓕𝓑𝑬𝑻 X); 𝓕𝓑𝑬𝑻 (𝓕𝓑 (Y::L))] = 𝓕𝓑𝑬𝑻 (𝓕𝓑 (Y::X::L))``,

rw [ET_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF, FBLOCK_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ rw [GSYM FBLOCK_DEF]
\\ Induct_on `L`
   >-( rw [FBLOCK_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
       \\ rw [FBLOCK_DEF]
       \\ rw [GSYM EVENT_TREE_LIST_DEF]
       \\ metis_tac [LEMMA14, INTER_COMM])
\\ rw [FBLOCK_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
\\ rw [GSYM FBLOCK_DEF]
\\ DEP_REWRITE_TAC [LEMMA14]);
(*-------------------------------------------------------------------------------------------------*)

(*----------------*)  
(*   PROPERTY 13  *)
(*----------------*)

val FBLOCK_EQ_ET_PATH_OF_FBLOCK_LIST = store_thm("FBLOCK_EQ_ET_PATH_OF_FBLOCK_LIST",
``!p L L1.  (prob_space p) /\
    	    (!y. MEM y (FLAT (L1::L)) ==> y IN events p) ==>
	    𝓕𝓑𝑬𝑻 (𝓕𝓑 (L1::L)) = ET_PATH p (𝓕𝓑𝑬𝑻Ν (L1::L))``,

rw [ET_PATH_EQ_PATH]
\\ DEP_REWRITE_TAC [ET_PATH_EQ_PATH]
\\ rw []
   >-( DEP_REWRITE_TAC [FB_ETN_IN_EVENTS]
       \\ rw []
       \\ Q.EXISTS_TAC `L1`
       \\ Q.EXISTS_TAC `L`
       \\ rw []
          >-(metis_tac [FBLOCK_ET_LIST_DEF])
       \\ metis_tac [FBLOCK_ET_LIST_DEF])
\\ Induct_on `L`
   >-( rw [FBLOCK_ET_LIST_DEF, FBLOCK_DEF]
       \\ rw [FBLOCK_DEF]
       \\ rw [PATH_DEF, FBLOCK_ET_DEF]
       \\ sg `ETREE (NODE (EVENT_TREE_LIST L1)) ∩ p_space p =  ETREE (NODE (EVENT_TREE_LIST L1))`
          >-( rw [NODE_IN_EVENTS, INTER_PSPACE, INTER_COMM])
       \\ POP_ORW
       \\ metis_tac [])
\\ rw [FBLOCK_ET_LIST_DEF, FBLOCK_DEF]
\\ rw [FBLOCK_DEF]
\\ rw [PATH_DEF]
\\ rw [GSYM FBLOCK_DEF]
\\ rw [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [LEMMA14]
\\ rw [GSYM FBLOCK_DEF]
\\ sg `FBLOCK_ET (FBLOCK (L1::L)) = PATH p (FBLOCK_ET_LIST (L1::L)) `
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-(metis_tac [])
       \\ metis_tac [])
\\ fs [FBLOCK_ET_DEF]
\\ POP_ORW
\\ rw [FBLOCK_ET_LIST_DEF]
\\ rw [PATH_DEF, FBLOCK_ET_DEF]
\\ rw [EXTENSION]
\\ metis_tac []);
(*-------------------------------------------------------------------------------------------------*)

(*----------------*)  
(*   PROPERTY 14  *)
(*----------------*)

val PROB_FBLOCK = store_thm("PROB_FBLOCK",
``!p L X.   (prob_space p) /\
    	    (!y. MEM y (FLAT (X::L)) ==> y IN events p)  /\
            (LIST_EVENT_OUTCOME_SPACE_CONDS (X::L)) /\
	    (MUTUAL_INDEP p (FLAT (X::L))) ==> 
    	    (prob p (𝓕𝓑𝑬𝑻 (𝓕𝓑 (X::L))) = ∏ (∑𝟚𝗗𝑷𝑹𝑶𝑩 p (X::L)))``,

once_rewrite_tac [FBLOCK_ET_DEF]
\\ GEN_TAC
\\ Induct
   >-( rw [FBLOCK_ET_DEF, FBLOCK_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF, FBLOCK_DEF]
       \\ rw [FOLDR, CARTESIAN_PRODUCT_DEF]
       \\ rw [PROB_SUM_LIST_DEF, PROD_LIST_DEF]
       \\ rw [GSYM EVENT_TREE_LIST_DEF]
       \\ fs [LIST_EVENT_OUTCOME_SPACE_CONDS_DEF]
       \\ DEP_REWRITE_TAC [PROB_NODE]
       \\ metis_tac [])
\\ rw [FBLOCK_ET_DEF, FBLOCK_DEF, ETREE_DEF, EVENT_TREE_LIST_DEF, FBLOCK_DEF]
\\ rw [PROB_SUM_LIST_DEF, PROD_LIST_DEF]
\\ rw [GSYM EVENT_TREE_LIST_DEF]
\\ fs [LIST_EVENT_OUTCOME_SPACE_CONDS_DEF]
\\ fs [GSYM FBLOCK_DEF]
\\ fs [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC[LEMMA14]
\\ fs [GSYM FBLOCK_DEF]
\\ rw [GSYM FBLOCK_ET_DEF]
\\ DEP_REWRITE_TAC [PROB_ADD_FB_ET_TO_EXIST_FB_ET_FB]
\\ rw []
   >-( metis_tac [])
   >-( metis_tac [])
   >-( metis_tac [])
   >-( fs [LIST_EVENT_OUTCOME_SPACE_CONDS_DEF]
       \\ fs [disjoint]
       \\ metis_tac [])
   >-( irule MUTUAL_INDEP_APPEND1
       \\ rw [])
\\ rw [FBLOCK_ET_DEF]
\\ sg `prob p (ETREE (NODE (EVENT_TREE_LIST h))) = ∑𝑷𝑹𝑶𝑩 p h `
   >-( DEP_REWRITE_TAC [PROB_NODE]
       \\ rw [])
\\ POP_ORW
\\ fs [FBLOCK_ET_DEF]
\\ sg `prob p (ETREE (NODE (EVENT_TREE_LIST (𝓕𝓑 (X::L))))) = ∏ (∑𝟚𝗗𝑷𝑹𝑶𝑩 p (X::L)) `
   >-( first_x_assum (match_mp_tac)
       \\ rw []
          >-( metis_tac [])
	  >-( metis_tac [])
       \\ irule MUTUAL_INDEP_FRONT_APPEND
       \\ Q.EXISTS_TAC `h`
       \\ once_rewrite_tac[APPEND_ASSOC]
       \\ irule MUTUAL_INDEP_APPEND1
       \\ rw [])
\\ POP_ORW
\\ rw [PROB_SUM_LIST_DEF, PROD_LIST_DEF]
\\ REAL_ARITH_TAC);
(*-------------------------------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------------------------------*)
(*-------------------------------------------------------------------------------------------------*)

(*------------------*)  
(*   ML Functions   *)
(*------------------*)

val ERR = Feedback.mk_HOL_ERR "binary_ieeeLib"
(*--------------------------------------------------------------------------------------------------*)

fun HOL_TO_REAL t =
  if      t ~~ ``($*):real -> real -> real`` then Real.*
  else if t ~~ ``($+):real -> real -> real`` then Real.+
  else if t ~~ ``($/):real -> real -> real`` then Real./
  else if t ~~ ``($-):real -> real -> real`` then Real.-
  else failwith "Unrecognized HOL operator";
(*--------------------------------------------------------------------------------------------------*)

fun REAL_TO_POS_ARBRAT tm =
      case Lib.total realSyntax.dest_injected tm of
         SOME a => Arbrat.fromNat (numLib.dest_numeral a)
       | NONE => raise ERR "REAL_TO_POS_ARBRAT" "";
(*--------------------------------------------------------------------------------------------------*)

fun REAL_TO_SIGNED_ARBRAT tm =
      case Lib.total realSyntax.dest_negated tm of
         SOME a => Arbrat.negate (REAL_TO_POS_ARBRAT a)
       | NONE => REAL_TO_POS_ARBRAT tm;
(*--------------------------------------------------------------------------------------------------*)
     
fun REAL_TO_ARBRAT tm =
      case Lib.total realSyntax.dest_div tm of
         SOME (a, b) =>
            Arbrat./ (REAL_TO_SIGNED_ARBRAT a, REAL_TO_SIGNED_ARBRAT b)
       | NONE => REAL_TO_SIGNED_ARBRAT tm;
(*--------------------------------------------------------------------------------------------------*)
       
fun ARBRAT_TO_MATH_REAL x =
  Real./ (Real.fromInt (Arbint.toInt (Arbrat.numerator x)),
          Real.fromInt (Arbnum.toInt (Arbrat.denominator x)));
(*--------------------------------------------------------------------------------------------------*)

val REAL_TO_MATH_REAL = ARBRAT_TO_MATH_REAL o REAL_TO_ARBRAT;

fun HOL_TO_REAL_EVALUATION t =
 let
     val failstring = "Symbolic expression could not be translated in a number"
 in
     case strip_comb t of 
       (f,[a1, a2]) => HOL_TO_REAL f (HOL_TO_REAL_EVALUATION a1, HOL_TO_REAL_EVALUATION a2)
       | (f,[a]) =>
           if f ~~ ``($&):num -> real`` then Arbnum.toReal (dest_numeral a)
           else failwith failstring
       | _ => failwith failstring
 end;
(*--------------------------------------------------------------------------------------------------*)

fun HOL4_EVALUATION t =
 let
    val failstring = "Symbolic expression could not be translated in a number"
 in
    case strip_comb t of (f,[a1,a2]) =>  

       HOL_TO_REAL f (HOL4_EVALUATION a1,HOL4_EVALUATION a2)
       | (f,[a]) =>
                if f ~~ ``($&):num -> real`` then Arbnum.toReal (dest_numeral a)
	   	else if f ~~  ``exp:real -> real`` then Math.exp (REAL_TO_MATH_REAL (a))
		else failwith failstring
       |_ => failwith failstring
 end;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*----------------------------*)  
(*    ML Printing Functions   *)
(*----------------------------*)
				
fun CONVERT_LIST (L:term) = fst(dest_list L);
(*--------------------------------------------------------------------------------------------------*)

fun PRINT_FBD_PATH n L =
let
     val value = List.nth ((CONVERT_LIST L), n);
in
     print("Path #" ^ " " ^ (int_to_string (n)) ^ " : " ^ " " ^ (term_to_string (value)) ^  "\n")
end;
(*--------------------------------------------------------------------------------------------------*)

fun PRINT_ALL_FBD_PATH_NUMBERS L =
let
    val N = ref (List.length (CONVERT_LIST L) - 1)
in
    while !N <> 0 do
        (PRINT_FBD_PATH (!N) L;N := !N -1);
  PRINT_PATH (!N) L
end;
(*--------------------------------------------------------------------------------------------------*)

fun PROBABILITY CLASS X =
let 
    val value = HOL4_EVALUATION  X;
in
    print("Probability of " ^ " " ^ (term_to_string (CLASS)) ^ " " ^ "Equal" ^ " ");
    print(Real.toString (value) ^ "\n\n")
end;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------------------------*)  
(*  FBD-based Safety Analysis of Nuclear Power Plant System   *)
(*------------------------------------------------------------*)

val WCa_DEF = Define
`WCa [0:num; 1:num; 2:num; 3:num] [l; m; s; t] [Ca; Cb] =
  ⊞  [0:num; 1:num; 2:num; 3:num] (𝓕𝓑 [[l; m; s; t];[Ca; Cb]])`;

val WCb_DEF = Define
`WCb [4:num; 5:num; 6:num; 7:num] [l; m; s; t] [Ca; Cb] =
  ⊞  [4:num; 5:num; 6:num; 7:num] (𝓕𝓑 [[l; m; s; t];[Ca; Cb]])`;

val WYa_DEF = Define
`WYa [0:num; 1:num; 2:num; 3:num] [l; m; s; t] [Ca; Cb] [Ya; Yb] =
  ⊞  [0:num; 1:num; 2:num; 3:num] (𝓕𝓑 [(WCa [0:num; 1:num; 2:num; 3:num] [l; m; s; t] [Ca; Cb]);[Ya; Yb]])`;

val WYb_DEF = Define
`WYb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t] [Ca; Cb] [Ya; Yb] =
  ⊞  [4:num; 5:num; 6:num; 7:num] (𝓕𝓑 [(WCa [0:num; 1:num; 2:num; 3:num] [l; m; s; t] [Ca; Cb]);[Ya; Yb]])`;

val WQa_DEF = Define
`WQa [0:num; 1:num; 2:num; 3:num] [l; m; s; t] [Ca; Cb] [Ya; Yb] [Qa; Qb] =
  ⊞  [0:num; 1:num; 2:num; 3:num] (𝓕𝓑 [(WYa [0:num; 1:num; 2:num; 3:num]
                                             [l; m; s; t] [Ca; Cb] [Ya; Yb]);[Qa; Qb]])`;

val WQb_DEF = Define
`WQb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t] [Ca; Cb] [Ya; Yb] [Qa; Qb] =
  ⊞  [4:num; 5:num; 6:num; 7:num] (𝓕𝓑 [(WYa [0:num; 1:num; 2:num; 3:num]
                                             [l; m; s; t] [Ca; Cb] [Ya; Yb]);[Qa; Qb]])`;

val WUa_DEF = Define
`WUa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t] [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] =
  ⊞  [0:num; 1:num; 2:num; 3:num] (𝓕𝓑 [(WQb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num]
                                             [l; m; s; t] [Ca; Cb] [Ya; Yb] [Qa; Qb]);[Ua; Ub]])`;

val WUb_DEF = Define
`WUb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t] [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] =
  ⊞  [4:num; 5:num; 6:num; 7:num] (𝓕𝓑 [(WQb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num]
                                             [l; m; s; t] [Ca; Cb] [Ya; Yb] [Qa; Qb]);[Ua; Ub]])`;

val WZa_DEF = Define
`WZa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] =
  ⊞  [0:num; 1:num; 2:num; 3:num] (𝓕𝓑 [(WUb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num]
                                             [l; m; s; t] [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub]);[Za; Zb]])`;

val WZb_DEF = Define
`WZb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] =
  ⊞   [4:num; 5:num; 6:num; 7:num] (𝓕𝓑 [(WUb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num]
                                             [l; m; s; t] [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub]);[Za; Zb]])`;

val WVa_DEF = Define
`WVa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb] =
  ⊞  [0:num; 1:num; 2:num; 3:num] (𝓕𝓑 [(WZa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num]
                                       [l; m; s; t] [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb]);[Va; Vb]])`;

val WVb_DEF = Define
`WVb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb] =
  ⊞  [4:num; 5:num; 6:num; 7:num] (𝓕𝓑 [(WZa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num]
                                       [l; m; s; t] [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb]);[Va; Vb]])`;

val WEa_DEF = Define
`WEa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t] [Ca; Cb] [Ya; Yb] [Ea; Eb] =
  ⊞  [0:num; 1:num; 2:num; 3:num] (𝓕𝓑 [(WYb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] 
                                             [l; m; s; t] [Ca; Cb] [Ya; Yb]);[Ea; Eb]])`;

val WEb_DEF = Define
`WEb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t] [Ca; Cb] [Ya; Yb] [Ea; Eb] =
  ⊞  [4:num; 5:num; 6:num; 7:num] (𝓕𝓑 [(WYb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] 
                                             [l; m; s; t] [Ca; Cb] [Ya; Yb]);[Ea; Eb]])`;

val WIa_DEF = Define
`WIa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     [Ca; Cb] [Ya; Yb] [Ea; Eb] [Ia; Ib] =
  ⊞  [0:num; 1:num; 2:num; 3:num] (𝓕𝓑 [(WEa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] 
                                             [l; m; s; t] [Ca; Cb] [Ya; Yb] [Ea; Eb]);[Ia; Ib]])`;

val WIb_DEF = Define
`WIb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     [Ca; Cb] [Ya; Yb] [Ea; Eb] [Ia; Ib] =
  ⊞  [4:num; 5:num; 6:num; 7:num] (𝓕𝓑 [(WEa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] 
                                             [l; m; s; t] [Ca; Cb] [Ya; Yb] [Ea; Eb]);[Ia; Ib]])`;

val WXa_DEF = Define
`WXa [0:num; 1:num; 2:num; 3:num; 4:num; 5:num; 6:num; 7:num; 8:num; 9:num;
       10:num; 11:num; 12:num; 13:num; 14:num; 15:num]
     [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb] [Ea; Eb] [Ia; Ib] [Xa; Xb] =
   ⊞  [0:num; 1:num; 2:num; 3:num; 4:num; 5:num; 6:num; 7:num; 8:num; 9:num;
       10:num; 11:num; 12:num; 13:num; 14:num; 15:num]
   (𝓕𝓑
      [  (WQa [0:num; 1:num; 2:num; 3:num] [l; m; s; t] [Ca; Cb] [Ya; Yb] [Qa; Qb]) ++
         (WUa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t] [Ca; Cb] [Ya; Yb]
              [Qa; Qb] [Ua; Ub]) ++
         (WVa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
              [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb]) ++
	 (WIa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
              [Ca; Cb] [Ya; Yb] [Ea; Eb] [Ia; Ib]); [Xa; Xb]])`;

val WXb_DEF = Define
`WXb [16:num; 17:num; 18:num; 19:num; 20:num; 21:num; 22:num; 23:num; 24:num; 25:num;
      26:num; 27:num; 28:num; 29:num; 30:num; 31:num]
     [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb] [Ea; Eb] [Ia; Ib] [Xa; Xb] =
   ⊞  [16:num; 17:num; 18:num; 19:num; 20:num; 21:num; 22:num; 23:num; 24:num; 25:num;
       26:num; 27:num; 28:num; 29:num; 30:num; 31:num] 
   (𝓕𝓑 [(WQa [0:num; 1:num; 2:num; 3:num] [l; m; s; t] [Ca; Cb] [Ya; Yb] [Qa; Qb]) ++
         (WUa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t] [Ca; Cb] [Ya; Yb]
              [Qa; Qb] [Ua; Ub]) ++
         (WVa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
              [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb]) ++
	 (WIa [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
              [Ca; Cb] [Ya; Yb] [Ea; Eb] [Ia; Ib]); [Xa; Xb]])`;

val WWa_DEF = Define
`WWa [0:num; 1:num; 2:num; 3:num; 4:num; 5:num; 6:num; 7:num; 8:num; 9:num;
       10:num; 11:num; 12:num; 13:num; 14:num; 15:num]
     [16:num; 17:num; 18:num; 19:num; 20:num; 21:num; 22:num; 23:num; 24:num; 25:num;
      26:num; 27:num; 28:num; 29:num; 30:num; 31:num]
     [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb] [Ea; Eb] [Ia; Ib] [Xa; Xb]  [Wa; Wb] =
   ⊞  [0:num; 1:num; 2:num; 3:num; 4:num; 5:num; 6:num; 7:num; 8:num; 9:num;
       10:num; 11:num; 12:num; 13:num; 14:num; 15:num]
   (𝓕𝓑 [(WXb [16:num; 17:num; 18:num; 19:num; 20:num; 21:num; 22:num; 23:num; 24:num; 25:num;
               26:num; 27:num; 28:num; 29:num; 30:num; 31:num]
              [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     	      [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb] [Ea; Eb] [Ia; Ib] [Xa; Xb]); [Wa; Wb]])`;

val WWb_DEF = Define
`WWb [16:num; 17:num; 18:num; 19:num; 20:num; 21:num; 22:num; 23:num; 24:num; 25:num;
      26:num; 27:num; 28:num; 29:num; 30:num; 31:num]
     [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb] [Ea; Eb] [Ia; Ib] [Xa; Xb]  [Wa; Wb] =
   ⊞  [16:num; 17:num; 18:num; 19:num; 20:num; 21:num; 22:num; 23:num; 24:num; 25:num;
       26:num; 27:num; 28:num; 29:num; 30:num; 31:num]
   (𝓕𝓑 [(WXb [16:num; 17:num; 18:num; 19:num; 20:num; 21:num; 22:num; 23:num; 24:num; 25:num;
               26:num; 27:num; 28:num; 29:num; 30:num; 31:num]
              [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     	      [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb] [Ea; Eb] [Ia; Ib] [Xa; Xb]); [Wa; Wb]])`;
(*--------------------------------------------------------------------------------------------------*)

val OUTCOME_SUCCESS_BWR_DEF = Define
`OUTCOME_SUCCESS_BWR [0:num; 1:num; 2:num; 3:num; 4:num; 5:num; 6:num; 7:num; 8:num; 9:num;
                      10:num; 11:num; 12:num; 13:num; 14:num; 15:num]
                     [16:num; 17:num; 18:num; 19:num; 20:num; 21:num; 22:num; 23:num; 24:num; 25:num;
                      26:num; 27:num; 28:num; 29:num; 30:num; 31:num]
                     [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
                     [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb] [Ea; Eb] [Ia; Ib] [Xa; Xb] [Wa; Wb] =
𝓕𝓑𝑬𝑻 (𝓕𝓑𝑬𝑻Ν [(WXa [0:num; 1:num; 2:num; 3:num; 4:num; 5:num; 6:num; 7:num; 8:num; 9:num;
       	              10:num; 11:num; 12:num; 13:num; 14:num; 15:num]
                     [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     		     [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb] [Ea; Eb] [Ia; Ib] [Xa; Xb]);
               (WWa [0:num; 1:num; 2:num; 3:num; 4:num; 5:num; 6:num; 7:num; 8:num; 9:num;
                     10:num; 11:num; 12:num; 13:num; 14:num; 15:num]
                    [16:num; 17:num; 18:num; 19:num; 20:num; 21:num; 22:num; 23:num; 24:num; 25:num;
                     26:num; 27:num; 28:num; 29:num; 30:num; 31:num]
                    [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
                    [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb] [Ea; Eb] [Ia; Ib] [Xa; Xb] [Wa; Wb])])`; 
(*--------------------------------------------------------------------------------------------------*)

val OUTCOME_CLASS_I_BWR_DEF = Define
`OUTCOME_CLASS_I_BWR [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     		     [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb] =
      𝓕𝓑𝑬𝑻 (𝓕𝓑𝑬𝑻Ν [(WVb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
                           [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb]);
                      (WZb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
                           [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb])])`;
(*--------------------------------------------------------------------------------------------------*)

val OUTCOME_CLASS_II_BWR_DEF = Define
`OUTCOME_CLASS_II_BWR  [16:num; 17:num; 18:num; 19:num; 20:num; 21:num; 22:num; 23:num; 24:num; 25:num;
      		        26:num; 27:num; 28:num; 29:num; 30:num; 31:num]
                       [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
                       [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb] [Ea; Eb] [Ia; Ib] [Xa; Xb] [Wa; Wb] =
     𝓕𝓑𝑬𝑻 (WWb [16:num; 17:num; 18:num; 19:num; 20:num; 21:num; 22:num; 23:num; 24:num; 25:num;
                 26:num; 27:num; 28:num; 29:num; 30:num; 31:num]
                [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     	 	[Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb] [Ea; Eb] [Ia; Ib] [Xa; Xb] [Wa; Wb])`;
(*--------------------------------------------------------------------------------------------------*)

val OUTCOME_CLASS_III_BWR_DEF = Define
`OUTCOME_CLASS_III_BWR [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     		       [Ca; Cb] [Ya; Yb] [Ea; Eb] [Ia; Ib] = 
     𝓕𝓑𝑬𝑻 (𝓕𝓑𝑬𝑻Ν [(WEb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num]
                          [l; m; s; t] [Ca; Cb] [Ya; Yb] [Ea; Eb]);
                     (WIb [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
                          [Ca; Cb] [Ya; Yb] [Ea; Eb] [Ia; Ib])])`;
(*--------------------------------------------------------------------------------------------------*)

val OUTCOME_CLASS_IV_BWR_DEF = Define
`OUTCOME_CLASS_IV_BWR  [4:num; 5:num; 6:num; 7:num] [l; m; s; t] [Ca; Cb] = 
    𝓕𝓑𝑬𝑻  (WCb [4:num; 5:num; 6:num; 7:num] [l; m; s; t] [Ca; Cb])`;
(*--------------------------------------------------------------------------------------------------*)

val PROB_OUTCOME_CLASS_III_BWR = store_thm("PROB_OUTCOME_CLASS_III_BWR",
``!p l m s t Ca Cb Ya Yb Ea Eb Ia Ib.
    prob_space p /\
    disjoint
      (set
         (MAP (λa. PATH p a)
            [[Eb; Yb; Ca; l]; [Eb; Yb; Ca; m]; [Eb; Yb; Ca; s];
             [Eb; Yb; Ca; t]; [Ib; Ea; Yb; Ca; l]; [Ib; Ea; Yb; Ca; m];
             [Ib; Ea; Yb; Ca; s]; [Ib; Ea; Yb; Ca; t]])) /\
    ALL_DISTINCT
      (MAP (λa. PATH p a)
         [[Eb; Yb; Ca; l]; [Eb; Yb; Ca; m]; [Eb; Yb; Ca; s]; [Eb; Yb; Ca; t];
          [Ib; Ea; Yb; Ca; l]; [Ib; Ea; Yb; Ca; m]; [Ib; Ea; Yb; Ca; s];
          [Ib; Ea; Yb; Ca; t]]) /\
    (∀x'.
         MEM x'[Eb; Yb; Ca; l; Eb; Yb; Ca; m; Eb; Yb; Ca; s; Eb; Yb; Ca; t; Ib; Ea;
                Yb; Ca; l; Ib; Ea; Yb; Ca; m; Ib; Ea; Yb; Ca; s; Ib; Ea; Yb; Ca; t] ⇒ x' ∈ events p) /\
    (MUTUAL_INDEP p
      [Eb; Yb; Ca; l; Eb; Yb; Ca; m; Eb; Yb; Ca; s; Eb; Yb; Ca; t; Ib; Ea;
       Yb; Ca; l; Ib; Ea; Yb; Ca; m; Ib; Ea; Yb; Ca; s; Ib; Ea; Yb; Ca; t]) ==>
  prob p (OUTCOME_CLASS_III_BWR [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
     	  			[Ca; Cb] [Ya; Yb] [Ea; Eb] [Ia; Ib]) =
  prob p Eb * prob p Yb * prob p Ca * prob p l +
  prob p Eb * prob p Yb * prob p Ca * prob p m +
  prob p Eb * prob p Yb * prob p Ca * prob p s +
  prob p Eb * prob p Yb * prob p Ca * prob p t +
  prob p Ib * prob p Ea * prob p Yb * prob p Ca * prob p l  +
  prob p Ib * prob p Ea * prob p Yb * prob p Ca * prob p m  +
  prob p Ib * prob p Ea * prob p Yb * prob p Ca * prob p s  +
  prob p Ib * prob p Ea * prob p Yb * prob p Ca * prob p t``,			

rw [OUTCOME_CLASS_III_BWR_DEF]
\\ rw [WEb_DEF, WIb_DEF]
\\ rw [WYb_DEF, WEa_DEF]
\\ rw [WCa_DEF]
\\ sg `(𝓕𝓑𝑬𝑻
        (𝓕𝓑𝑬𝑻Ν
           [⊞ [4; 5; 6; 7]
              (𝓕𝓑
                 [⊞ [4; 5; 6; 7]
                    (𝓕𝓑
                       [⊞ [0; 1; 2; 3] (𝓕𝓑 [[l; m; s; t]; [Ca; Cb]]);
                        [Ya; Yb]]); [Ea; Eb]]);
            ⊞ [4; 5; 6; 7]
              (𝓕𝓑
                 [⊞ [0; 1; 2; 3]
                    (𝓕𝓑
                       [⊞ [4; 5; 6; 7]
                          (𝓕𝓑
                             [⊞ [0; 1; 2; 3] (𝓕𝓑 [[l; m; s; t]; [Ca; Cb]]);
                              [Ya; Yb]]); [Ea; Eb]]); [Ia; Ib]])])) =

  (Eb ∩ (Yb ∩ (Ca ∩ l)) ∪
      (Eb ∩ (Yb ∩ (Ca ∩ m)) ∪
       (Eb ∩ (Yb ∩ (Ca ∩ s)) ∪ (Eb ∩ (Yb ∩ (Ca ∩ t)) ∪ ∅))) ∪
      (Ib ∩ (Ea ∩ (Yb ∩ (Ca ∩ l))) ∪
       (Ib ∩ (Ea ∩ (Yb ∩ (Ca ∩ m))) ∪
        (Ib ∩ (Ea ∩ (Yb ∩ (Ca ∩ s))) ∪ (Ib ∩ (Ea ∩ (Yb ∩ (Ca ∩ t))) ∪ ∅))) ∪
       ∅))`
   >-(EVAL_TAC)
\\ POP_ORW
\\ rw [INTER_ASSOC, UNION_OVER_INTER, UNION_ASSOC]
\\ sg `Eb ∩ Yb ∩ Ca ∩ l ∪ Eb ∩ Yb ∩ Ca ∩ m ∪ Eb ∩ Yb ∩ Ca ∩ s ∪
       Eb ∩ Yb ∩ Ca ∩ t ∪ Ib ∩ Ea ∩ Yb ∩ Ca ∩ l ∪ Ib ∩ Ea ∩ Yb ∩ Ca ∩ m ∪
       Ib ∩ Ea ∩ Yb ∩ Ca ∩ s ∪ Ib ∩ Ea ∩ Yb ∩ Ca ∩ t =
   ETREE (NODE (EVENT_TREE_LIST (MAP (λa. ET_PATH p a)
   [[Eb;Yb;Ca;l];[Eb;Yb;Ca;m];[Eb;Yb;Ca;s];[Eb;Yb;Ca;t];[Ib;Ea;Yb;Ca;l];
    [Ib;Ea;Yb;Ca;m];[Ib;Ea;Yb;Ca;s];[Ib;Ea;Yb;Ca;t]])))`
  >-( rw [ET_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
      \\ rw [UNION_ASSOC])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NODE_OF_ET_PATHS]
\\ fs []
\\ sg `(∀z.
              z = [Eb; Yb; Ca; l] ∨ z = [Eb; Yb; Ca; m] ∨
              z = [Eb; Yb; Ca; s] ∨ z = [Eb; Yb; Ca; t] ∨
              z = [Ib; Ea; Yb; Ca; l] ∨ z = [Ib; Ea; Yb; Ca; m] ∨
              z = [Ib; Ea; Yb; Ca; s] ∨ z = [Ib; Ea; Yb; Ca; t] ⇒
              ~NULL z)`
   >-( metis_tac [NULL])
\\ sg ` (∀x'.
             x' = Eb ∨ x' = Yb ∨ x' = Ca ∨ x' = l ∨ x' = Eb ∨ x' = Yb ∨
             x' = Ca ∨ x' = m ∨ x' = Eb ∨ x' = Yb ∨ x' = Ca ∨ x' = s ∨
             x' = Eb ∨ x' = Yb ∨ x' = Ca ∨ x' = t ∨ x' = Ib ∨ x' = Ea ∨
             x' = Yb ∨ x' = Ca ∨ x' = l ∨ x' = Ib ∨ x' = Ea ∨ x' = Yb ∨
             x' = Ca ∨ x' = m ∨ x' = Ib ∨ x' = Ea ∨ x' = Yb ∨ x' = Ca ∨
             x' = s ∨ x' = Ib ∨ x' = Ea ∨ x' = Yb ∨ x' = Ca ∨ x' = t ⇒
             x' ∈ events p) `
   >-( metis_tac [])
\\ REWRITE_TAC [PROB_LIST_DEF, PROD_LIST_DEF, SUM_LIST_DEF]
\\ sg `prob p Eb * (prob p Yb * (prob p Ca * (prob p l * 1))) +
        (prob p Eb * (prob p Yb * (prob p Ca * (prob p m * 1))) +
         (prob p Eb * (prob p Yb * (prob p Ca * (prob p s * 1))) +
          (prob p Eb * (prob p Yb * (prob p Ca * (prob p t * 1))) +
           (prob p Ib *
            (prob p Ea * (prob p Yb * (prob p Ca * (prob p l * 1)))) +
            (prob p Ib *
             (prob p Ea * (prob p Yb * (prob p Ca * (prob p m * 1)))) +
             (prob p Ib *
              (prob p Ea * (prob p Yb * (prob p Ca * (prob p s * 1)))) +
              (prob p Ib *
               (prob p Ea * (prob p Yb * (prob p Ca * (prob p t * 1)))) + 0))))))) =
        prob p Eb * prob p Yb * prob p Ca * prob p l +
        prob p Eb * prob p Yb * prob p Ca * prob p m +
        prob p Eb * prob p Yb * prob p Ca * prob p s +
        prob p Eb * prob p Yb * prob p Ca * prob p t +
        prob p Ib * prob p Ea * prob p Yb * prob p Ca * prob p l +
        prob p Ib * prob p Ea * prob p Yb * prob p Ca * prob p m +
        prob p Ib * prob p Ea * prob p Yb * prob p Ca * prob p s +
        prob p Ib * prob p Ea * prob p Yb * prob p Ca * prob p t `
   >-(REAL_ARITH_TAC)
\\ metis_tac []);   
(*--------------------------------------------------------------------------------------------------*)

val PROB_OUTCOME_CLASS_II_BWR = store_thm("PROB_OUTCOME_CLASS_II_BWR",
``!p l m s t Ca Cb Qa Qb Ya Yb Ua Ub Ea Eb Ia Ib Za Zb Va Vb Xa Xb Wa Wb.
  prob_space p /\
           disjoint
           (set
              (MAP (λa. PATH p a)
                 [[Wb; Xb; Qa; Ya; Ca; l]; [Wb; Xb; Qa; Ya; Ca; m];
                  [Wb; Xb; Qa; Ya; Ca; s]; [Wb; Xb; Qa; Ya; Ca; t];
                  [Wb; Xb; Ua; Qb; Ya; Ca; l]; [Wb; Xb; Ua; Qb; Ya; Ca; m];
                  [Wb; Xb; Ua; Qb; Ya; Ca; s]; [Wb; Xb; Ua; Qb; Ya; Ca; t];
                  [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; l];
                  [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; m];
                  [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; s];
                  [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; t];
                  [Wb; Xb; Ia; Ea; Yb; Ca; l]; [Wb; Xb; Ia; Ea; Yb; Ca; m];
                  [Wb; Xb; Ia; Ea; Yb; Ca; s]; [Wb; Xb; Ia; Ea; Yb; Ca; t]])) /\
         ALL_DISTINCT
           (MAP (λa. PATH p a)
              [[Wb; Xb; Qa; Ya; Ca; l]; [Wb; Xb; Qa; Ya; Ca; m];
               [Wb; Xb; Qa; Ya; Ca; s]; [Wb; Xb; Qa; Ya; Ca; t];
               [Wb; Xb; Ua; Qb; Ya; Ca; l]; [Wb; Xb; Ua; Qb; Ya; Ca; m];
               [Wb; Xb; Ua; Qb; Ya; Ca; s]; [Wb; Xb; Ua; Qb; Ya; Ca; t];
               [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; l];
               [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; m];
               [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; s];
               [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; t];
               [Wb; Xb; Ia; Ea; Yb; Ca; l]; [Wb; Xb; Ia; Ea; Yb; Ca; m];
               [Wb; Xb; Ia; Ea; Yb; Ca; s]; [Wb; Xb; Ia; Ea; Yb; Ca; t]]) /\
         (∀x'.
              x' = Wb ∨ x' = Xb ∨ x' = Qa ∨ x' = Ya ∨ x' = Ca ∨ x' = l ∨
              x' = Wb ∨ x' = Xb ∨ x' = Qa ∨ x' = Ya ∨ x' = Ca ∨ x' = m ∨
              x' = Wb ∨ x' = Xb ∨ x' = Qa ∨ x' = Ya ∨ x' = Ca ∨ x' = s ∨
              x' = Wb ∨ x' = Xb ∨ x' = Qa ∨ x' = Ya ∨ x' = Ca ∨ x' = t ∨
              x' = Wb ∨ x' = Xb ∨ x' = Ua ∨ x' = Qb ∨ x' = Ya ∨ x' = Ca ∨
              x' = l ∨ x' = Wb ∨ x' = Xb ∨ x' = Ua ∨ x' = Qb ∨ x' = Ya ∨
              x' = Ca ∨ x' = m ∨ x' = Wb ∨ x' = Xb ∨ x' = Ua ∨ x' = Qb ∨
              x' = Ya ∨ x' = Ca ∨ x' = s ∨ x' = Wb ∨ x' = Xb ∨ x' = Ua ∨
              x' = Qb ∨ x' = Ya ∨ x' = Ca ∨ x' = t ∨ x' = Wb ∨ x' = Xb ∨
              x' = Va ∨ x' = Za ∨ x' = Ub ∨ x' = Qb ∨ x' = Ya ∨ x' = Ca ∨
              x' = l ∨ x' = Wb ∨ x' = Xb ∨ x' = Va ∨ x' = Za ∨ x' = Ub ∨
              x' = Qb ∨ x' = Ya ∨ x' = Ca ∨ x' = m ∨ x' = Wb ∨ x' = Xb ∨
              x' = Va ∨ x' = Za ∨ x' = Ub ∨ x' = Qb ∨ x' = Ya ∨ x' = Ca ∨
              x' = s ∨ x' = Wb ∨ x' = Xb ∨ x' = Va ∨ x' = Za ∨ x' = Ub ∨
              x' = Qb ∨ x' = Ya ∨ x' = Ca ∨ x' = t ∨ x' = Wb ∨ x' = Xb ∨
              x' = Ia ∨ x' = Ea ∨ x' = Yb ∨ x' = Ca ∨ x' = l ∨ x' = Wb ∨
              x' = Xb ∨ x' = Ia ∨ x' = Ea ∨ x' = Yb ∨ x' = Ca ∨ x' = m ∨
              x' = Wb ∨ x' = Xb ∨ x' = Ia ∨ x' = Ea ∨ x' = Yb ∨ x' = Ca ∨
              x' = s ∨ x' = Wb ∨ x' = Xb ∨ x' = Ia ∨ x' = Ea ∨ x' = Yb ∨
              x' = Ca ∨ x' = t ⇒ x' ∈ events p) /\
         (MUTUAL_INDEP p
           [Wb; Xb; Qa; Ya; Ca; l; Wb; Xb; Qa; Ya; Ca; m; Wb; Xb; Qa; Ya; Ca;
            s; Wb; Xb; Qa; Ya; Ca; t; Wb; Xb; Ua; Qb; Ya; Ca; l; Wb; Xb; Ua;
            Qb; Ya; Ca; m; Wb; Xb; Ua; Qb; Ya; Ca; s; Wb; Xb; Ua; Qb; Ya; Ca;
            t; Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; l; Wb; Xb; Va; Za; Ub; Qb; Ya;
            Ca; m; Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; s; Wb; Xb; Va; Za; Ub; Qb;
            Ya; Ca; t; Wb; Xb; Ia; Ea; Yb; Ca; l; Wb; Xb; Ia; Ea; Yb; Ca; m;
            Wb; Xb; Ia; Ea; Yb; Ca; s; Wb; Xb; Ia; Ea; Yb; Ca; t]) ==>
  prob p (OUTCOME_CLASS_II_BWR [16:num; 17:num; 18:num; 19:num; 20:num; 21:num; 22:num; 23:num; 24:num; 25:num;
      		                26:num; 27:num; 28:num; 29:num; 30:num; 31:num]
                               [0:num; 1:num; 2:num; 3:num] [4:num; 5:num; 6:num; 7:num] [l; m; s; t]
                       	       [Ca; Cb] [Ya; Yb] [Qa; Qb] [Ua; Ub] [Za; Zb] [Va; Vb]
			       [Ea; Eb] [Ia; Ib] [Xa; Xb] [Wa; Wb]) =
         prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p l  +
         prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p m  +
         prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p s  +
         prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p t  +
         prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p l +
         prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p m +
         prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p s +
         prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p t +
         prob p Wb * prob p Xb * prob p Va * prob p Za * prob p Ub * prob p Qb * prob p Ya * prob p Ca * prob p l +
         prob p Wb * prob p Xb * prob p Va * prob p Za * prob p Ub * prob p Qb * prob p Ya * prob p Ca * prob p m +
         prob p Wb * prob p Xb * prob p Va * prob p Za * prob p Ub * prob p Qb * prob p Ya * prob p Ca * prob p s +
         prob p Wb * prob p Xb * prob p Va * prob p Za * prob p Ub * prob p Qb * prob p Ya * prob p Ca * prob p t +
         prob p Wb * prob p Xb * prob p Ia * prob p Ea * prob p Yb * prob p Ca * prob p l  +
         prob p Wb * prob p Xb * prob p Ia * prob p Ea * prob p Yb * prob p Ca * prob p m  +
         prob p Wb * prob p Xb * prob p Ia * prob p Ea * prob p Yb * prob p Ca * prob p s  +
         prob p Wb * prob p Xb * prob p Ia * prob p Ea * prob p Yb * prob p Ca * prob p t``,

rw [OUTCOME_CLASS_II_BWR_DEF]
\\ rw [WWb_DEF, WXb_DEF]
\\ rw [WQa_DEF, WUa_DEF, WVa_DEF, WIa_DEF]
\\ rw [WYa_DEF, WQb_DEF, WZa_DEF, WEa_DEF]
\\ rw [WCa_DEF, WUb_DEF, WYb_DEF]
\\ rw [WQb_DEF, WYa_DEF, WCa_DEF]
\\ sg `(𝓕𝓑𝑬𝑻
             (⊞
                [16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30;
                 31]
                (𝓕𝓑
                   [⊞
                      [16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28;
                       29; 30; 31]
                      (𝓕𝓑
                         [⊞ [0; 1; 2; 3]
                            (𝓕𝓑
                               [⊞ [0; 1; 2; 3]
                                  (𝓕𝓑
                                     [⊞ [0; 1; 2; 3]
                                        (𝓕𝓑 [[l; m; s; t]; [Ca; Cb]]);
                                      [Ya; Yb]]); [Qa; Qb]]) ⧺
                          ⊞ [0; 1; 2; 3]
                            (𝓕𝓑
                               [⊞ [4; 5; 6; 7]
                                  (𝓕𝓑
                                     [⊞ [0; 1; 2; 3]
                                        (𝓕𝓑
                                           [⊞ [0; 1; 2; 3]
                                              (𝓕𝓑 [[l; m; s; t]; [Ca; Cb]]);
                                            [Ya; Yb]]); [Qa; Qb]]); [Ua; Ub]]) ⧺
                          ⊞ [0; 1; 2; 3]
                            (𝓕𝓑
                               [⊞ [0; 1; 2; 3]
                                  (𝓕𝓑
                                     [⊞ [4; 5; 6; 7]
                                        (𝓕𝓑
                                           [⊞ [4; 5; 6; 7]
                                              (𝓕𝓑
                                                 [⊞ [0; 1; 2; 3]
                                                    (𝓕𝓑
                                                       [⊞ [0; 1; 2; 3]
                                                          (𝓕𝓑
                                                             [[l; m; s; t];
                                                              [Ca; Cb]]);
                                                        [Ya; Yb]]); [Qa; Qb]]);
                                            [Ua; Ub]]); [Za; Zb]]); [Va; Vb]]) ⧺
                          ⊞ [0; 1; 2; 3]
                            (𝓕𝓑
                               [⊞ [0; 1; 2; 3]
                                  (𝓕𝓑
                                     [⊞ [4; 5; 6; 7]
                                        (𝓕𝓑
                                           [⊞ [0; 1; 2; 3]
                                              (𝓕𝓑 [[l; m; s; t]; [Ca; Cb]]);
                                            [Ya; Yb]]); [Ea; Eb]]); [Ia; Ib]]);
                          [Xa; Xb]]); [Wa; Wb]]))) =
         (Wb ∩ (Xb ∩ (Qa ∩ (Ya ∩ (Ca ∩ l)))) ∪
           (Wb ∩ (Xb ∩ (Qa ∩ (Ya ∩ (Ca ∩ m)))) ∪
            (Wb ∩ (Xb ∩ (Qa ∩ (Ya ∩ (Ca ∩ s)))) ∪
             (Wb ∩ (Xb ∩ (Qa ∩ (Ya ∩ (Ca ∩ t)))) ∪
              (Wb ∩ (Xb ∩ (Ua ∩ (Qb ∩ (Ya ∩ (Ca ∩ l))))) ∪
               (Wb ∩ (Xb ∩ (Ua ∩ (Qb ∩ (Ya ∩ (Ca ∩ m))))) ∪
                (Wb ∩ (Xb ∩ (Ua ∩ (Qb ∩ (Ya ∩ (Ca ∩ s))))) ∪
                 (Wb ∩ (Xb ∩ (Ua ∩ (Qb ∩ (Ya ∩ (Ca ∩ t))))) ∪
                  (Wb ∩ (Xb ∩ (Va ∩ (Za ∩ (Ub ∩ (Qb ∩ (Ya ∩ (Ca ∩ l))))))) ∪
                   (Wb ∩ (Xb ∩ (Va ∩ (Za ∩ (Ub ∩ (Qb ∩ (Ya ∩ (Ca ∩ m))))))) ∪
                    (Wb ∩ (Xb ∩ (Va ∩ (Za ∩ (Ub ∩ (Qb ∩ (Ya ∩ (Ca ∩ s))))))) ∪
                     (Wb ∩ (Xb ∩ (Va ∩ (Za ∩ (Ub ∩ (Qb ∩ (Ya ∩ (Ca ∩ t))))))) ∪
                      (Wb ∩ (Xb ∩ (Ia ∩ (Ea ∩ (Yb ∩ (Ca ∩ l))))) ∪
                       (Wb ∩ (Xb ∩ (Ia ∩ (Ea ∩ (Yb ∩ (Ca ∩ m))))) ∪
                        (Wb ∩ (Xb ∩ (Ia ∩ (Ea ∩ (Yb ∩ (Ca ∩ s))))) ∪
                         (Wb ∩ (Xb ∩ (Ia ∩ (Ea ∩ (Yb ∩ (Ca ∩ t))))) ∪ ∅)))))))))))))))) `

   >-(EVAL_TAC)
\\ POP_ORW
\\ rw [INTER_ASSOC, UNION_OVER_INTER, UNION_ASSOC]
\\ sg `   (Wb ∩ Xb ∩ Qa ∩ Ya ∩ Ca ∩ l ∪ Wb ∩ Xb ∩ Qa ∩ Ya ∩ Ca ∩ m ∪
           Wb ∩ Xb ∩ Qa ∩ Ya ∩ Ca ∩ s ∪ Wb ∩ Xb ∩ Qa ∩ Ya ∩ Ca ∩ t ∪
           Wb ∩ Xb ∩ Ua ∩ Qb ∩ Ya ∩ Ca ∩ l ∪
           Wb ∩ Xb ∩ Ua ∩ Qb ∩ Ya ∩ Ca ∩ m ∪
           Wb ∩ Xb ∩ Ua ∩ Qb ∩ Ya ∩ Ca ∩ s ∪
           Wb ∩ Xb ∩ Ua ∩ Qb ∩ Ya ∩ Ca ∩ t ∪
           Wb ∩ Xb ∩ Va ∩ Za ∩ Ub ∩ Qb ∩ Ya ∩ Ca ∩ l ∪
           Wb ∩ Xb ∩ Va ∩ Za ∩ Ub ∩ Qb ∩ Ya ∩ Ca ∩ m ∪
           Wb ∩ Xb ∩ Va ∩ Za ∩ Ub ∩ Qb ∩ Ya ∩ Ca ∩ s ∪
           Wb ∩ Xb ∩ Va ∩ Za ∩ Ub ∩ Qb ∩ Ya ∩ Ca ∩ t ∪
           Wb ∩ Xb ∩ Ia ∩ Ea ∩ Yb ∩ Ca ∩ l ∪
           Wb ∩ Xb ∩ Ia ∩ Ea ∩ Yb ∩ Ca ∩ m ∪
           Wb ∩ Xb ∩ Ia ∩ Ea ∩ Yb ∩ Ca ∩ s ∪ Wb ∩ Xb ∩ Ia ∩ Ea ∩ Yb ∩ Ca ∩ t) =
    ETREE (NODE (EVENT_TREE_LIST (MAP (λa. ET_PATH p a)
         [[Wb; Xb; Qa; Ya; Ca; l]; 
	  [Wb; Xb; Qa; Ya; Ca; m];
	  [Wb; Xb; Qa; Ya; Ca; s];
	  [Wb; Xb; Qa; Ya; Ca; t];
	  [Wb; Xb; Ua; Qb; Ya; Ca; l];
	  [Wb; Xb; Ua; Qb; Ya; Ca; m];
	  [Wb; Xb; Ua; Qb; Ya; Ca; s];
	  [Wb; Xb; Ua; Qb; Ya; Ca; t];
	  [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; l];
	  [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; m];
	  [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; s];
	  [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; t];
	  [Wb; Xb; Ia; Ea; Yb; Ca; l];
	  [Wb; Xb; Ia; Ea; Yb; Ca; m];
	  [Wb; Xb; Ia; Ea; Yb; Ca; s];
	  [Wb; Xb; Ia; Ea; Yb; Ca; t]])))`
  >-( rw [ET_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
      \\ rw [UNION_ASSOC])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NODE_OF_ET_PATHS]
\\ fs []
\\ sg `(∀z.
              z = [Wb; Xb; Qa; Ya; Ca; l] ∨ z = [Wb; Xb; Qa; Ya; Ca; m] ∨
              z = [Wb; Xb; Qa; Ya; Ca; s] ∨ z = [Wb; Xb; Qa; Ya; Ca; t] ∨
              z = [Wb; Xb; Ua; Qb; Ya; Ca; l] ∨
              z = [Wb; Xb; Ua; Qb; Ya; Ca; m] ∨
              z = [Wb; Xb; Ua; Qb; Ya; Ca; s] ∨
              z = [Wb; Xb; Ua; Qb; Ya; Ca; t] ∨
              z = [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; l] ∨
              z = [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; m] ∨
              z = [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; s] ∨
              z = [Wb; Xb; Va; Za; Ub; Qb; Ya; Ca; t] ∨
              z = [Wb; Xb; Ia; Ea; Yb; Ca; l] ∨
              z = [Wb; Xb; Ia; Ea; Yb; Ca; m] ∨
              z = [Wb; Xb; Ia; Ea; Yb; Ca; s] ∨
              z = [Wb; Xb; Ia; Ea; Yb; Ca; t] ⇒
              ~NULL z)`
   >-( metis_tac [NULL])
\\ sg `(∀x'.
             x' = Wb ∨ x' = Xb ∨ x' = Qa ∨ x' = Ya ∨ x' = Ca ∨ x' = l ∨
             x' = Wb ∨ x' = Xb ∨ x' = Qa ∨ x' = Ya ∨ x' = Ca ∨ x' = m ∨
             x' = Wb ∨ x' = Xb ∨ x' = Qa ∨ x' = Ya ∨ x' = Ca ∨ x' = s ∨
             x' = Wb ∨ x' = Xb ∨ x' = Qa ∨ x' = Ya ∨ x' = Ca ∨ x' = t ∨
             x' = Wb ∨ x' = Xb ∨ x' = Ua ∨ x' = Qb ∨ x' = Ya ∨ x' = Ca ∨
             x' = l ∨ x' = Wb ∨ x' = Xb ∨ x' = Ua ∨ x' = Qb ∨ x' = Ya ∨
             x' = Ca ∨ x' = m ∨ x' = Wb ∨ x' = Xb ∨ x' = Ua ∨ x' = Qb ∨
             x' = Ya ∨ x' = Ca ∨ x' = s ∨ x' = Wb ∨ x' = Xb ∨ x' = Ua ∨
             x' = Qb ∨ x' = Ya ∨ x' = Ca ∨ x' = t ∨ x' = Wb ∨ x' = Xb ∨
             x' = Va ∨ x' = Za ∨ x' = Ub ∨ x' = Qb ∨ x' = Ya ∨ x' = Ca ∨
             x' = l ∨ x' = Wb ∨ x' = Xb ∨ x' = Va ∨ x' = Za ∨ x' = Ub ∨
             x' = Qb ∨ x' = Ya ∨ x' = Ca ∨ x' = m ∨ x' = Wb ∨ x' = Xb ∨
             x' = Va ∨ x' = Za ∨ x' = Ub ∨ x' = Qb ∨ x' = Ya ∨ x' = Ca ∨
             x' = s ∨ x' = Wb ∨ x' = Xb ∨ x' = Va ∨ x' = Za ∨ x' = Ub ∨
             x' = Qb ∨ x' = Ya ∨ x' = Ca ∨ x' = t ∨ x' = Wb ∨ x' = Xb ∨
             x' = Ia ∨ x' = Ea ∨ x' = Yb ∨ x' = Ca ∨ x' = l ∨ x' = Wb ∨
             x' = Xb ∨ x' = Ia ∨ x' = Ea ∨ x' = Yb ∨ x' = Ca ∨ x' = m ∨
             x' = Wb ∨ x' = Xb ∨ x' = Ia ∨ x' = Ea ∨ x' = Yb ∨ x' = Ca ∨
             x' = s ∨ x' = Wb ∨ x' = Xb ∨ x' = Ia ∨ x' = Ea ∨ x' = Yb ∨
             x' = Ca ∨ x' = t ⇒ x' ∈ events p)`
   >-( metis_tac [])
\\ REWRITE_TAC [PROB_LIST_DEF, PROD_LIST_DEF, SUM_LIST_DEF]
\\ sg ` prob p Wb *
        (prob p Xb *
         (prob p Qa * (prob p Ya * (prob p Ca * (prob p l * 1))))) +
        (prob p Wb *
         (prob p Xb *
          (prob p Qa * (prob p Ya * (prob p Ca * (prob p m * 1))))) +
         (prob p Wb *
          (prob p Xb *
           (prob p Qa * (prob p Ya * (prob p Ca * (prob p s * 1))))) +
          (prob p Wb *
           (prob p Xb *
            (prob p Qa * (prob p Ya * (prob p Ca * (prob p t * 1))))) +
           (prob p Wb *
            (prob p Xb *
             (prob p Ua *
              (prob p Qb * (prob p Ya * (prob p Ca * (prob p l * 1)))))) +
            (prob p Wb *
             (prob p Xb *
              (prob p Ua *
               (prob p Qb * (prob p Ya * (prob p Ca * (prob p m * 1)))))) +
             (prob p Wb *
              (prob p Xb *
               (prob p Ua *
                (prob p Qb * (prob p Ya * (prob p Ca * (prob p s * 1)))))) +
              (prob p Wb *
               (prob p Xb *
                (prob p Ua *
                 (prob p Qb * (prob p Ya * (prob p Ca * (prob p t * 1)))))) +
               (prob p Wb *
                (prob p Xb *
                 (prob p Va *
                  (prob p Za *
                   (prob p Ub *
                    (prob p Qb * (prob p Ya * (prob p Ca * (prob p l * 1)))))))) +
                (prob p Wb *
                 (prob p Xb *
                  (prob p Va *
                   (prob p Za *
                    (prob p Ub *
                     (prob p Qb * (prob p Ya * (prob p Ca * (prob p m * 1)))))))) +
                 (prob p Wb *
                  (prob p Xb *
                   (prob p Va *
                    (prob p Za *
                     (prob p Ub *
                      (prob p Qb *
                       (prob p Ya * (prob p Ca * (prob p s * 1)))))))) +
                  (prob p Wb *
                   (prob p Xb *
                    (prob p Va *
                     (prob p Za *
                      (prob p Ub *
                       (prob p Qb *
                        (prob p Ya * (prob p Ca * (prob p t * 1)))))))) +
                   (prob p Wb *
                    (prob p Xb *
                     (prob p Ia *
                      (prob p Ea *
                       (prob p Yb * (prob p Ca * (prob p l * 1)))))) +
                    (prob p Wb *
                     (prob p Xb *
                      (prob p Ia *
                       (prob p Ea *
                        (prob p Yb * (prob p Ca * (prob p m * 1)))))) +
                     (prob p Wb *
                      (prob p Xb *
                       (prob p Ia *
                        (prob p Ea *
                         (prob p Yb * (prob p Ca * (prob p s * 1)))))) +
                      (prob p Wb *
                       (prob p Xb *
                        (prob p Ia *
                         (prob p Ea *
                          (prob p Yb * (prob p Ca * (prob p t * 1)))))) + 0))))))))))))))) =
         prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p l  +
         prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p m  +
         prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p s  +
         prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p t  +
         prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p l +
         prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p m +
         prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p s +
         prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p t +
         prob p Wb * prob p Xb * prob p Va * prob p Za * prob p Ub * prob p Qb * prob p Ya * prob p Ca * prob p l +
         prob p Wb * prob p Xb * prob p Va * prob p Za * prob p Ub * prob p Qb * prob p Ya * prob p Ca * prob p m +
         prob p Wb * prob p Xb * prob p Va * prob p Za * prob p Ub * prob p Qb * prob p Ya * prob p Ca * prob p s +
         prob p Wb * prob p Xb * prob p Va * prob p Za * prob p Ub * prob p Qb * prob p Ya * prob p Ca * prob p t +
         prob p Wb * prob p Xb * prob p Ia * prob p Ea * prob p Yb * prob p Ca * prob p l  +
         prob p Wb * prob p Xb * prob p Ia * prob p Ea * prob p Yb * prob p Ca * prob p m  +
         prob p Wb * prob p Xb * prob p Ia * prob p Ea * prob p Yb * prob p Ca * prob p s  +
         prob p Wb * prob p Xb * prob p Ia * prob p Ea * prob p Yb * prob p Ca * prob p t`
   >-(REAL_ARITH_TAC)
\\ metis_tac []);   
(*--------------------------------------------------------------------------------------------------*)



val _ = export_theory();

(*--------------------------------------------------------------------------------------------------*)
        (*------------------------------------------------------------------------------------*)
                     (*-----------------------------------------------------*)
		                   (*---------------------------*)
				           (*-----------*)
					       (*----*)