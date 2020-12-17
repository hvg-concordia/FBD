(* ========================================================================= *)
(* File Name: Nuclear_Power_Plant_FBD.sml	          	                                     *)
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
          "arithmeticTheory","boolTheory", "listSyntax", "ETreeTheory", "FBDTheory"];

open HolKernel Parse boolLib bossLib limTheory arithmeticTheory realTheory prim_recTheory
     real_probabilityTheory seqTheory pred_setTheory res_quanTheory sortingTheory res_quanTools
     listTheory transcTheory rich_listTheory pairTheory combinTheory realLib  optionTheory
     dep_rewrite util_probTheory extrealTheory real_measureTheory real_sigmaTheory indexedListsTheory
     listLib satTheory numTheory bossLib metisLib realLib numLib combinTheory arithmeticTheory
     boolTheory listSyntax ETreeTheory FBDTheory;

val _ = new_theory "Nuclear_Power_Plant_FBD";
(*---------------------------------------------------------------------------------------------------*)

				(*-------------------------------------------*)  
				(*  CASE STUDY: NUCLEAR POWER PLANT SYSTEM   *)
				(*-------------------------------------------*)

(*-----------------------------*)  
(*   SYSTEM_LEVEL FBD MODEL    *)
(*-----------------------------*)

val SYSTEM_LEVEL_FBD_BER_DEF = Define
`SYSTEM_LEVEL_FBD_BER [[l;m;s;t];[Sbwr]] [Psuccess;Pclassi;Pclassii;Pclasssiii;Pclassiv] =
 𝓕𝓑𝑬𝑻 (𝓕𝓑𝑬𝑻Ν [ ⊞ Psuccess   (𝓕𝓑 [[l;m;s;t];[Sbwr]]);
                  ⊞ Pclassi    (𝓕𝓑 [[l;m;s;t];[Sbwr]]);
		  ⊞ Pclassii   (𝓕𝓑 [[l;m;s;t];[Sbwr]]);
		  ⊞ Pclasssiii (𝓕𝓑 [[l;m;s;t];[Sbwr]]);
		  ⊞ Pclassiv   (𝓕𝓑 [[l;m;s;t];[Sbwr]])])`;

(*-----------------------------*)  
(*   FIRST_LEVEL FBD MODEL     *)
(*-----------------------------*)

val FIRST_LEVEL_FBD_BER_DEF = Define
`SYSTEM_LEVEL_FBD_BER [[l;m;s;t];[Ca;Cb];[Ra;Rb;Rc];[Ha;Hb]] [PCa;PCb;PRa;PRb;PRc;PHa;PHb] =
 𝓕𝓑𝑬𝑻 (𝓕𝓑𝑬𝑻Ν [ ⊞ PCb (𝓕𝓑 [[l;m;s;t];[Ca;Cb]]);
                  ⊞ PRb (𝓕𝓑 [⊞ PCa (𝓕𝓑 [[l;m;s;t];[Ca;Cb]]); [Ra;Rb;Rc]]);
		  ⊞ PRc (𝓕𝓑 [⊞ PCa (𝓕𝓑 [[l;m;s;t];[Ca;Cb]]); [Ra;Rb;Rc]]);
                  ⊞ PHa (𝓕𝓑 ([⊞ PRa (𝓕𝓑 [⊞ PCa (𝓕𝓑 [[l;m;s;t];[Ca;Cb]]); [Ra;Rb;Rc]]);[Ha;Hb]]));
		  ⊞ PHb (𝓕𝓑 ([⊞ PRa (𝓕𝓑 [⊞ PCa (𝓕𝓑 [[l;m;s;t];[Ca;Cb]]); [Ra;Rb;Rc]]);[Ha;Hb]]))])`;

(*------------------------------*)  
(*   MULTIPLE_LEVELS FBD MODEL  *)
(*------------------------------*)

val WCa_DEF = Define
`WCa [l; m; s; t; Ca] = 𝓕𝓑 [[l; m; s; t];[Ca]]`;

val WCb_DEF = Define
`WCb [l; m; s; t; Cb] = 𝓕𝓑 [[l; m; s; t];[Cb]]`;

val WYa_DEF = Define
`WYa [l; m; s; t; Ca; Ya] = 𝓕𝓑Ν [[WCa [l; m; s; t; Ca]];[[Ya]]]`;
  
val WYb_DEF = Define
`WYb [l; m; s; t; Ca; Yb] = 𝓕𝓑Ν [[WCa [l; m; s; t; Ca]];[[Yb]]]`;

val WYc_DEF = Define
`WYc [l; m; s; t; Ca; Yc] = 𝓕𝓑Ν [[WCa [l; m; s; t; Ca]];[[Yc]]]`;

val WQa_DEF = Define
`WQa [l; m; s; t; Ca; Ya; Qa] = 𝓕𝓑Ν [[WYa [l; m; s; t; Ca; Ya]];[[Qa]]]`;

val WQb_DEF = Define
`WQb [l; m; s; t; Ca; Ya; Qb] = 𝓕𝓑Ν [[WYa [l; m; s; t; Ca; Ya]];[[Qb]]]`;

val WUa_DEF = Define
`WUa [l; m; s; t; Ca; Ya; Yc; Qb; Ua] =
 𝓕𝓑Ν [[WQb [l; m; s; t; Ca; Ya; Qb] ++ WYc [l; m; s; t; Ca; Yc]];[[Ua]]]`;

val WUb_DEF = Define
`WUb [l; m; s; t; Ca; Ya; Yc; Qb; Ub] =
 𝓕𝓑Ν [[WQb [l; m; s; t; Ca; Ya; Qb] ++ WYc [l; m; s; t; Ca; Yc]];[[Ub]]]`;

val WZa_DEF = Define
`WZa [l; m; s; t; Ca; Ya; Yc; Qb; Ub; Za] =
 𝓕𝓑Ν [[WQb [l; m; s; t; Ca; Ya; Qb] ++ WYc [l; m; s; t; Ca; Yc]];[[Ub]];[[Za]]]`;

val WZb_DEF = Define
`WZb[l; m; s; t; Ca; Ya; Yc; Qb; Ub; Zb] =
 𝓕𝓑Ν [[WQb [l; m; s; t; Ca; Ya; Qb] ++ WYc [l; m; s; t; Ca; Yc]];[[Ub]];[[Zb]]]`;

val WVa_DEF = Define
`WVa [l; m; s; t; Ca; Ya; Yc; Qb; Ub; Za; Va] =
 𝓕𝓑Ν [[WQb [l; m; s; t; Ca; Ya; Qb] ++ WYc [l; m; s; t; Ca; Yc]];[[Ub]];[[Za]];[[Va]]]`;

val WVb_DEF = Define
`WVb [l; m; s; t; Ca; Ya; Yc; Qb; Ub; Za; Vb] =
 𝓕𝓑Ν [[WQb [l; m; s; t; Ca; Ya; Qb] ++ WYc [l; m; s; t; Ca; Yc]];[[Ub]];[[Za]];[[Vb]]]`;

val WEa_DEF = Define
`WEa [l; m; s; t; Ca; Yb; Ea] = 𝓕𝓑Ν [[WYb [l; m; s; t; Ca; Yb]];[[Ea]]]`;

val WEb_DEF = Define
`WEb [l; m; s; t; Ca; Yb; Eb] = 𝓕𝓑Ν [[WYb [l; m; s; t; Ca; Yb]];[[Eb]]]`;

val WIa_DEF = Define
`WIa [l; m; s; t; Ca; Yb; Ea; Ia] = 𝓕𝓑Ν [[WYb [l; m; s; t; Ca; Yb]];[[Ea]];[[Ia]]]`;

val WIb_DEF = Define
`WIb [l; m; s; t; Ca; Yb; Ea; Ib] = 𝓕𝓑Ν [[WYb [l; m; s; t; Ca; Yb]];[[Ea]];[[Ib]]]`;

val WXa_DEF = Define
`WXa [l; m; s; t; Ca; Ya; Yc; Qa; Yb; Qb; Ua; Ub; Va; Za; Ea; Ia; Xa] =
 𝓕𝓑Ν [[WQa [l; m; s; t; Ca; Ya; Qa] ++ WUa [l; m; s; t; Ca; Ya; Yc; Qb; Ua] ++
        WVa [l; m; s; t; Ca; Ya; Yc; Qb; Ub; Za; Va] ++
	WIa [l; m; s; t; Ca; Yb; Ea; Ia]];[[Xa]]]`;

val WXb_DEF = Define
`WXb [l; m; s; t; Ca; Ya; Yc; Qa; Yb; Qb; Ua; Ub; Va; Za; Ea; Ia; Xb] =
 𝓕𝓑Ν [[WQa [l; m; s; t; Ca; Ya; Qa] ++ WUa [l; m; s; t; Ca; Ya; Yc; Qb; Ua] ++
        WVa [l; m; s; t; Ca; Ya; Yc; Qb; Ub; Za; Va] ++ WIa [l; m; s; t; Ca; Yb; Ea; Ia]];[[Xb]]]`;

val WWa_DEF = Define
`WWa [l; m; s; t; Ca; Yb; Ea; Ia; Wa; Qa; Qb; Ua; Ub; Va; Xb; Ya; Yc; Za] =
𝓕𝓑Ν [[WXb [l; m; s; t; Ca; Ya; Yc; Qa; Yb; Qb; Ua; Ub; Va; Za; Ea; Ia; Xb]];[[Wa]]]`;

val WWb_DEF = Define
`WWb [l; m; s; t; Ca; Yb; Ea; Ia; Wb; Qa; Qb; Ua; Ub; Va; Xb; Ya; Yc; Za] =
𝓕𝓑Ν [[WXb [l; m; s; t; Ca; Ya; Yc; Qa; Yb; Qb; Ua; Ub; Va; Za; Ea; Ia; Xb]];[[Wb]]]`;
(*--------------------------------------------------------------------------------------------------*)

(*-------------------------------*)  
(* MULTIPLE_LEVELS FBD OUTCOMES  *)
(*-------------------------------*)

val OUTCOME_SUCCESS_BWR_DEF = Define
`OUTCOME_SUCCESS_BWR [l; m; s; t; Ca; Yb; Ea; Ia; Wa; Qa; Qb; Ua; Ub; Va; Xb; Ya; Yc; Za; Xa]  =
𝓕𝓑𝑬𝑻 (𝓕𝓑𝑬𝑻Ν [WXa [l; m; s; t; Ca; Ya; Yc; Qa; Yb; Qb; Ua; Ub; Va; Za; Ea; Ia; Xa];
     	        WWa [l; m; s; t; Ca; Yb; Ea; Ia; Wa; Qa; Qb; Ua; Ub; Va; Xb; Ya; Yc; Za] ])`;
(*--------------------------------------------------------------------------------------------------*)

val OUTCOME_CLASS_I_BWR_DEF = Define
`OUTCOME_CLASS_I_BWR [l; m; s; t; Ca; Ya; Yc; Qb; Ub; Za; Vb; Zb] =
𝓕𝓑𝑬𝑻 (𝓕𝓑𝑬𝑻Ν [WVb [l; m; s; t; Ca; Ya; Yc; Qb; Ub; Za; Vb];
                WZb [l; m; s; t; Ca; Ya; Yc; Qb; Ub; Zb]])`;
(*--------------------------------------------------------------------------------------------------*)

val OUTCOME_CLASS_II_BWR_DEF = Define
`OUTCOME_CLASS_II_BWR [l; m; s; t; Ca; Yb; Ea; Ia; Wb; Qa; Qb; Ua; Ub; Va; Xb; Ya; Yc; Za]
= 𝓕𝓑𝑬𝑻 (WWb [l; m; s; t; Ca; Yb; Ea; Ia; Wb; Qa; Qb; Ua; Ub; Va; Xb; Ya; Yc; Za])`;
(*--------------------------------------------------------------------------------------------------*)

val OUTCOME_CLASS_III_BWR_DEF = Define
`OUTCOME_CLASS_III_BWR [l; m; s; t; Ca; Yb; Eb; Ea; Ib]  = 
     𝓕𝓑𝑬𝑻 (𝓕𝓑𝑬𝑻Ν [WEb [l; m; s; t; Ca; Yb; Eb]; WIb [l; m; s; t; Ca; Yb; Ea; Ib] ])`;	      
(*--------------------------------------------------------------------------------------------------*)

val OUTCOME_CLASS_IV_BWR_DEF = Define
`OUTCOME_CLASS_IV_BWR [l; m; s; t; Cb] = 𝓕𝓑𝑬𝑻  (WCb [l; m; s; t; Cb])`;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

				(*-------------------------------------*)  
				(*   OUTCOMES PROBABILISTIC ANALYSIS   *)
				(*-------------------------------------*)
				
(*---------------------------*)   
(* Probability of CLASS III  *)
(*---------------------------*)

val PROB_OUTCOME_CLASS_III_BWR = store_thm("PROB_OUTCOME_CLASS_III_BWR",
``!p l m s t Ca Cb Ya Yb Ea Eb Ia Ib.
    prob_space p /\
    disjoint
      (set
         (MAP (λa. PATH p a)
            [[Eb; Yb; Ca; l]; [Eb; Yb; Ca; m]; [Eb; Yb; Ca; s];
             [Eb; Yb; Ca; t]; [Ea; Ib; Yb; Ca; l]; [Ea; Ib; Yb; Ca; m];
             [Ea; Ib; Yb; Ca; s]; [Ea; Ib; Yb; Ca; t]])) /\
    ALL_DISTINCT
      (MAP (λa. PATH p a)
           [[Eb; Yb; Ca; l]; [Eb; Yb; Ca; m]; [Eb; Yb; Ca; s];
            [Eb; Yb; Ca; t]; [Ea; Ib; Yb; Ca; l]; [Ea; Ib; Yb; Ca; m];
            [Ea; Ib; Yb; Ca; s]; [Ea; Ib; Yb; Ca; t]])    /\
    (∀x'.
         MEM x'[Eb; Yb; Ca; l; Eb; Yb; Ca; m; Eb; Yb; Ca; s; Eb; Yb; Ca; t; Ib; Ea;
                Yb; Ca; l; Ib; Ea; Yb; Ca; m; Ib; Ea; Yb; Ca; s; Ib; Ea; Yb; Ca; t] ⇒ x' ∈ events p) /\
    (MUTUAL_INDEP p
      [Eb; Yb; Ca; l; Eb; Yb; Ca; m; Eb; Yb; Ca; s; Eb; Yb; Ca; t; Ea;
       Ib; Yb; Ca; l; Ea; Ib; Yb; Ca; m; Ea; Ib; Yb; Ca; s; Ea; Ib; Yb; Ca; t]) ==>

  prob p (OUTCOME_CLASS_III_BWR [l; m; s; t; Ca; Yb; Eb; Ea; Ib])  =
  prob p Eb * prob p Yb * prob p Ca * prob p l +
        prob p Eb * prob p Yb * prob p Ca * prob p m +
        prob p Eb * prob p Yb * prob p Ca * prob p s +
        prob p Eb * prob p Yb * prob p Ca * prob p t +
        prob p Ea * prob p Ib * prob p Yb * prob p Ca * prob p l +
        prob p Ea * prob p Ib * prob p Yb * prob p Ca * prob p m +
        prob p Ea * prob p Ib * prob p Yb * prob p Ca * prob p s +
        prob p Ea * prob p Ib * prob p Yb * prob p Ca * prob p t ``,			

rw [OUTCOME_CLASS_III_BWR_DEF]
\\ rw [WEb_DEF, WIb_DEF, WYb_DEF, WEa_DEF, WCa_DEF]
\\ sg `(𝓕𝓑𝑬𝑻
             (𝓕𝓑𝑬𝑻Ν
                [𝓕𝓑Ν [[𝓕𝓑Ν [[𝓕𝓑 [[l; m; s; t]; [Ca]]]; [[Yb]]]]; [[Eb]]];
                 𝓕𝓑Ν
                   [[𝓕𝓑Ν [[𝓕𝓑 [[l; m; s; t]; [Ca]]]; [[Yb]]]]; [[Ea]];
                    [[Ib]]]])) =
          (Eb ∩ (Yb ∩ (Ca ∩ l)) ∪
           (Eb ∩ (Yb ∩ (Ca ∩ m)) ∪
            (Eb ∩ (Yb ∩ (Ca ∩ s)) ∪ (Eb ∩ (Yb ∩ (Ca ∩ t)) ∪ ∅))) ∪
           (Ea ∩ (Ib ∩ (Yb ∩ (Ca ∩ l))) ∪
            (Ea ∩ (Ib ∩ (Yb ∩ (Ca ∩ m))) ∪
             (Ea ∩ (Ib ∩ (Yb ∩ (Ca ∩ s))) ∪
              (Ea ∩ (Ib ∩ (Yb ∩ (Ca ∩ t))) ∪ ∅))) ∪ ∅))`
   >-(EVAL_TAC)
\\ POP_ORW
\\ rw [INTER_ASSOC, UNION_OVER_INTER, UNION_ASSOC]
\\ sg `Eb ∩ Yb ∩ Ca ∩ l ∪ Eb ∩ Yb ∩ Ca ∩ m ∪ Eb ∩ Yb ∩ Ca ∩ s ∪
           Eb ∩ Yb ∩ Ca ∩ t ∪ Ea ∩ Ib ∩ Yb ∩ Ca ∩ l ∪ Ea ∩ Ib ∩ Yb ∩ Ca ∩ m ∪
           Ea ∩ Ib ∩ Yb ∩ Ca ∩ s ∪ Ea ∩ Ib ∩ Yb ∩ Ca ∩ t =
   ETREE (NODE (EVENT_TREE_LIST (MAP (λa. ET_PATH p a)
   [[Eb;Yb;Ca;l];[Eb;Yb;Ca;m];[Eb;Yb;Ca;s];[Eb;Yb;Ca;t];[Ea;Ib;Yb;Ca;l];
    [Ea;Ib;Yb;Ca;m];[Ea;Ib;Yb;Ca;s];[Ea;Ib;Yb;Ca;t]])))`
  >-( rw [ET_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
      \\ rw [UNION_ASSOC])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NODE_OF_ET_PATHS]
\\ fs []
\\ sg `(∀z.
              z = [Eb; Yb; Ca; l] ∨ z = [Eb; Yb; Ca; m] ∨
              z = [Eb; Yb; Ca; s] ∨ z = [Eb; Yb; Ca; t] ∨
              z = [Ea; Ib; Yb; Ca; l] ∨ z = [Ea; Ib; Yb; Ca; m] ∨
              z = [Ea; Ib; Yb; Ca; s] ∨ z = [Ea; Ib; Yb; Ca; t] ⇒
              ~NULL z)`
   >-( metis_tac [NULL])
\\ sg `∀x'.
             x' = Eb ∨ x' = Yb ∨ x' = Ca ∨ x' = l ∨ x' = Eb ∨ x' = Yb ∨
             x' = Ca ∨ x' = m ∨ x' = Eb ∨ x' = Yb ∨ x' = Ca ∨ x' = s ∨
             x' = Eb ∨ x' = Yb ∨ x' = Ca ∨ x' = t ∨ x' = Ea ∨ x' = Ib ∨
             x' = Yb ∨ x' = Ca ∨ x' = l ∨ x' = Ea ∨ x' = Ib ∨ x' = Yb ∨
             x' = Ca ∨ x' = m ∨ x' = Ea ∨ x' = Ib ∨ x' = Yb ∨ x' = Ca ∨
             x' = s ∨ x' = Ea ∨ x' = Ib ∨ x' = Yb ∨ x' = Ca ∨ x' = t ⇒
             x' ∈ events p `
   >-( metis_tac [])
\\ REWRITE_TAC [PROB_LIST_DEF, PROD_LIST_DEF, SUM_LIST_DEF]
\\ sg `prob p Eb * (prob p Yb * (prob p Ca * (prob p l * 1))) +
        (prob p Eb * (prob p Yb * (prob p Ca * (prob p m * 1))) +
         (prob p Eb * (prob p Yb * (prob p Ca * (prob p s * 1))) +
          (prob p Eb * (prob p Yb * (prob p Ca * (prob p t * 1))) +
           (prob p Ea *
            (prob p Ib * (prob p Yb * (prob p Ca * (prob p l * 1)))) +
            (prob p Ea *
             (prob p Ib * (prob p Yb * (prob p Ca * (prob p m * 1)))) +
             (prob p Ea *
              (prob p Ib * (prob p Yb * (prob p Ca * (prob p s * 1)))) +
              (prob p Ea *
               (prob p Ib * (prob p Yb * (prob p Ca * (prob p t * 1)))) + 0)))))))  =
        prob p Eb * prob p Yb * prob p Ca * prob p l +
        prob p Eb * prob p Yb * prob p Ca * prob p m +
        prob p Eb * prob p Yb * prob p Ca * prob p s +
        prob p Eb * prob p Yb * prob p Ca * prob p t +
        prob p Ea * prob p Ib * prob p Yb * prob p Ca * prob p l +
        prob p Ea * prob p Ib * prob p Yb * prob p Ca * prob p m +
        prob p Ea * prob p Ib * prob p Yb * prob p Ca * prob p s +
        prob p Ea * prob p Ib * prob p Yb * prob p Ca * prob p t `
   >-(REAL_ARITH_TAC)
\\ metis_tac []);   
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*-----------------------------------------------------*)   
(* Probability of CLASS III  Exponential Distribution  *)
(*-----------------------------------------------------*)

val PROB_OUTCOME_CLASS_III_BWR_EXP_DISTRIBUTION  = store_thm("PROB_OUTCOME_CLASS_III_BWR_EXP_DISTRIBUTION",
``!p l m s T C Yb E I FR_l FR_m FR_s FR_T FR_C FR_Yb FR_E FR_I t.
    prob_space p /\ 0 <= t /\
    EXP_ET_DISTRIB p l FR_l /\ EXP_ET_DISTRIB p m FR_m /\ EXP_ET_DISTRIB p s FR_s /\ EXP_ET_DISTRIB p T FR_T
 /\ EXP_ET_DISTRIB p C FR_C  /\ EXP_ET_DISTRIB p Yb FR_Yb  /\ EXP_ET_DISTRIB p E FR_E  /\ EXP_ET_DISTRIB p I FR_I
 /\ disjoint
      (set
         (MAP (λa. PATH p a)
           [[↓ p E t; ↓ p Yb t; ↑ p C t; ↓ p l t];
	    [↓ p E t ; ↓ p Yb t;  ↑ p C t; ↓ p m t];
	    [↓ p E t; ↓ p Yb t;  ↑ p C t; ↓ p s t];
            [↓ p E t; ↓ p Yb t;  ↑ p C t; ↓ p T t];
	    [↑ p E t ; ↓ p I t; ↓ p Yb t;  ↑ p C t; ↓ p l t];
	    [↑ p E t ; ↓ p I t;  ↓ p Yb t;  ↑ p C t; ↓ p m t];
            [↑ p E t ; ↓ p I t;  ↓ p Yb t;  ↑ p C t; ↓ p s t];
	    [↑ p E t ; ↓ p I t;  ↓ p Yb t;  ↑ p C t; ↓ p T t]])) /\
    ALL_DISTINCT
      (MAP (λa. PATH p a)
         [[↓ p E t; ↓ p Yb t;  ↑ p C t; ↓ p l t];
	  [↓ p E t; ↓ p Yb t;  ↑ p C t; ↓ p m t];
	  [↓ p E t; ↓ p Yb t;  ↑ p C t; ↓ p s t];
	  [↓ p E t; ↓ p Yb t;  ↑ p C t; ↓ p T t];
          [↑ p E t ; ↓ p I t;  ↓ p Yb t;  ↑ p C t; ↓ p l t];
	  [↑ p E t ; ↓ p I t;  ↓ p Yb t;  ↑ p C t; ↓ p m t];
	  [↑ p E t ; ↓ p I t;  ↓ p Yb t;  ↑ p C t; ↓ p s t];
          [↑ p E t ; ↓ p I t;  ↓ p Yb t;  ↑ p C t; ↓ p T t]]) /\
    (∀x'.
         MEM x'[↓ p E t; ↓ p Yb t; ↑ p C t ; ↓ p l t;
	        ↓ p E t; ↓ p Yb t;  ↑ p C t; ↓ p m t;
		↓ p E t; ↓ p Yb t;  ↑ p C t; ↓ p s t;
		↓ p E t; ↓ p Yb t;  ↑ p C t; ↓ p T t;
		↑ p E t ; ↓ p I t;  ↓ p Yb t;  ↑ p C t; ↓ p l t;
		↑ p E t ; ↓ p I t;  ↓ p Yb t;  ↑ p C t; ↓ p m t;
		↑ p E t ; ↓ p I t;  ↓ p Yb t;  ↑ p C t; ↓ p s t;
		↑ p E t ; ↓ p I t;  ↓ p Yb t;  ↑ p C t; ↓ p T t;  ↓ p C t] ⇒ x' ∈ events p) /\
    (MUTUAL_INDEP p
      [↓ p E t; ↓ p Yb t;  ↑ p C t; ↓ p l t;
       ↓ p E t; ↓ p Yb t;  ↑ p C t; ↓ p m t;
       ↓ p E t; ↓ p Yb t;  ↑ p C t; ↓ p s t;
       ↓ p E t; ↓ p Yb t ;  ↑ p C t; ↓ p T t;
       ↑ p E t ; ↓ p I t;  ↓ p Yb t; ↑ p C t ; ↓ p l t;
       ↑ p E t ; ↓ p I t;  ↓ p Yb t;  ↑ p C t; ↓ p m t;
       ↑ p E t ; ↓ p I t;  ↓ p Yb t;  ↑ p C t; ↓ p s t;
       ↑ p E t;  ↓ p I t;  ↓ p Yb t;  ↑ p C t; ↓ p T t])
  ==>
  prob p (OUTCOME_CLASS_III_BWR [↓ p l t; ↓ p m t; ↓ p s t; ↓ p T t; ↑ p C t; ↓ p Yb t; ↓ p E t; ↑ p E t; ↓ p I t]) =
	 (1 - exp (-FR_E * t)) * (1 - exp (-FR_Yb * t)) * exp (-FR_C * t) * (1 - exp (-FR_l * t)) +
         (1 - exp (-FR_E * t)) * (1 - exp (-FR_Yb * t)) * exp (-FR_C * t) * (1 - exp (-FR_m * t)) +
         (1 - exp (-FR_E * t)) * (1 - exp (-FR_Yb * t)) * exp (-FR_C * t) * (1 - exp (-FR_s * t))  +
         (1 - exp (-FR_E * t)) * (1 - exp (-FR_Yb * t)) * exp (-FR_C * t) * (1 - exp (-FR_T * t)) +
    exp (-FR_E * t) * (1 - exp (-FR_I * t)) * (1 - exp (-FR_Yb * t)) * exp (-FR_C * t) * (1 - exp (-FR_l * t)) +
    exp (-FR_E * t) * (1 - exp (-FR_I * t)) * (1 - exp (-FR_Yb * t)) * exp (-FR_C * t) * (1 - exp (-FR_m * t)) +
    exp (-FR_E * t) * (1 - exp (-FR_I * t)) * (1 - exp (-FR_Yb * t)) * exp (-FR_C * t) * (1 - exp (-FR_s * t)) +
    exp (-FR_E * t) * (1 - exp (-FR_I * t)) * (1 - exp (-FR_Yb * t)) * exp (-FR_C * t) * (1 - exp (-FR_T * t))``,

rw []
\\ DEP_REWRITE_TAC [PROB_OUTCOME_CLASS_III_BWR]
\\ fs []
\\ CONJ_TAC
   >-(metis_tac [])
\\ rw [SUCCESS_DEF, FAIL_DEF]
\\ sg `!X. prob p (PREIMAGE X {y | y ≤ Normal t} ∩ p_space p) = distribution p X {y | y ≤ Normal t}`
   >-(metis_tac [distribution_def])
\\ fs []
\\ rw [GSYM CDF_DEF]
\\ rw [GSYM SUCCESS_DEF]
\\ rw [GSYM SUCCESS_EQ_FAIL]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw [FAIL_DEF]
\\ rw [GSYM CDF_DEF]
\\ rw [REAL_ADD_ASSOC]
\\ rw [REAL_SUB_ADD]
\\ fs [EXP_ET_DISTRIB_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*---------------------------*)   
(* Probability of CLASS IV   *)
(*---------------------------*)

val PROB_OUTCOME_CLASS_IV_BWR = store_thm("PROB_OUTCOME_CLASS_IV_BWR",
``!p l m s t Ca Cb.
           prob_space p /\
	 disjoint (set (MAP (λa. PATH p a) [[Cb; l]; [Cb; m]; [Cb; s]; [Cb; t]])) ∧
         ALL_DISTINCT (MAP (λa. PATH p a) [[Cb; l]; [Cb; m]; [Cb; s]; [Cb; t]]) /\
	 (∀x'.  x' = Cb ∨ x' = l ∨ x' = m  ∨ x' = s ∨ x' = t ⇒ x' ∈ events p) /\
	 MUTUAL_INDEP p [Cb; l; Cb; m; Cb; s; Cb; t]  ==> 
prob p (OUTCOME_CLASS_IV_BWR [l; m; s; t; Cb]) =
prob p Cb * prob p l  + prob p Cb * prob p m + prob p Cb * prob p s + prob p Cb * prob p t``,

rw [OUTCOME_CLASS_IV_BWR_DEF, WCb_DEF]
\\ sg ` 𝓕𝓑𝑬𝑻 (𝓕𝓑 [[l; m; s; t]; [Cb]]) = Cb ∩ l ∪ (Cb ∩ m ∪ (Cb ∩ s ∪ (Cb ∩ t ∪ ∅)))`
   >-(EVAL_TAC)
\\ POP_ORW
\\ rw [INTER_ASSOC, UNION_OVER_INTER, UNION_ASSOC]
\\ sg ` Cb ∩ l ∪ Cb ∩ m ∪ Cb ∩ s ∪ Cb ∩ t =
   ETREE (NODE (EVENT_TREE_LIST (MAP (λa. ET_PATH p a)
   [[Cb;l]; [Cb;m]; [Cb;s]; [Cb;t]])))`
  >-( rw [ET_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
      \\ rw [UNION_ASSOC])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NODE_OF_ET_PATHS]
\\ fs []
\\ sg `(∀z. z = [Cb; l] ∨ z = [Cb; m] ∨ z = [Cb; s] ∨ z = [Cb; t] ⇒ ~NULL z)`
   >-( metis_tac [NULL])
\\ sg ` (∀x'.
              x' = Cb ∨ x' = l ∨ x' = Cb ∨ x' = m ∨ x' = Cb ∨ x' = s ∨
              x' = Cb ∨ x' = t ⇒
              x' ∈ events p)`
   >-( metis_tac [])
\\ REWRITE_TAC [PROB_LIST_DEF, PROD_LIST_DEF, SUM_LIST_DEF]
\\ sg `prob p Cb * (prob p l * 1) +
        (prob p Cb * (prob p m * 1) +
         (prob p Cb * (prob p s * 1) + (prob p Cb * (prob p t * 1) + 0))) =
       prob p Cb * prob p l  + prob p Cb * prob p m + prob p Cb * prob p s + prob p Cb * prob p t`
   >-(REAL_ARITH_TAC)
\\ metis_tac []);   
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*-----------------------------------------------------*)   
(*  Probability of CLASS IV  Exponential Distribution  *)
(*-----------------------------------------------------*)

val PROB_OUTCOME_CLASS_IV_BWR_EXP_DISTRIBUTION = store_thm("PROB_OUTCOME_CLASS_IV_BWR_EXP_DISTRIBUTION",
``!p l m s T C t FR_l FR_m FR_s FR_T FR_C.
         prob_space p /\ 0 <= t /\
         EXP_ET_DISTRIB p l FR_l /\ EXP_ET_DISTRIB p m FR_m /\ EXP_ET_DISTRIB p s FR_s /\ EXP_ET_DISTRIB p T FR_T
         /\ EXP_ET_DISTRIB p C FR_C  /\
	 disjoint (set (MAP (λa. PATH p a) [[↓ p C t; ↓ p l t]; [↓ p C t; ↓ p m t];
	                                    [↓ p C t; ↓ p s t]; [↓ p C t; ↓ p T t]])) ∧
         ALL_DISTINCT (MAP (λa. PATH p a) [[↓ p C t; ↓ p l t]; [↓ p C t; ↓ p m t];
	                                    [↓ p C t; ↓ p s t]; [↓ p C t; ↓ p T t]]) /\
	 (∀x'.  x' = ↓ p C t ∨ x' = ↓ p l t ∨ x' =  ↓ p m t ∨ x' = ↓ p s t ∨ x' = ↓ p T t ⇒ x' ∈ events p) /\
	 MUTUAL_INDEP p [↓ p C t; ↓ p l t; ↓ p C t; ↓ p m t; ↓ p C t; ↓ p s t; ↓ p C t; ↓ p T t]  ==> 
prob p (OUTCOME_CLASS_IV_BWR [↓ p l t; ↓ p m t; ↓ p s t; ↓ p T t; ↓ p C t]) =
(1 − exp (-FR_C * t)) * (1 − exp (-FR_l * t)) + (1 − exp (-FR_C * t)) * (1 − exp (-FR_m * t)) +
(1 − exp (-FR_C * t)) * (1 − exp (-FR_s * t)) + (1 − exp (-FR_C * t)) * (1 − exp (-FR_T * t))``,

rw []
\\ DEP_REWRITE_TAC [PROB_OUTCOME_CLASS_IV_BWR]
\\ fs []
\\ CONJ_TAC
   >-(metis_tac [])
\\ rw [SUCCESS_DEF, FAIL_DEF]
\\ sg `!X. prob p (PREIMAGE X {y | y ≤ Normal t} ∩ p_space p) = distribution p X {y | y ≤ Normal t}`
   >-(metis_tac [distribution_def])
\\ fs []
\\ rw [GSYM CDF_DEF]
\\ rw [GSYM SUCCESS_DEF]
\\ rw [GSYM SUCCESS_EQ_FAIL]
\\ DEP_REWRITE_TAC [PROB_COMPL]
\\ rw [FAIL_DEF]
\\ rw [GSYM CDF_DEF]
\\ rw [REAL_ADD_ASSOC]
\\ rw [REAL_SUB_ADD]
\\ fs [EXP_ET_DISTRIB_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*---------------------------*)   
(* Probability of CLASS I    *)
(*---------------------------*)

val PROB_OUTCOME_CLASS_I_BWR = store_thm("PROB_OUTCOME_CLASS_I_BWR",
``!p l m s t Ca Ya Yc Qb Ub Za Vb Zb.
          prob_space p /\
	  disjoint
           (set
              (MAP (λa. PATH p a)
                 [[Ub; Za; Vb; Qb; Ya; Ca; l]; [Ub; Za; Vb; Qb; Ya; Ca; m];
                  [Ub; Za; Vb; Qb; Ya; Ca; s]; [Ub; Za; Vb; Qb; Ya; Ca; t];
                  [Ub; Za; Vb; Yc; Ca; l]; [Ub; Za; Vb; Yc; Ca; m];
                  [Ub; Za; Vb; Yc; Ca; s]; [Ub; Za; Vb; Yc; Ca; t];
                  [Ub; Zb; Qb; Ya; Ca; l]; [Ub; Zb; Qb; Ya; Ca; m];
                  [Ub; Zb; Qb; Ya; Ca; s]; [Ub; Zb; Qb; Ya; Ca; t];
                  [Ub; Zb; Yc; Ca; l]; [Ub; Zb; Yc; Ca; m];
                  [Ub; Zb; Yc; Ca; s]; [Ub; Zb; Yc; Ca; t]])) ∧
         ALL_DISTINCT
           (MAP (λa. PATH p a)
              [[Ub; Za; Vb; Qb; Ya; Ca; l]; [Ub; Za; Vb; Qb; Ya; Ca; m];
               [Ub; Za; Vb; Qb; Ya; Ca; s]; [Ub; Za; Vb; Qb; Ya; Ca; t];
               [Ub; Za; Vb; Yc; Ca; l]; [Ub; Za; Vb; Yc; Ca; m];
               [Ub; Za; Vb; Yc; Ca; s]; [Ub; Za; Vb; Yc; Ca; t];
               [Ub; Zb; Qb; Ya; Ca; l]; [Ub; Zb; Qb; Ya; Ca; m];
               [Ub; Zb; Qb; Ya; Ca; s]; [Ub; Zb; Qb; Ya; Ca; t];
               [Ub; Zb; Yc; Ca; l]; [Ub; Zb; Yc; Ca; m]; [Ub; Zb; Yc; Ca; s];
               [Ub; Zb; Yc; Ca; t]]) /\
         (∀x'. x' = Ub ∨ x' = Za ∨ x' = Vb ∨ x' = Qb ∨ x' = Ya ∨ x' = Ca ∨
              x' = l ∨  x' = m ∨  x' = s ∨  x' = t ∨ x' = Yc ∨ x' = Ub ∨
	      x' = Zb ∨ x' = Ya  ⇒ x' ∈ events p) /\
	 MUTUAL_INDEP p
           [Ub; Za; Vb; Qb; Ya; Ca; l; Ub; Za; Vb; Qb; Ya; Ca; m; Ub; Za; Vb;
            Qb; Ya; Ca; s; Ub; Za; Vb; Qb; Ya; Ca; t; Ub; Za; Vb; Yc; Ca; l;
            Ub; Za; Vb; Yc; Ca; m; Ub; Za; Vb; Yc; Ca; s; Ub; Za; Vb; Yc; Ca;
            t; Ub; Zb; Qb; Ya; Ca; l; Ub; Zb; Qb; Ya; Ca; m; Ub; Zb; Qb; Ya;
            Ca; s; Ub; Zb; Qb; Ya; Ca; t; Ub; Zb; Yc; Ca; l; Ub; Zb; Yc; Ca;
            m; Ub; Zb; Yc; Ca; s; Ub; Zb; Yc; Ca; t]   ==> 
      prob p (OUTCOME_CLASS_I_BWR [l; m; s; t; Ca; Ya; Yc; Qb; Ub; Za; Vb; Zb])  =
      prob p Ub * prob p Za * prob p Vb * prob p Qb * prob p Ya * prob p Ca * prob p l  +
      prob p Ub * prob p Za * prob p Vb * prob p Qb * prob p Ya * prob p Ca * prob p m  +
      prob p Ub * prob p Za * prob p Vb * prob p Qb * prob p Ya * prob p Ca * prob p s  +
      prob p Ub * prob p Za * prob p Vb * prob p Qb * prob p Ya * prob p Ca * prob p t  +
      prob p Ub * prob p Za * prob p Vb * prob p Yc * prob p Ca * prob p l   +
      prob p Ub * prob p Za * prob p Vb * prob p Yc * prob p Ca * prob p m   +
      prob p Ub * prob p Za * prob p Vb * prob p Yc * prob p Ca * prob p s   +
      prob p Ub * prob p Za * prob p Vb * prob p Yc * prob p Ca * prob p t   +
      prob p Ub * prob p Zb * prob p Qb * prob p Ya * prob p Ca * prob p l   +
      prob p Ub * prob p Zb * prob p Qb * prob p Ya * prob p Ca * prob p m   +
      prob p Ub * prob p Zb * prob p Qb * prob p Ya * prob p Ca * prob p s   +
      prob p Ub * prob p Zb * prob p Qb * prob p Ya * prob p Ca * prob p t   +
      prob p Ub * prob p Zb * prob p Yc * prob p Ca * prob p l  +
      prob p Ub * prob p Zb * prob p Yc * prob p Ca * prob p m  +
      prob p Ub * prob p Zb * prob p Yc * prob p Ca * prob p s  +
      prob p Ub * prob p Zb * prob p Yc * prob p Ca * prob p t``,

rw [OUTCOME_CLASS_I_BWR_DEF, WVb_DEF, WZb_DEF]
\\ sg ` (𝓕𝓑𝑬𝑻
             (𝓕𝓑𝑬𝑻Ν
                [𝓕𝓑Ν
                   [[WQb [l; m; s; t; Ca; Ya; Qb] ⧺ WYc [l; m; s; t; Ca; Yc]];
                    [[Ub]]; [[Za]]; [[Vb]]];
                 𝓕𝓑Ν
                   [[WQb [l; m; s; t; Ca; Ya; Qb] ⧺ WYc [l; m; s; t; Ca; Yc]];
                    [[Ub]]; [[Zb]]]])) =
       (Ub ∩ (Za ∩ (Vb ∩ (Qb ∩ (Ya ∩ (Ca ∩ l))))) ∪
           (Ub ∩ (Za ∩ (Vb ∩ (Qb ∩ (Ya ∩ (Ca ∩ m))))) ∪
            (Ub ∩ (Za ∩ (Vb ∩ (Qb ∩ (Ya ∩ (Ca ∩ s))))) ∪
             (Ub ∩ (Za ∩ (Vb ∩ (Qb ∩ (Ya ∩ (Ca ∩ t))))) ∪
              (Ub ∩ (Za ∩ (Vb ∩ (Yc ∩ (Ca ∩ l)))) ∪
               (Ub ∩ (Za ∩ (Vb ∩ (Yc ∩ (Ca ∩ m)))) ∪
                (Ub ∩ (Za ∩ (Vb ∩ (Yc ∩ (Ca ∩ s)))) ∪
                 (Ub ∩ (Za ∩ (Vb ∩ (Yc ∩ (Ca ∩ t)))) ∪ ∅))))))) ∪
           (Ub ∩ (Zb ∩ (Qb ∩ (Ya ∩ (Ca ∩ l)))) ∪
            (Ub ∩ (Zb ∩ (Qb ∩ (Ya ∩ (Ca ∩ m)))) ∪
             (Ub ∩ (Zb ∩ (Qb ∩ (Ya ∩ (Ca ∩ s)))) ∪
              (Ub ∩ (Zb ∩ (Qb ∩ (Ya ∩ (Ca ∩ t)))) ∪
               (Ub ∩ (Zb ∩ (Yc ∩ (Ca ∩ l))) ∪
                (Ub ∩ (Zb ∩ (Yc ∩ (Ca ∩ m))) ∪
                 (Ub ∩ (Zb ∩ (Yc ∩ (Ca ∩ s))) ∪
                  (Ub ∩ (Zb ∩ (Yc ∩ (Ca ∩ t))) ∪ ∅))))))) ∪ ∅))`
   >-(EVAL_TAC)
\\ POP_ORW
\\ rw [INTER_ASSOC, UNION_OVER_INTER, UNION_ASSOC]
\\ sg `    Ub ∩ Za ∩ Vb ∩ Qb ∩ Ya ∩ Ca ∩ l ∪
           Ub ∩ Za ∩ Vb ∩ Qb ∩ Ya ∩ Ca ∩ m ∪
           Ub ∩ Za ∩ Vb ∩ Qb ∩ Ya ∩ Ca ∩ s ∪
           Ub ∩ Za ∩ Vb ∩ Qb ∩ Ya ∩ Ca ∩ t ∪
	   Ub ∩ Za ∩ Vb ∩ Yc ∩ Ca ∩ l ∪
           Ub ∩ Za ∩ Vb ∩ Yc ∩ Ca ∩ m ∪
	   Ub ∩ Za ∩ Vb ∩ Yc ∩ Ca ∩ s ∪
           Ub ∩ Za ∩ Vb ∩ Yc ∩ Ca ∩ t ∪
	   Ub ∩ Zb ∩ Qb ∩ Ya ∩ Ca ∩ l ∪
           Ub ∩ Zb ∩ Qb ∩ Ya ∩ Ca ∩ m ∪
	   Ub ∩ Zb ∩ Qb ∩ Ya ∩ Ca ∩ s ∪
           Ub ∩ Zb ∩ Qb ∩ Ya ∩ Ca ∩ t ∪
	   Ub ∩ Zb ∩ Yc ∩ Ca ∩ l ∪
           Ub ∩ Zb ∩ Yc ∩ Ca ∩ m ∪
	   Ub ∩ Zb ∩ Yc ∩ Ca ∩ s ∪
           Ub ∩ Zb ∩ Yc ∩ Ca ∩ t =
   ETREE (NODE (EVENT_TREE_LIST (MAP (λa. ET_PATH p a)
   [[Ub; Za; Vb; Qb; Ya; Ca; l];
    [Ub; Za; Vb; Qb; Ya; Ca; m];
    [Ub; Za; Vb; Qb; Ya; Ca; s];
    [Ub; Za; Vb; Qb; Ya; Ca; t];
    [Ub; Za; Vb; Yc; Ca; l];
    [Ub; Za; Vb; Yc; Ca; m];
    [Ub; Za; Vb; Yc; Ca; s];
    [Ub; Za; Vb; Yc; Ca; t];
    [Ub; Zb; Qb; Ya; Ca; l];
    [Ub; Zb; Qb; Ya; Ca; m];
    [Ub; Zb; Qb; Ya; Ca; s];
    [Ub; Zb; Qb; Ya; Ca; t];
    [Ub; Zb; Yc; Ca; l];
    [Ub; Zb; Yc; Ca; m];
    [Ub; Zb; Yc; Ca; s];
    [Ub; Zb; Yc; Ca; t]])))`
  >-( rw [ET_PATH_DEF, EVENT_TREE_LIST_DEF, ETREE_DEF]
      \\ rw [UNION_ASSOC])
\\ POP_ORW
\\ DEP_REWRITE_TAC [PROB_NODE_OF_ET_PATHS]
\\ fs []
\\ sg `(∀z.
              z = [Ub; Za; Vb; Qb; Ya; Ca; l] ∨
              z = [Ub; Za; Vb; Qb; Ya; Ca; m] ∨
              z = [Ub; Za; Vb; Qb; Ya; Ca; s] ∨
              z = [Ub; Za; Vb; Qb; Ya; Ca; t] ∨ z = [Ub; Za; Vb; Yc; Ca; l] ∨
              z = [Ub; Za; Vb; Yc; Ca; m] ∨ z = [Ub; Za; Vb; Yc; Ca; s] ∨
              z = [Ub; Za; Vb; Yc; Ca; t] ∨ z = [Ub; Zb; Qb; Ya; Ca; l] ∨
              z = [Ub; Zb; Qb; Ya; Ca; m] ∨ z = [Ub; Zb; Qb; Ya; Ca; s] ∨
              z = [Ub; Zb; Qb; Ya; Ca; t] ∨ z = [Ub; Zb; Yc; Ca; l] ∨
              z = [Ub; Zb; Yc; Ca; m] ∨ z = [Ub; Zb; Yc; Ca; s] ∨
              z = [Ub; Zb; Yc; Ca; t] ⇒
              ~NULL z)`
   >-( metis_tac [NULL])
\\ sg `(∀x'.
              x' = Ub ∨ x' = Za ∨ x' = Vb ∨ x' = Qb ∨ x' = Ya ∨ x' = Ca ∨
              x' = l ∨ x' = Ub ∨ x' = Za ∨ x' = Vb ∨ x' = Qb ∨ x' = Ya ∨
              x' = Ca ∨ x' = m ∨ x' = Ub ∨ x' = Za ∨ x' = Vb ∨ x' = Qb ∨
              x' = Ya ∨ x' = Ca ∨ x' = s ∨ x' = Ub ∨ x' = Za ∨ x' = Vb ∨
              x' = Qb ∨ x' = Ya ∨ x' = Ca ∨ x' = t ∨ x' = Ub ∨ x' = Za ∨
              x' = Vb ∨ x' = Yc ∨ x' = Ca ∨ x' = l ∨ x' = Ub ∨ x' = Za ∨
              x' = Vb ∨ x' = Yc ∨ x' = Ca ∨ x' = m ∨ x' = Ub ∨ x' = Za ∨
              x' = Vb ∨ x' = Yc ∨ x' = Ca ∨ x' = s ∨ x' = Ub ∨ x' = Za ∨
              x' = Vb ∨ x' = Yc ∨ x' = Ca ∨ x' = t ∨ x' = Ub ∨ x' = Zb ∨
              x' = Qb ∨ x' = Ya ∨ x' = Ca ∨ x' = l ∨ x' = Ub ∨ x' = Zb ∨
              x' = Qb ∨ x' = Ya ∨ x' = Ca ∨ x' = m ∨ x' = Ub ∨ x' = Zb ∨
              x' = Qb ∨ x' = Ya ∨ x' = Ca ∨ x' = s ∨ x' = Ub ∨ x' = Zb ∨
              x' = Qb ∨ x' = Ya ∨ x' = Ca ∨ x' = t ∨ x' = Ub ∨ x' = Zb ∨
              x' = Yc ∨ x' = Ca ∨ x' = l ∨ x' = Ub ∨ x' = Zb ∨ x' = Yc ∨
              x' = Ca ∨ x' = m ∨ x' = Ub ∨ x' = Zb ∨ x' = Yc ∨ x' = Ca ∨
              x' = s ∨ x' = Ub ∨ x' = Zb ∨ x' = Yc ∨ x' = Ca ∨ x' = t ⇒ x' ∈ events p)`
   >-( metis_tac [])
\\ REWRITE_TAC [PROB_LIST_DEF, PROD_LIST_DEF, SUM_LIST_DEF]
\\ sg `prob p Ub *
        (prob p Za *
         (prob p Vb *
          (prob p Qb * (prob p Ya * (prob p Ca * (prob p l * 1)))))) +
        (prob p Ub *
         (prob p Za *
          (prob p Vb *
           (prob p Qb * (prob p Ya * (prob p Ca * (prob p m * 1)))))) +
         (prob p Ub *
          (prob p Za *
           (prob p Vb *
            (prob p Qb * (prob p Ya * (prob p Ca * (prob p s * 1)))))) +
          (prob p Ub *
           (prob p Za *
            (prob p Vb *
             (prob p Qb * (prob p Ya * (prob p Ca * (prob p t * 1)))))) +
           (prob p Ub *
            (prob p Za *
             (prob p Vb * (prob p Yc * (prob p Ca * (prob p l * 1))))) +
            (prob p Ub *
             (prob p Za *
              (prob p Vb * (prob p Yc * (prob p Ca * (prob p m * 1))))) +
             (prob p Ub *
              (prob p Za *
               (prob p Vb * (prob p Yc * (prob p Ca * (prob p s * 1))))) +
              (prob p Ub *
               (prob p Za *
                (prob p Vb * (prob p Yc * (prob p Ca * (prob p t * 1))))) +
               (prob p Ub *
                (prob p Zb *
                 (prob p Qb * (prob p Ya * (prob p Ca * (prob p l * 1))))) +
                (prob p Ub *
                 (prob p Zb *
                  (prob p Qb * (prob p Ya * (prob p Ca * (prob p m * 1))))) +
                 (prob p Ub *
                  (prob p Zb *
                   (prob p Qb * (prob p Ya * (prob p Ca * (prob p s * 1))))) +
                  (prob p Ub *
                   (prob p Zb *
                    (prob p Qb * (prob p Ya * (prob p Ca * (prob p t * 1))))) +
                   (prob p Ub *
                    (prob p Zb * (prob p Yc * (prob p Ca * (prob p l * 1)))) +
                    (prob p Ub *
                     (prob p Zb * (prob p Yc * (prob p Ca * (prob p m * 1)))) +
                     (prob p Ub *
                      (prob p Zb *
                       (prob p Yc * (prob p Ca * (prob p s * 1)))) +
                      (prob p Ub *
                       (prob p Zb *
                        (prob p Yc * (prob p Ca * (prob p t * 1)))) + 0))))))))))))))) =
      prob p Ub * prob p Za * prob p Vb * prob p Qb * prob p Ya * prob p Ca * prob p l  +
      prob p Ub * prob p Za * prob p Vb * prob p Qb * prob p Ya * prob p Ca * prob p m  +
      prob p Ub * prob p Za * prob p Vb * prob p Qb * prob p Ya * prob p Ca * prob p s  +
      prob p Ub * prob p Za * prob p Vb * prob p Qb * prob p Ya * prob p Ca * prob p t  +
      prob p Ub * prob p Za * prob p Vb * prob p Yc * prob p Ca * prob p l   +
      prob p Ub * prob p Za * prob p Vb * prob p Yc * prob p Ca * prob p m   +
      prob p Ub * prob p Za * prob p Vb * prob p Yc * prob p Ca * prob p s   +
      prob p Ub * prob p Za * prob p Vb * prob p Yc * prob p Ca * prob p t   +
      prob p Ub * prob p Zb * prob p Qb * prob p Ya * prob p Ca * prob p l   +
      prob p Ub * prob p Zb * prob p Qb * prob p Ya * prob p Ca * prob p m   +
      prob p Ub * prob p Zb * prob p Qb * prob p Ya * prob p Ca * prob p s   +
      prob p Ub * prob p Zb * prob p Qb * prob p Ya * prob p Ca * prob p t   +
      prob p Ub * prob p Zb * prob p Yc * prob p Ca * prob p l  +
      prob p Ub * prob p Zb * prob p Yc * prob p Ca * prob p m  +
      prob p Ub * prob p Zb * prob p Yc * prob p Ca * prob p s  +
      prob p Ub * prob p Zb * prob p Yc * prob p Ca * prob p t `
   >-(REAL_ARITH_TAC)
\\ metis_tac []);   
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*-----------------------------------------------------*)   
(*  Probability of CLASS I Exponential Distribution    *)
(*-----------------------------------------------------*)

val PROB_OUTCOME_CLASS_I_BWR_EXP_DISTRIBUTION = store_thm("PROB_OUTCOME_CLASS_I_BWR_EXP_DISTRIBUTION",
``!p l m s T C Ya Yc Q U Z V t  FR_l FR_m FR_s FR_T FR_C FR_Ya FR_Yc FR_Yb FR_Q FR_U FR_Z FR_V.
         prob_space p /\ 0 <= t /\
         EXP_ET_DISTRIB p l FR_l /\ EXP_ET_DISTRIB p m FR_m /\ EXP_ET_DISTRIB p s FR_s /\
	 EXP_ET_DISTRIB p T FR_T /\ EXP_ET_DISTRIB p C FR_C  /\ EXP_ET_DISTRIB p Yc FR_Yc /\
	 EXP_ET_DISTRIB p Q FR_Q /\ EXP_ET_DISTRIB p U FR_U /\ EXP_ET_DISTRIB p Z FR_Z /\
	 EXP_ET_DISTRIB p V FR_V /\ EXP_ET_SUCCESS_DISTRIB p Ya FR_Ya /\
	 EXP_ET_SUCCESS_DISTRIB p Z FR_Z /\ EXP_ET_SUCCESS_DISTRIB p C FR_C /\
	  disjoint
           (set
              (MAP (λa. PATH p a)
                 [[↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Q t; ↑ p Ya t;  ↑ p C t; ↓ p l t];
		  [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Q t; ↑ p Ya t;  ↑ p C t; ↓ p m t];
		  [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Q t; ↑ p Ya t;  ↑ p C t; ↓ p s t];
		  [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Q t; ↑ p Ya t;  ↑ p C t; ↓ p T t];
		  [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Yc t; ↑ p C t; ↓ p l t];
		  [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Yc t; ↑ p C t; ↓ p m t];
		  [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Yc t; ↑ p C t; ↓ p s t];
		  [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Yc t; ↑ p C t; ↓ p T t];
		  [↓ p U t; ↓ p Z t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p l t];
		  [↓ p U t; ↓ p Z t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p m t];
		  [↓ p U t; ↓ p Z t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p s t];
		  [↓ p U t; ↓ p Z t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p T t];
                  [↓ p U t;  ↓ p Z t; ↓ p Yc t; ↑ p C t; ↓ p l t];
		  [↓ p U t;  ↓ p Z t; ↓ p Yc t; ↑ p C t; ↓ p m t];
		  [↓ p U t;  ↓ p Z t; ↓ p Yc t; ↑ p C t; ↓ p s t];
		  [↓ p U t;  ↓ p Z t; ↓ p Yc t; ↑ p C t; ↓ p T t]])) ∧
         ALL_DISTINCT
           (MAP (λa. PATH p a)
	         [[↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Q t; ↑ p Ya t;  ↑ p C t; ↓ p l t];
		  [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Q t; ↑ p Ya t;  ↑ p C t; ↓ p m t];
		  [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Q t; ↑ p Ya t;  ↑ p C t; ↓ p s t];
		  [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Q t; ↑ p Ya t;  ↑ p C t; ↓ p T t];
		  [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Yc t; ↑ p C t; ↓ p l t];
		  [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Yc t; ↑ p C t; ↓ p m t];
		  [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Yc t; ↑ p C t; ↓ p s t];
		  [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Yc t; ↑ p C t; ↓ p T t];
		  [↓ p U t; ↓ p Z t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p l t];
		  [↓ p U t; ↓ p Z t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p m t];
		  [↓ p U t; ↓ p Z t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p s t];
		  [↓ p U t; ↓ p Z t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p T t];
                  [↓ p U t;  ↓ p Z t; ↓ p Yc t; ↑ p C t; ↓ p l t];
		  [↓ p U t;  ↓ p Z t; ↓ p Yc t; ↑ p C t; ↓ p m t];
		  [↓ p U t;  ↓ p Z t; ↓ p Yc t; ↑ p C t; ↓ p s t];
		  [↓ p U t;  ↓ p Z t; ↓ p Yc t; ↑ p C t; ↓ p T t]]) /\
	 MUTUAL_INDEP p
           [↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p l t;
            ↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p m t;
            ↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p s t;
            ↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p T t;
            ↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Yc t; ↑ p C t; ↓ p l t; ↓ p U t;
            ↑ p Z t; ↓ p V t; ↓ p Yc t; ↑ p C t; ↓ p m t; ↓ p U t; ↑ p Z t;
            ↓ p V t; ↓ p Yc t; ↑ p C t; ↓ p s t; ↓ p U t; ↑ p Z t; ↓ p V t;
            ↓ p Yc t; ↑ p C t; ↓ p T t; ↓ p U t; ↓ p Z t; ↓ p Q t; ↑ p Ya t;
            ↑ p C t; ↓ p l t; ↓ p U t; ↓ p Z t; ↓ p Q t; ↑ p Ya t; ↑ p C t;
            ↓ p m t; ↓ p U t; ↓ p Z t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p s t;
            ↓ p U t; ↓ p Z t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p T t; ↓ p U t;
            ↓ p Z t; ↓ p Yc t; ↑ p C t; ↓ p l t; ↓ p U t; ↓ p Z t; ↓ p Yc t;
            ↑ p C t; ↓ p m t; ↓ p U t; ↓ p Z t; ↓ p Yc t; ↑ p C t; ↓ p s t;
            ↓ p U t; ↓ p Z t; ↓ p Yc t; ↑ p C t; ↓ p T t] /\ (FR_Ya = FR_Yc + FR_Yb) /\  
         (∀x'. x' = ↓ p U t ∨ x' = ↑ p Z t ∨ x' = ↓ p V t ∨ x' = ↓ p Q t ∨ x' = ↑ p Ya t ∨ x' = ↑ p C t ∨
               x' = ↓ p l t ∨ x' = ↓ p m t ∨ x' = ↓ p s t ∨ x' = ↓ p T t ∨ x' = ↓ p Yc t ∨ x' = ↓ p U t ∨
	       x' = ↓ p Z t ∨ x' = ↑ p Ya t  ⇒ x' ∈ events p)   ==>
prob p (OUTCOME_CLASS_I_BWR [↓ p l t; ↓ p m t; ↓ p s t; ↓ p T t; ↑ p C t; ↑ p Ya t;
	                     ↓ p Yc t; ↓ p Q t; ↓ p U t; ↑ p Z t; ↓ p V t; ↓ p Z t])  =
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) * (1 − exp (-FR_V * t)) *
        (1 − exp (-FR_Q * t)) * exp (-(FR_Yc + FR_Yb) * t) * exp (-FR_C * t) *
        (1 − exp (-FR_l * t)) +
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t)  * (1 − exp (-FR_V * t)) *
        (1 − exp (-FR_Q * t)) * exp (-(FR_Yc + FR_Yb) * t)  * exp (-FR_C * t) *
        (1 − exp (-FR_m * t)) +
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) * (1 − exp (-FR_V * t)) *
        (1 − exp (-FR_Q * t)) * exp (-(FR_Yc + FR_Yb) * t)  * exp (-FR_C * t) *
        (1 − exp (-FR_s * t)) +
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) * (1 − exp (-FR_V * t)) *
        (1 − exp (-FR_Q * t)) *  exp (-(FR_Yc + FR_Yb) * t) * exp (-FR_C * t) *
        (1 − exp (-FR_T * t)) +
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) * (1 − exp (-FR_V * t)) *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_l * t)) +
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) * (1 − exp (-FR_V * t)) *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_m * t)) +
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) * (1 − exp (-FR_V * t)) *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t)* (1 − exp (-FR_s * t)) +
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) * (1 − exp (-FR_V * t)) *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_T * t)) +
        (1 − exp (-FR_U * t)) * (1 − exp (-FR_Z * t)) *
        (1 − exp (-FR_Q * t)) *  exp (-(FR_Yc + FR_Yb) * t)  * exp (-FR_C * t) *
        (1 − exp (-FR_l * t)) +
        (1 − exp (-FR_U * t)) * (1 − exp (-FR_Z * t)) *
        (1 − exp (-FR_Q * t)) * exp (-(FR_Yc + FR_Yb) * t) * exp (-FR_C * t) *
        (1 − exp (-FR_m * t)) +
        (1 − exp (-FR_U * t)) * (1 − exp (-FR_Z * t)) *
        (1 − exp (-FR_Q * t)) *  exp (-(FR_Yc + FR_Yb) * t) * exp (-FR_C * t) *
        (1 − exp (-FR_s * t)) +
        (1 − exp (-FR_U * t)) * (1 − exp (-FR_Z * t)) *
        (1 − exp (-FR_Q * t)) * exp (-(FR_Yc + FR_Yb) * t)  * exp (-FR_C * t) *
        (1 − exp (-FR_T * t)) +
        (1 − exp (-FR_U * t)) * (1 − exp (-FR_Z * t)) *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_l * t)) +
        (1 − exp (-FR_U * t)) * (1 − exp (-FR_Z * t)) *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_m * t)) +
        (1 − exp (-FR_U * t)) * (1 − exp (-FR_Z * t)) *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_s * t)) +
        (1 − exp (-FR_U * t)) * (1 − exp (-FR_Z * t)) *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_T * t))``,

rw []
\\ DEP_REWRITE_TAC [PROB_OUTCOME_CLASS_I_BWR]
\\ fs []
\\ CONJ_TAC
   >-(metis_tac [])
\\ rw [SUCCESS_DEF, FAIL_DEF]
\\ sg `!X. prob p (PREIMAGE X {y | y ≤ Normal t} ∩ p_space p) = distribution p X {y | y ≤ Normal t}`
   >-(metis_tac [distribution_def])
\\ sg `!X. prob p (PREIMAGE X {y | Normal t < y} ∩ p_space p) = distribution p X {y |  Normal t < y}`
   >-(metis_tac [distribution_def])
\\ fs []
\\ rw [GSYM CDF_DEF]
\\ rw [GSYM RELIABILITY_DEF]
\\ fs [EXP_ET_DISTRIB_DEF, EXP_ET_SUCCESS_DISTRIB_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

(*---------------------------*)   
(* Probability of CLASS II   *)
(*---------------------------*)

val PROB_OUTCOME_CLASS_II_BWR = store_thm("PROB_OUTCOME_CLASS_II_BWR",
``!p l m s t Ca Cb Qa Qb Ya Yb Ua Ub Ea Eb Ia Ib Za Zb Va Vb Xa Xb Wa Wb Yc.
           prob_space p /\
	   disjoint
           (set
              (MAP (λa. PATH p a)
                 [[Wb; Xb; Qa; Ya; Ca; l]; [Wb; Xb; Qa; Ya; Ca; m];
                  [Wb; Xb; Qa; Ya; Ca; s]; [Wb; Xb; Qa; Ya; Ca; t];
                  [Wb; Xb; Ua; Qb; Ya; Ca; l]; [Wb; Xb; Ua; Qb; Ya; Ca; m];
                  [Wb; Xb; Ua; Qb; Ya; Ca; s]; [Wb; Xb; Ua; Qb; Ya; Ca; t];
                  [Wb; Xb; Ua; Yc; Ca; l]; [Wb; Xb; Ua; Yc; Ca; m];
                  [Wb; Xb; Ua; Yc; Ca; s]; [Wb; Xb; Ua; Yc; Ca; t];
                  [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; l];
                  [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; m];
                  [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; s];
                  [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; t];
                  [Wb; Xb; Ub; Za; Va; Yc; Ca; l];
                  [Wb; Xb; Ub; Za; Va; Yc; Ca; m];
                  [Wb; Xb; Ub; Za; Va; Yc; Ca; s];
                  [Wb; Xb; Ub; Za; Va; Yc; Ca; t];
                  [Wb; Xb; Ea; Ia; Yb; Ca; l]; [Wb; Xb; Ea; Ia; Yb; Ca; m];
                  [Wb; Xb; Ea; Ia; Yb; Ca; s]; [Wb; Xb; Ea; Ia; Yb; Ca; t]])) /\
         ALL_DISTINCT
           (MAP (λa. PATH p a)
              [[Wb; Xb; Qa; Ya; Ca; l]; [Wb; Xb; Qa; Ya; Ca; m];
               [Wb; Xb; Qa; Ya; Ca; s]; [Wb; Xb; Qa; Ya; Ca; t];
               [Wb; Xb; Ua; Qb; Ya; Ca; l]; [Wb; Xb; Ua; Qb; Ya; Ca; m];
               [Wb; Xb; Ua; Qb; Ya; Ca; s]; [Wb; Xb; Ua; Qb; Ya; Ca; t];
               [Wb; Xb; Ua; Yc; Ca; l]; [Wb; Xb; Ua; Yc; Ca; m];
               [Wb; Xb; Ua; Yc; Ca; s]; [Wb; Xb; Ua; Yc; Ca; t];
               [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; l];
               [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; m];
               [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; s];
               [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; t];
               [Wb; Xb; Ub; Za; Va; Yc; Ca; l];
               [Wb; Xb; Ub; Za; Va; Yc; Ca; m];
               [Wb; Xb; Ub; Za; Va; Yc; Ca; s];
               [Wb; Xb; Ub; Za; Va; Yc; Ca; t]; [Wb; Xb; Ea; Ia; Yb; Ca; l];
               [Wb; Xb; Ea; Ia; Yb; Ca; m]; [Wb; Xb; Ea; Ia; Yb; Ca; s];
               [Wb; Xb; Ea; Ia; Yb; Ca; t]]) /\
         (∀x'.
              x' = Wb ∨ x' = Xb ∨ x' = Qa ∨ x' = Ya ∨ x' = Yc  ∨ x' = Ca ∨ x' = l 
              ∨ x' = m ∨ x' = s ∨ x' = t  ∨ x' = Ua ∨ x' = Qb ∨ x' = Va
              ∨ x' = Za ∨ x' = Ub ∨ x' = Qb ∨ x' = Ia ∨ x' = Ea ∨ x' = Yb  ⇒ x' ∈ events p) /\
         (MUTUAL_INDEP p
           [Wb; Xb; Qa; Ya; Ca; l; Wb; Xb; Qa; Ya; Ca; m; Wb; Xb; Qa; Ya; Ca;
            s; Wb; Xb; Qa; Ya; Ca; t; Wb; Xb; Ua; Qb; Ya; Ca; l; Wb; Xb; Ua;
            Qb; Ya; Ca; m; Wb; Xb; Ua; Qb; Ya; Ca; s; Wb; Xb; Ua; Qb; Ya; Ca;
            t; Wb; Xb; Ua; Yc; Ca; l; Wb; Xb; Ua; Yc; Ca; m; Wb; Xb; Ua; Yc;
            Ca; s; Wb; Xb; Ua; Yc; Ca; t; Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; l;
            Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; m; Wb; Xb; Ub; Za; Va; Qb; Ya;
            Ca; s; Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; t; Wb; Xb; Ub; Za; Va; Yc;
            Ca; l; Wb; Xb; Ub; Za; Va; Yc; Ca; m; Wb; Xb; Ub; Za; Va; Yc; Ca;
            s; Wb; Xb; Ub; Za; Va; Yc; Ca; t; Wb; Xb; Ea; Ia; Yb; Ca; l; Wb;
            Xb; Ea; Ia; Yb; Ca; m; Wb; Xb; Ea; Ia; Yb; Ca; s; Wb; Xb; Ea; Ia;
            Yb; Ca; t]) ==>
  prob p (OUTCOME_CLASS_II_BWR [l; m; s; t; Ca; Yb; Ea; Ia; Wb; Qa; Qb; Ua; Ub; Va; Xb; Ya; Yc; Za]) =
             prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p l  +
	     prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p m  +
	     prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p s  +
	     prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p t  +
	     prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p l  +
	     prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p m  +
	     prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p s  +
	     prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p t  +
	     prob p Wb * prob p Xb * prob p Ua * prob p Yc * prob p Ca * prob p l +
	     prob p Wb * prob p Xb * prob p Ua * prob p Yc * prob p Ca * prob p m +
	     prob p Wb * prob p Xb * prob p Ua * prob p Yc * prob p Ca * prob p s +
	     prob p Wb * prob p Xb * prob p Ua * prob p Yc * prob p Ca * prob p t +
	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Qb * prob p Ya * prob p Ca * prob p l +
	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Qb * prob p Ya * prob p Ca * prob p m +
     	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Qb * prob p Ya * prob p Ca * prob p s +
	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Qb * prob p Ya * prob p Ca * prob p t +
	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Yc * prob p Ca * prob p l  +
	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Yc * prob p Ca * prob p m  +
	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Yc * prob p Ca * prob p s  +
	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Yc * prob p Ca * prob p t  +
	     prob p Wb * prob p Xb * prob p Ea * prob p Ia * prob p Yb * prob p Ca * prob p l  +
	     prob p Wb * prob p Xb * prob p Ea * prob p Ia * prob p Yb * prob p Ca * prob p m  +
	     prob p Wb * prob p Xb * prob p Ea * prob p Ia * prob p Yb * prob p Ca * prob p s  +
	     prob p Wb * prob p Xb * prob p Ea * prob p Ia * prob p Yb * prob p Ca * prob p t``,

rw [OUTCOME_CLASS_II_BWR_DEF]
\\ rw [WWb_DEF, WXb_DEF]
\\ rw [WQa_DEF, WUa_DEF, WVa_DEF, WIa_DEF]
\\ rw [WYa_DEF, WQb_DEF, WZa_DEF, WEa_DEF]
\\ rw [WCa_DEF, WUb_DEF, WYb_DEF]
\\ rw [WQb_DEF, WYa_DEF, WCa_DEF]
\\ sg `(𝓕𝓑𝑬𝑻
             (𝓕𝓑Ν
                [[𝓕𝓑Ν
                    [[𝓕𝓑Ν [[𝓕𝓑Ν [[𝓕𝓑 [[l; m; s; t]; [Ca]]]; [[Ya]]]]; [[Qa]]] ⧺
                      𝓕𝓑Ν
                        [[𝓕𝓑Ν
                            [[𝓕𝓑Ν [[𝓕𝓑 [[l; m; s; t]; [Ca]]]; [[Ya]]]];
                             [[Qb]]] ⧺ WYc [l; m; s; t; Ca; Yc]]; [[Ua]]] ⧺
                      𝓕𝓑Ν
                        [[𝓕𝓑Ν
                            [[𝓕𝓑Ν [[𝓕𝓑 [[l; m; s; t]; [Ca]]]; [[Ya]]]];
                             [[Qb]]] ⧺ WYc [l; m; s; t; Ca; Yc]]; [[Ub]];
                         [[Za]]; [[Va]]] ⧺
                      𝓕𝓑Ν
                        [[𝓕𝓑Ν [[𝓕𝓑 [[l; m; s; t]; [Ca]]]; [[Yb]]]]; [[Ea]];
                         [[Ia]]]]; [[Xb]]]]; [[Wb]]])) =
	(Wb ∩ (Xb ∩ (Qa ∩ (Ya ∩ (Ca ∩ l)))) ∪
           (Wb ∩ (Xb ∩ (Qa ∩ (Ya ∩ (Ca ∩ m)))) ∪
            (Wb ∩ (Xb ∩ (Qa ∩ (Ya ∩ (Ca ∩ s)))) ∪
             (Wb ∩ (Xb ∩ (Qa ∩ (Ya ∩ (Ca ∩ t)))) ∪
              (Wb ∩ (Xb ∩ (Ua ∩ (Qb ∩ (Ya ∩ (Ca ∩ l))))) ∪
               (Wb ∩ (Xb ∩ (Ua ∩ (Qb ∩ (Ya ∩ (Ca ∩ m))))) ∪
                (Wb ∩ (Xb ∩ (Ua ∩ (Qb ∩ (Ya ∩ (Ca ∩ s))))) ∪
                 (Wb ∩ (Xb ∩ (Ua ∩ (Qb ∩ (Ya ∩ (Ca ∩ t))))) ∪
                  (Wb ∩ (Xb ∩ (Ua ∩ (Yc ∩ (Ca ∩ l)))) ∪
                   (Wb ∩ (Xb ∩ (Ua ∩ (Yc ∩ (Ca ∩ m)))) ∪
                    (Wb ∩ (Xb ∩ (Ua ∩ (Yc ∩ (Ca ∩ s)))) ∪
                     (Wb ∩ (Xb ∩ (Ua ∩ (Yc ∩ (Ca ∩ t)))) ∪
                      (Wb ∩
                       (Xb ∩ (Ub ∩ (Za ∩ (Va ∩ (Qb ∩ (Ya ∩ (Ca ∩ l))))))) ∪
                       (Wb ∩
                        (Xb ∩ (Ub ∩ (Za ∩ (Va ∩ (Qb ∩ (Ya ∩ (Ca ∩ m))))))) ∪
                        (Wb ∩
                         (Xb ∩ (Ub ∩ (Za ∩ (Va ∩ (Qb ∩ (Ya ∩ (Ca ∩ s))))))) ∪
                         (Wb ∩
                          (Xb ∩ (Ub ∩ (Za ∩ (Va ∩ (Qb ∩ (Ya ∩ (Ca ∩ t))))))) ∪
                          (Wb ∩ (Xb ∩ (Ub ∩ (Za ∩ (Va ∩ (Yc ∩ (Ca ∩ l)))))) ∪
                           (Wb ∩ (Xb ∩ (Ub ∩ (Za ∩ (Va ∩ (Yc ∩ (Ca ∩ m)))))) ∪
                            (Wb ∩ (Xb ∩ (Ub ∩ (Za ∩ (Va ∩ (Yc ∩ (Ca ∩ s)))))) ∪
                             (Wb ∩
                              (Xb ∩ (Ub ∩ (Za ∩ (Va ∩ (Yc ∩ (Ca ∩ t)))))) ∪
                              (Wb ∩ (Xb ∩ (Ea ∩ (Ia ∩ (Yb ∩ (Ca ∩ l))))) ∪
                               (Wb ∩ (Xb ∩ (Ea ∩ (Ia ∩ (Yb ∩ (Ca ∩ m))))) ∪
                                (Wb ∩ (Xb ∩ (Ea ∩ (Ia ∩ (Yb ∩ (Ca ∩ s))))) ∪
                                 (Wb ∩ (Xb ∩ (Ea ∩ (Ia ∩ (Yb ∩ (Ca ∩ t))))) ∪
                                  ∅))))))))))))))))))))))))`
   >-(EVAL_TAC)
\\ POP_ORW
\\ rw [INTER_ASSOC, UNION_OVER_INTER, UNION_ASSOC]
\\ sg     `Wb ∩ Xb ∩ Qa ∩ Ya ∩ Ca ∩ l ∪
           Wb ∩ Xb ∩ Qa ∩ Ya ∩ Ca ∩ m ∪
           Wb ∩ Xb ∩ Qa ∩ Ya ∩ Ca ∩ s ∪
	   Wb ∩ Xb ∩ Qa ∩ Ya ∩ Ca ∩ t ∪
           Wb ∩ Xb ∩ Ua ∩ Qb ∩ Ya ∩ Ca ∩ l ∪
           Wb ∩ Xb ∩ Ua ∩ Qb ∩ Ya ∩ Ca ∩ m ∪
           Wb ∩ Xb ∩ Ua ∩ Qb ∩ Ya ∩ Ca ∩ s ∪
           Wb ∩ Xb ∩ Ua ∩ Qb ∩ Ya ∩ Ca ∩ t ∪
	   Wb ∩ Xb ∩ Ua ∩ Yc ∩ Ca ∩ l ∪
           Wb ∩ Xb ∩ Ua ∩ Yc ∩ Ca ∩ m ∪
	   Wb ∩ Xb ∩ Ua ∩ Yc ∩ Ca ∩ s ∪
           Wb ∩ Xb ∩ Ua ∩ Yc ∩ Ca ∩ t ∪
           Wb ∩ Xb ∩ Ub ∩ Za ∩ Va ∩ Qb ∩ Ya ∩ Ca ∩ l ∪
           Wb ∩ Xb ∩ Ub ∩ Za ∩ Va ∩ Qb ∩ Ya ∩ Ca ∩ m ∪
           Wb ∩ Xb ∩ Ub ∩ Za ∩ Va ∩ Qb ∩ Ya ∩ Ca ∩ s ∪
           Wb ∩ Xb ∩ Ub ∩ Za ∩ Va ∩ Qb ∩ Ya ∩ Ca ∩ t ∪
           Wb ∩ Xb ∩ Ub ∩ Za ∩ Va ∩ Yc ∩ Ca ∩ l ∪
           Wb ∩ Xb ∩ Ub ∩ Za ∩ Va ∩ Yc ∩ Ca ∩ m ∪
           Wb ∩ Xb ∩ Ub ∩ Za ∩ Va ∩ Yc ∩ Ca ∩ s ∪
           Wb ∩ Xb ∩ Ub ∩ Za ∩ Va ∩ Yc ∩ Ca ∩ t ∪
           Wb ∩ Xb ∩ Ea ∩ Ia ∩ Yb ∩ Ca ∩ l ∪
           Wb ∩ Xb ∩ Ea ∩ Ia ∩ Yb ∩ Ca ∩ m ∪
           Wb ∩ Xb ∩ Ea ∩ Ia ∩ Yb ∩ Ca ∩ s ∪
	   Wb ∩ Xb ∩ Ea ∩ Ia ∩ Yb ∩ Ca ∩ t =
    ETREE (NODE (EVENT_TREE_LIST (MAP (λa. ET_PATH p a)
         [[Wb; Xb; Qa; Ya; Ca; l]; 
	  [Wb; Xb; Qa; Ya; Ca; m];
	  [Wb; Xb; Qa; Ya; Ca; s];
	  [Wb; Xb; Qa; Ya; Ca; t];
	  [Wb; Xb; Ua; Qb; Ya; Ca; l];
	  [Wb; Xb; Ua; Qb; Ya; Ca; m];
	  [Wb; Xb; Ua; Qb; Ya; Ca; s];
	  [Wb; Xb; Ua; Qb; Ya; Ca; t];
	  [Wb; Xb; Ua; Yc; Ca; l];
	  [Wb; Xb; Ua; Yc; Ca; m];
	  [Wb; Xb; Ua; Yc; Ca; s];
	  [Wb; Xb; Ua; Yc; Ca; t];
	  [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; l];
	  [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; m];
	  [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; s];
	  [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; t];
	  [Wb; Xb; Ub; Za; Va; Yc; Ca; l];
	  [Wb; Xb; Ub; Za; Va; Yc; Ca; m];
	  [Wb; Xb; Ub; Za; Va; Yc; Ca; s];
	  [Wb; Xb; Ub; Za; Va; Yc; Ca; t];
	  [Wb; Xb; Ea; Ia; Yb; Ca; l];
	  [Wb; Xb; Ea; Ia; Yb; Ca; m];
	  [Wb; Xb; Ea; Ia; Yb; Ca; s];
	  [Wb; Xb; Ea; Ia; Yb; Ca; t]])))`
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
              z = [Wb; Xb; Ua; Qb; Ya; Ca; t] ∨ z = [Wb; Xb; Ua; Yc; Ca; l] ∨
              z = [Wb; Xb; Ua; Yc; Ca; m] ∨ z = [Wb; Xb; Ua; Yc; Ca; s] ∨
              z = [Wb; Xb; Ua; Yc; Ca; t] ∨
              z = [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; l] ∨
              z = [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; m] ∨
              z = [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; s] ∨
              z = [Wb; Xb; Ub; Za; Va; Qb; Ya; Ca; t] ∨
              z = [Wb; Xb; Ub; Za; Va; Yc; Ca; l] ∨
              z = [Wb; Xb; Ub; Za; Va; Yc; Ca; m] ∨
              z = [Wb; Xb; Ub; Za; Va; Yc; Ca; s] ∨
              z = [Wb; Xb; Ub; Za; Va; Yc; Ca; t] ∨
              z = [Wb; Xb; Ea; Ia; Yb; Ca; l] ∨
              z = [Wb; Xb; Ea; Ia; Yb; Ca; m] ∨
              z = [Wb; Xb; Ea; Ia; Yb; Ca; s] ∨
              z = [Wb; Xb; Ea; Ia; Yb; Ca; t] ⇒
              ~NULL z)`
   >-( metis_tac [NULL])
\\ sg `∀x'.
             x' = Wb ∨ x' = Xb ∨ x' = Qa ∨ x' = Ya ∨ x' = Ca ∨ x' = l ∨
             x' = Wb ∨ x' = Xb ∨ x' = Qa ∨ x' = Ya ∨ x' = Ca ∨ x' = m ∨
             x' = Wb ∨ x' = Xb ∨ x' = Qa ∨ x' = Ya ∨ x' = Ca ∨ x' = s ∨
             x' = Wb ∨ x' = Xb ∨ x' = Qa ∨ x' = Ya ∨ x' = Ca ∨ x' = t ∨
             x' = Wb ∨ x' = Xb ∨ x' = Ua ∨ x' = Qb ∨ x' = Ya ∨ x' = Ca ∨
             x' = l ∨ x' = Wb ∨ x' = Xb ∨ x' = Ua ∨ x' = Qb ∨ x' = Ya ∨
             x' = Ca ∨ x' = m ∨ x' = Wb ∨ x' = Xb ∨ x' = Ua ∨ x' = Qb ∨
             x' = Ya ∨ x' = Ca ∨ x' = s ∨ x' = Wb ∨ x' = Xb ∨ x' = Ua ∨
             x' = Qb ∨ x' = Ya ∨ x' = Ca ∨ x' = t ∨ x' = Wb ∨ x' = Xb ∨
             x' = Ua ∨ x' = Yc ∨ x' = Ca ∨ x' = l ∨ x' = Wb ∨ x' = Xb ∨
             x' = Ua ∨ x' = Yc ∨ x' = Ca ∨ x' = m ∨ x' = Wb ∨ x' = Xb ∨
             x' = Ua ∨ x' = Yc ∨ x' = Ca ∨ x' = s ∨ x' = Wb ∨ x' = Xb ∨
             x' = Ua ∨ x' = Yc ∨ x' = Ca ∨ x' = t ∨ x' = Wb ∨ x' = Xb ∨
             x' = Ub ∨ x' = Za ∨ x' = Va ∨ x' = Qb ∨ x' = Ya ∨ x' = Ca ∨
             x' = l ∨ x' = Wb ∨ x' = Xb ∨ x' = Ub ∨ x' = Za ∨ x' = Va ∨
             x' = Qb ∨ x' = Ya ∨ x' = Ca ∨ x' = m ∨ x' = Wb ∨ x' = Xb ∨
             x' = Ub ∨ x' = Za ∨ x' = Va ∨ x' = Qb ∨ x' = Ya ∨ x' = Ca ∨
             x' = s ∨ x' = Wb ∨ x' = Xb ∨ x' = Ub ∨ x' = Za ∨ x' = Va ∨
             x' = Qb ∨ x' = Ya ∨ x' = Ca ∨ x' = t ∨ x' = Wb ∨ x' = Xb ∨
             x' = Ub ∨ x' = Za ∨ x' = Va ∨ x' = Yc ∨ x' = Ca ∨ x' = l ∨
             x' = Wb ∨ x' = Xb ∨ x' = Ub ∨ x' = Za ∨ x' = Va ∨ x' = Yc ∨
             x' = Ca ∨ x' = m ∨ x' = Wb ∨ x' = Xb ∨ x' = Ub ∨ x' = Za ∨
             x' = Va ∨ x' = Yc ∨ x' = Ca ∨ x' = s ∨ x' = Wb ∨ x' = Xb ∨
             x' = Ub ∨ x' = Za ∨ x' = Va ∨ x' = Yc ∨ x' = Ca ∨ x' = t ∨
             x' = Wb ∨ x' = Xb ∨ x' = Ea ∨ x' = Ia ∨ x' = Yb ∨ x' = Ca ∨
             x' = l ∨ x' = Wb ∨ x' = Xb ∨ x' = Ea ∨ x' = Ia ∨ x' = Yb ∨
             x' = Ca ∨ x' = m ∨ x' = Wb ∨ x' = Xb ∨ x' = Ea ∨ x' = Ia ∨
             x' = Yb ∨ x' = Ca ∨ x' = s ∨ x' = Wb ∨ x' = Xb ∨ x' = Ea ∨
             x' = Ia ∨ x' = Yb ∨ x' = Ca ∨ x' = t ⇒
             x' ∈ events p`
   >-( metis_tac [])
\\ REWRITE_TAC [PROB_LIST_DEF, PROD_LIST_DEF, SUM_LIST_DEF]
\\ sg `prob p Wb *
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
                 (prob p Ua * (prob p Yc * (prob p Ca * (prob p l * 1))))) +
                (prob p Wb *
                 (prob p Xb *
                  (prob p Ua * (prob p Yc * (prob p Ca * (prob p m * 1))))) +
                 (prob p Wb *
                  (prob p Xb *
                   (prob p Ua * (prob p Yc * (prob p Ca * (prob p s * 1))))) +
                  (prob p Wb *
                   (prob p Xb *
                    (prob p Ua * (prob p Yc * (prob p Ca * (prob p t * 1))))) +
                   (prob p Wb *
                    (prob p Xb *
                     (prob p Ub *
                      (prob p Za *
                       (prob p Va *
                        (prob p Qb *
                         (prob p Ya * (prob p Ca * (prob p l * 1)))))))) +
                    (prob p Wb *
                     (prob p Xb *
                      (prob p Ub *
                       (prob p Za *
                        (prob p Va *
                         (prob p Qb *
                          (prob p Ya * (prob p Ca * (prob p m * 1)))))))) +
                     (prob p Wb *
                      (prob p Xb *
                       (prob p Ub *
                        (prob p Za *
                         (prob p Va *
                          (prob p Qb *
                           (prob p Ya * (prob p Ca * (prob p s * 1)))))))) +
                      (prob p Wb *
                       (prob p Xb *
                        (prob p Ub *
                         (prob p Za *
                          (prob p Va *
                           (prob p Qb *
                            (prob p Ya * (prob p Ca * (prob p t * 1)))))))) +
                       (prob p Wb *
                        (prob p Xb *
                         (prob p Ub *
                          (prob p Za *
                           (prob p Va *
                            (prob p Yc * (prob p Ca * (prob p l * 1))))))) +
                        (prob p Wb *
                         (prob p Xb *
                          (prob p Ub *
                           (prob p Za *
                            (prob p Va *
                             (prob p Yc * (prob p Ca * (prob p m * 1))))))) +
                         (prob p Wb *
                          (prob p Xb *
                           (prob p Ub *
                            (prob p Za *
                             (prob p Va *
                              (prob p Yc * (prob p Ca * (prob p s * 1))))))) +
                          (prob p Wb *
                           (prob p Xb *
                            (prob p Ub *
                             (prob p Za *
                              (prob p Va *
                               (prob p Yc * (prob p Ca * (prob p t * 1))))))) +
                           (prob p Wb *
                            (prob p Xb *
                             (prob p Ea *
                              (prob p Ia *
                               (prob p Yb * (prob p Ca * (prob p l * 1)))))) +
                            (prob p Wb *
                             (prob p Xb *
                              (prob p Ea *
                               (prob p Ia *
                                (prob p Yb * (prob p Ca * (prob p m * 1)))))) +
                             (prob p Wb *
                              (prob p Xb *
                               (prob p Ea *
                                (prob p Ia *
                                 (prob p Yb * (prob p Ca * (prob p s * 1)))))) +
                              (prob p Wb *
                               (prob p Xb *
                                (prob p Ea *
                                 (prob p Ia *
                                  (prob p Yb * (prob p Ca * (prob p t * 1)))))) +
                               0))))))))))))))))))))))) = 
             prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p l  +
	     prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p m  +
	     prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p s  +
	     prob p Wb * prob p Xb * prob p Qa * prob p Ya * prob p Ca * prob p t  +
	     prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p l  +
	     prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p m  +
	     prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p s  +
	     prob p Wb * prob p Xb * prob p Ua * prob p Qb * prob p Ya * prob p Ca * prob p t  +
	     prob p Wb * prob p Xb * prob p Ua * prob p Yc * prob p Ca * prob p l +
	     prob p Wb * prob p Xb * prob p Ua * prob p Yc * prob p Ca * prob p m +
	     prob p Wb * prob p Xb * prob p Ua * prob p Yc * prob p Ca * prob p s +
	     prob p Wb * prob p Xb * prob p Ua * prob p Yc * prob p Ca * prob p t +
	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Qb * prob p Ya * prob p Ca * prob p l +
	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Qb * prob p Ya * prob p Ca * prob p m +
     	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Qb * prob p Ya * prob p Ca * prob p s +
	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Qb * prob p Ya * prob p Ca * prob p t +
	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Yc * prob p Ca * prob p l  +
	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Yc * prob p Ca * prob p m  +
	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Yc * prob p Ca * prob p s  +
	     prob p Wb * prob p Xb * prob p Ub * prob p Za * prob p Va * prob p Yc * prob p Ca * prob p t  +
	     prob p Wb * prob p Xb * prob p Ea * prob p Ia * prob p Yb * prob p Ca * prob p l  +
	     prob p Wb * prob p Xb * prob p Ea * prob p Ia * prob p Yb * prob p Ca * prob p m  +
	     prob p Wb * prob p Xb * prob p Ea * prob p Ia * prob p Yb * prob p Ca * prob p s  +
	     prob p Wb * prob p Xb * prob p Ea * prob p Ia * prob p Yb * prob p Ca * prob p t`
   >-(REAL_ARITH_TAC)
\\ metis_tac []);   
(*--------------------------------------------------------------------------------------------------*)

(*------------------------------------------------------------*)   
(*  Probability of CLASS II Failure Exponential Distribution  *)
(*------------------------------------------------------------*)

val PROB_OUTCOME_CLASS_II_BWR_EXP_DISTRIBUTION = store_thm("PROB_OUTCOME_CLASS_II_BWR_EXP_DISTRIBUTION",
``!p l m s T C Ya Yc Yb Q U Z V X W t E I FR_l FR_m FR_s FR_T
   FR_C FR_Ya FR_Yc FR_Yb FR_Q FR_U FR_Z FR_V FR_X FR_W FR_I FR_E.
         prob_space p /\ 0 <= t    /\
         EXP_ET_DISTRIB p l FR_l   /\ EXP_ET_DISTRIB p m FR_m  /\ EXP_ET_DISTRIB p s FR_s   /\
	 EXP_ET_DISTRIB p T FR_T   /\ EXP_ET_DISTRIB p C FR_C  /\ EXP_ET_DISTRIB p Yc FR_Yc /\
	 EXP_ET_DISTRIB p Yb FR_Yb /\ EXP_ET_DISTRIB p Q FR_Q  /\ EXP_ET_DISTRIB p U FR_U   /\
	 EXP_ET_DISTRIB p X FR_X   /\ EXP_ET_DISTRIB p I FR_I  /\ EXP_ET_DISTRIB p W FR_W   /\
	 EXP_ET_SUCCESS_DISTRIB p Ya FR_Ya /\ EXP_ET_SUCCESS_DISTRIB p Z FR_Z /\
	 EXP_ET_SUCCESS_DISTRIB p C FR_C   /\ EXP_ET_SUCCESS_DISTRIB p E FR_E /\
	 EXP_ET_SUCCESS_DISTRIB p I FR_I   /\ EXP_ET_SUCCESS_DISTRIB p Q FR_Q /\
	 EXP_ET_SUCCESS_DISTRIB p U FR_U   /\ EXP_ET_SUCCESS_DISTRIB p V FR_V /\
	 (FR_Ya = FR_Yc + FR_Yb) /\
         disjoint
           (set
              (MAP (λa. PATH p a)
                 [[↓ p W t; ↓ p X t; ↑ p Q t; ↑ p Ya t; ↑ p C t; ↓ p l t];
                  [↓ p W t; ↓ p X t; ↑ p Q t; ↑ p Ya t; ↑ p C t; ↓ p m t];
                  [↓ p W t; ↓ p X t; ↑ p Q t; ↑ p Ya t; ↑ p C t; ↓ p s t];
                  [↓ p W t; ↓ p X t; ↑ p Q t; ↑ p Ya t; ↑ p C t; ↓ p T t];
                  [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p l t];
                  [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p m t];
                  [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p s t];
                  [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p T t];
                  [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Yc t; ↑ p C t; ↓ p l t];
                  [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Yc t; ↑ p C t; ↓ p m t];
                  [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Yc t; ↑ p C t; ↓ p s t];
                  [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Yc t; ↑ p C t; ↓ p T t];
                  [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p l t];
                  [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p m t];
                  [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p s t];
                  [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p T t];
                  [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Yc t; ↑ p C t; ↓ p l t];
                  [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Yc t; ↑ p C t; ↓ p m t];
                  [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Yc t; ↑ p C t; ↓ p s t];
                  [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Yc t; ↑ p C t; ↓ p T t];
                  [↓ p W t; ↓ p X t; ↑ p E t; ↑ p I t; ↓ p Yb t; ↑ p C t; ↓ p l t];
                  [↓ p W t; ↓ p X t; ↑ p E t; ↑ p I t; ↓ p Yb t; ↑ p C t; ↓ p m t];
                  [↓ p W t; ↓ p X t; ↑ p E t; ↑ p I t; ↓ p Yb t; ↑ p C t; ↓ p s t];
                  [↓ p W t; ↓ p X t; ↑ p E t; ↑ p I t; ↓ p Yb t; ↑ p C t; ↓ p T t]])) /\
         ALL_DISTINCT
           (MAP (λa. PATH p a)
              [[↓ p W t; ↓ p X t; ↑ p Q t; ↑ p Ya t; ↑ p C t; ↓ p l t];
               [↓ p W t; ↓ p X t; ↑ p Q t; ↑ p Ya t; ↑ p C t; ↓ p m t];
               [↓ p W t; ↓ p X t; ↑ p Q t; ↑ p Ya t; ↑ p C t; ↓ p s t];
               [↓ p W t; ↓ p X t; ↑ p Q t; ↑ p Ya t; ↑ p C t; ↓ p T t];
               [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p l t];
               [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p m t];
               [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p s t];
               [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p T t];
               [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Yc t; ↑ p C t; ↓ p l t];
               [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Yc t; ↑ p C t; ↓ p m t];
               [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Yc t; ↑ p C t; ↓ p s t];
               [↓ p W t; ↓ p X t; ↑ p U t; ↓ p Yc t; ↑ p C t; ↓ p T t];
               [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p l t];
               [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p m t];
               [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p s t];
               [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p T t];
               [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Yc t; ↑ p C t; ↓ p l t];
               [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Yc t; ↑ p C t; ↓ p m t];
               [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Yc t; ↑ p C t; ↓ p s t];
               [↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Yc t; ↑ p C t; ↓ p T t];
               [↓ p W t; ↓ p X t; ↑ p E t; ↑ p I t; ↓ p Yb t; ↑ p C t; ↓ p l t];
               [↓ p W t; ↓ p X t; ↑ p E t; ↑ p I t; ↓ p Yb t; ↑ p C t; ↓ p m t];
               [↓ p W t; ↓ p X t; ↑ p E t; ↑ p I t; ↓ p Yb t; ↑ p C t; ↓ p s t];
               [↓ p W t; ↓ p X t; ↑ p E t; ↑ p I t; ↓ p Yb t; ↑ p C t; ↓ p T t]]) /\
         (∀x'.
              x' = ↓ p W t ∨ x' = ↓ p X t ∨ x' = ↑ p Q t ∨ x' = ↑ p Ya t ∨
              x' = ↓ p Yc t ∨ x' = ↑ p C t ∨ x' = ↓ p l t ∨ x' = ↓ p m t ∨
              x' = ↓ p s t ∨ x' = ↓ p T t ∨ x' = ↑ p U t ∨ x' = ↓ p Q t ∨
              x' = ↑ p V t ∨ x' = ↑ p Z t ∨ x' = ↓ p U t ∨ x' = ↓ p Q t ∨
              x' = ↑ p I t ∨ x' = ↑ p E t ∨ x' = ↓ p Yb t ⇒ x' ∈ events p) /\
         MUTUAL_INDEP p
           [↓ p W t; ↓ p X t; ↑ p Q t; ↑ p Ya t; ↑ p C t; ↓ p l t; ↓ p W t;
            ↓ p X t; ↑ p Q t; ↑ p Ya t; ↑ p C t; ↓ p m t; ↓ p W t; ↓ p X t;
            ↑ p Q t; ↑ p Ya t; ↑ p C t; ↓ p s t; ↓ p W t; ↓ p X t; ↑ p Q t;
            ↑ p Ya t; ↑ p C t; ↓ p T t; ↓ p W t; ↓ p X t; ↑ p U t; ↓ p Q t;
            ↑ p Ya t; ↑ p C t; ↓ p l t; ↓ p W t; ↓ p X t; ↑ p U t; ↓ p Q t;
            ↑ p Ya t; ↑ p C t; ↓ p m t; ↓ p W t; ↓ p X t; ↑ p U t; ↓ p Q t;
            ↑ p Ya t; ↑ p C t; ↓ p s t; ↓ p W t; ↓ p X t; ↑ p U t; ↓ p Q t;
            ↑ p Ya t; ↑ p C t; ↓ p T t; ↓ p W t; ↓ p X t; ↑ p U t;
            ↓ p Yc t; ↑ p C t; ↓ p l t; ↓ p W t; ↓ p X t; ↑ p U t; ↓ p Yc t;
            ↑ p C t; ↓ p m t; ↓ p W t; ↓ p X t; ↑ p U t; ↓ p Yc t; ↑ p C t;
            ↓ p s t; ↓ p W t; ↓ p X t; ↑ p U t; ↓ p Yc t; ↑ p C t; ↓ p T t;
            ↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Q t; ↑ p Ya t;
            ↑ p C t; ↓ p l t; ↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t;
            ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p m t; ↓ p W t; ↓ p X t; ↓ p U t;
            ↑ p Z t; ↑ p V t; ↓ p Q t; ↑ p Ya t; ↑ p C t; ↓ p s t; ↓ p W t;
            ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Q t; ↑ p Ya t; ↑ p C t;
            ↓ p T t; ↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t; ↓ p Yc t;
            ↑ p C t; ↓ p l t; ↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t; ↑ p V t;
            ↓ p Yc t; ↑ p C t; ↓ p m t; ↓ p W t; ↓ p X t; ↓ p U t; ↑ p Z t;
            ↑ p V t; ↓ p Yc t; ↑ p C t; ↓ p s t; ↓ p W t; ↓ p X t; ↓ p U t;
            ↑ p Z t; ↑ p V t; ↓ p Yc t; ↑ p C t; ↓ p T t; ↓ p W t; ↓ p X t;
            ↑ p E t; ↑ p I t; ↓ p Yb t; ↑ p C t; ↓ p l t; ↓ p W t; ↓ p X t;
            ↑ p E t; ↑ p I t; ↓ p Yb t; ↑ p C t; ↓ p m t; ↓ p W t; ↓ p X t;
            ↑ p E t; ↑ p I t; ↓ p Yb t; ↑ p C t; ↓ p s t; ↓ p W t; ↓ p X t;
            ↑ p E t; ↑ p I t; ↓ p Yb t; ↑ p C t; ↓ p T t] ==>
  prob p (OUTCOME_CLASS_II_BWR [↓ p l t; ↓ p m t; ↓ p s t; ↓ p T t; ↑ p C t; ↓ p Yb t; ↑ p E t; ↑ p I t ; ↓ p W t;
                                ↑ p Q t; ↓ p Q t; ↑ p U t; ↓ p U t; ↑ p V t; ↓ p X t; ↑ p Ya t; ↓ p Yc t; ↑ p Z t])
 =         (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_Q * t) *
        exp (-(FR_Yc + FR_Yb) * t) * exp (-FR_C * t) * (1 − exp (-FR_l * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_Q * t) *
        exp (-(FR_Yc + FR_Yb) * t) * exp (-FR_C * t) * (1 − exp (-FR_m * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_Q * t) *
        exp (-(FR_Yc + FR_Yb) * t) * exp (-FR_C * t) * (1 − exp (-FR_s * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_Q * t) *
        exp (-(FR_Yc + FR_Yb) * t) * exp (-FR_C * t) * (1 − exp (-FR_T * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_U * t) *
        (1 − exp (-FR_Q * t)) * exp (-(FR_Yc + FR_Yb) * t) *
        exp (-FR_C * t) * (1 − exp (-FR_l * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_U * t) *
        (1 − exp (-FR_Q * t)) * exp (-(FR_Yc + FR_Yb) * t) *
        exp (-FR_C * t) * (1 − exp (-FR_m * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_U * t) *
        (1 − exp (-FR_Q * t)) * exp (-(FR_Yc + FR_Yb) * t) *
        exp (-FR_C * t) * (1 − exp (-FR_s * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_U * t) *
        (1 − exp (-FR_Q * t)) * exp (-(FR_Yc + FR_Yb) * t) *
        exp (-FR_C * t) * (1 − exp (-FR_T * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_U * t) *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_l * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_U * t) *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_m * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_U * t) *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_s * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_U * t) *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_T * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) *
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) *  exp (-FR_V * t)  *
        (1 − exp (-FR_Q * t)) * exp (-(FR_Yc + FR_Yb) * t) *
        exp (-FR_C * t) * (1 − exp (-FR_l * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) *
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) *  exp (-FR_V * t)  *
        (1 − exp (-FR_Q * t)) * exp (-(FR_Yc + FR_Yb) * t) *
        exp (-FR_C * t) * (1 − exp (-FR_m * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) *
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) *  exp (-FR_V * t)  *
        (1 − exp (-FR_Q * t)) * exp (-(FR_Yc + FR_Yb) * t) *
        exp (-FR_C * t) * (1 − exp (-FR_s * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) *
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) *  exp (-FR_V * t)  *
        (1 − exp (-FR_Q * t)) * exp (-(FR_Yc + FR_Yb) * t) *
        exp (-FR_C * t) * (1 − exp (-FR_T * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) *
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) *  exp (-FR_V * t)  *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_l * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) *
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) *  exp (-FR_V * t)  *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_m * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) *
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) *  exp (-FR_V * t)  *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_s * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) *
        (1 − exp (-FR_U * t)) * exp (-FR_Z * t) *  exp (-FR_V * t)  *
        (1 − exp (-FR_Yc * t)) * exp (-FR_C * t) * (1 − exp (-FR_T * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_E * t) *
        exp (-FR_I * t) * (1 − exp (-FR_Yb * t)) * exp (-FR_C * t) *
        (1 − exp (-FR_l * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_E * t) *
        exp (-FR_I * t) * (1 − exp (-FR_Yb * t)) * exp (-FR_C * t) *
        (1 − exp (-FR_m * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_E * t) *
        exp (-FR_I * t) * (1 − exp (-FR_Yb * t)) * exp (-FR_C * t) *
        (1 − exp (-FR_s * t)) +
        (1 − exp (-FR_W * t)) * (1 − exp (-FR_X * t)) * exp (-FR_E * t) *
        exp (-FR_I * t) * (1 − exp (-FR_Yb * t)) * exp (-FR_C * t) *
        (1 − exp (-FR_T * t))``,

rw []
\\ DEP_REWRITE_TAC [PROB_OUTCOME_CLASS_II_BWR]
\\ fs []
\\ CONJ_TAC
   >-(metis_tac [])
\\ rw [SUCCESS_DEF, FAIL_DEF]
\\ sg `!X. prob p (PREIMAGE X {y | y ≤ Normal t} ∩ p_space p) = distribution p X {y | y ≤ Normal t}`
   >-(metis_tac [distribution_def])
\\ sg `!X. prob p (PREIMAGE X {y | Normal t < y} ∩ p_space p) = distribution p X {y |  Normal t < y}`
   >-(metis_tac [distribution_def])
\\ fs []
\\ rw [GSYM CDF_DEF]
\\ rw [GSYM RELIABILITY_DEF]
\\ fs [EXP_ET_DISTRIB_DEF, EXP_ET_SUCCESS_DISTRIB_DEF]
\\ REAL_ARITH_TAC);
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

			(*-----------------------------------------------*)   
			(*  OUTCOME CLASSES Probabilitic SML Evaluation  *)
			(*-----------------------------------------------*)

(*----------------------------------------*)   
(* Assume  FR_L       =   0.11 per year   *)
(* Assume  FR_M       =   0.12 per year   *)
(* Assume  FR_S       =   0.15 per year   *)
(* Assume  FR_T       =   0.16 per year   *)
(* Assume  FR_C       =   0.21 per year   *)
(* Assume  FR_Yb      =   0.15 per year   *)
(* Assume  FR_Yc      =   0.21 per year   *)
(* Assume  FR_Q       =   0.57 per year   *)
(* Assume  FR_W       =   0.42 per year   *)
(* Assume  FR_U       =   0.23 per year   *)
(* Assume  FR_Z       =   0.22 per year   *)
(* Assume  FR_V       =   0.16 per year   *)
(* Assume  FR_E       =   0.12 per year   *)
(* Assume  FR_X       =   0.57 per year   *)
(* Assume  FR_I       =   0.46 per year   *)
(*----------------------------------------*)

PROBABILITY ``CLASS_I``
     `` (1 − exp (-(23:real)/(100:real))) * exp (-(22:real)/(100:real)) * (1 − exp (-(16:real)/(100:real))) *
        (1 − exp (-(57:real)/(100:real))) * exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real)) * exp (-(21:real)/(100:real)) *
        (1 − exp (-(11:real)/(100:real))) +
        (1 − exp (-(23:real)/(100:real))) * exp (-(22:real)/(100:real)) * (1 − exp (-(16:real)/(100:real))) *
        (1 − exp (-(57:real)/(100:real))) * exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real))  * exp (-(21:real)/(100:real)) *
        (1 − exp (-(12:real)/(100:real))) +
        (1 − exp (-(23:real)/(100:real))) * exp (-(22:real)/(100:real)) * (1 − exp (-(16:real)/(100:real))) *
        (1 − exp (-(57:real)/(100:real))) * exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real))  * exp (-(21:real)/(100:real)) *
        (1 − exp (-(15:real)/(100:real))) +
        (1 − exp (-(23:real)/(100:real))) * exp (-(22:real)/(100:real)  ) * (1 − exp (-(16:real)/(100:real))  ) *
        (1 − exp (-(57:real)/(100:real))) * exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real)) * exp (-(21:real)/(100:real)  ) *
        (1 − exp (-(16:real)/(100:real))) +
        (1 − exp (-(23:real)/(100:real))) * exp (-(22:real)/(100:real))   * (1 − exp (-(16:real)/(100:real)  )) *
        (1 − exp (-(21:real)/(100:real))  ) * exp (-(21:real)/(100:real)  ) * (1 − exp (-(11:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * exp (-(22:real)/(100:real)  ) * (1 − exp (-(16:real)/(100:real))  ) *
        (1 − exp (-(21:real)/(100:real)  )) * exp (-(21:real)/(100:real)  ) * (1 − exp (-(12:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * exp (-(22:real)/(100:real)  ) * (1 − exp (-(16:real)/(100:real)  )) *
        (1 − exp (-(21:real)/(100:real))  ) * exp (-(21:real)/(100:real)  )* (1 − exp (-(15:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * exp (-(22:real)/(100:real) ) * (1 − exp (-(16:real)/(100:real)  )) *
        (1 − exp (-(21:real)/(100:real)) ) * exp (-(21:real)/(100:real)  ) * (1 − exp (-(16:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real)  )) *
        (1 − exp (-(57:real)/(100:real)  )) * exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real))   * exp (-(21:real)/(100:real)  ) *
        (1 − exp (-(11:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real))  ) *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real))  * exp (-(21:real)/(100:real)  ) *
        (1 − exp (-(12:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real))  ) *
        (1 − exp (-(57:real)/(100:real)  )) *  exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real))  * exp (-(21:real)/(100:real)  ) *
        (1 − exp (-(15:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real))  ) *
        (1 − exp (-(57:real)/(100:real))  ) * exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real))  * exp (-(21:real)/(100:real)  ) *
        (1 − exp (-(16:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real)  )) *
        (1 − exp (-(21:real)/(100:real))  ) * exp (-(21:real)/(100:real)  ) * (1 − exp (-(11:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real) )) *
        (1 − exp (-(21:real)/(100:real))  ) * exp (-(21:real)/(100:real)  ) * (1 − exp (-(12:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real))  ) *
        (1 − exp (-(21:real)/(100:real))  ) * exp (-(21:real)/(100:real)  ) * (1 − exp (-(15:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real))  ) *
        (1 − exp (-(21:real)/(100:real))  ) * exp (-(21:real)/(100:real)  ) * (1 − exp (-(16:real)/(100:real)  ))``;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``CLASS_II``
`` (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(57:real)/(100:real) ) *
         exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) * exp (-(21:real)/(100:real) ) * (1 − exp (-(11:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(57:real)/(100:real) ) *
        exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) * exp (-(21:real)/(100:real) ) * (1 − exp (-(12:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(57:real)/(100:real) ) *
        exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) )  * exp (-(21:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(57:real)/(100:real) ) *
        exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) )* exp (-(21:real)/(100:real) ) * (1 − exp (-(16:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(11:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(12:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(16:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(11:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(12:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(16:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(11:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(12:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real)) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real)) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(16:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(11:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(12:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(16:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(12:real)/(100:real) ) *
        exp (-(46:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real ))) * exp (-(21:real)/(100:real) ) *
        (1 − exp (-(11:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(12:real)/(100:real) ) *
        exp (-(46:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real ))) * exp (-(21:real)/(100:real) ) *
        (1 − exp (-(12:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(12:real)/(100:real) ) *
        exp (-(46:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real ))) * exp (-(21:real)/(100:real) ) *
        (1 − exp (-(15:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(12:real)/(100:real) ) *
        exp (-(46:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real ))) * exp (-(21:real)/(100:real) ) *
        (1 − exp (-(16:real)/(100:real) ))``;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``CLASS_III``
  ``(1 - exp (-(12:real)/(100:real))) * (1 - exp (-(15:real)/(100:real))) * exp (-(21:real)/(100:real)) * (1 - exp (-(11:real)/(100:real))) +
    (1 - exp (-(12:real)/(100:real))) * (1 - exp (-(15:real)/(100:real)))  * exp (-(21:real)/(100:real)) * (1 - exp (-(12:real)/(100:real))) +
    (1 - exp (-(12:real)/(100:real))) * (1 - exp (-(15:real)/(100:real))) * exp (-(21:real)/(100:real)) * (1 - exp (-(15:real)/(100:real))) +
    (1 - exp (-(12:real)/(100:real))) * (1 - exp (-(15:real)/(100:real))) * exp (-(21:real)/(100:real)) * (1 - exp (-(16:real)/(100:real))) +
    exp (-(12:real)/(100:real)) * (1 - exp (-(46:real)/(100:real))) * (1 - exp (-(15:real)/(100:real))) * exp (-(21:real)/(100:real)) *
    (1 - exp (-(11:real)/(100:real))) +
    exp (-(12:real)/(100:real)) * (1 - exp (-(46:real)/(100:real))) * (1 - exp (-(15:real)/(100:real))) * exp (-(21:real)/(100:real)) *
    (1 - exp (-(12:real)/(100:real))) +
    exp (-(12:real)/(100:real)) * (1 - exp (-(46:real)/(100:real))) * (1 - exp (-(15:real)/(100:real))) * exp (-(21:real)/(100:real)) *
    (1 - exp (-(15:real)/(100:real))) +
    exp (-(12:real)/(100:real)) * (1 - exp (-(46:real)/(100:real))) * (1 - exp (-(15:real)/(100:real))) * exp (-(21:real)/(100:real)) *
    (1 - exp (-(16:real)/(100:real)))``;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``CLASS_IV``
``(1 − exp (-(21:real)/(100:real))) * (1 − exp (-(11:real)/(100:real))) +
  (1 − exp (-(21:real)/(100:real))) * (1 − exp (-(12:real)/(100:real))) +
  (1 − exp (-(21:real)/(100:real))) * (1 − exp (-(15:real)/(100:real))) +
  (1 − exp (-(21:real)/(100:real))) * (1 − exp (-(16:real)/(100:real)))``;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)

PROBABILITY ``SUCCESS``
  ``1 - ((1 − exp (-(23:real)/(100:real))) * exp (-(22:real)/(100:real)) * (1 − exp (-(16:real)/(100:real))) *
        (1 − exp (-(57:real)/(100:real))) * exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real)) * exp (-(21:real)/(100:real)) *
        (1 − exp (-(11:real)/(100:real))) +
        (1 − exp (-(23:real)/(100:real))) * exp (-(22:real)/(100:real)) * (1 − exp (-(16:real)/(100:real))) *
        (1 − exp (-(57:real)/(100:real))) * exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real))  * exp (-(21:real)/(100:real)) *
        (1 − exp (-(12:real)/(100:real))) +
        (1 − exp (-(23:real)/(100:real))) * exp (-(22:real)/(100:real)) * (1 − exp (-(16:real)/(100:real))) *
        (1 − exp (-(57:real)/(100:real))) * exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real))  * exp (-(21:real)/(100:real)) *
        (1 − exp (-(15:real)/(100:real))) +
        (1 − exp (-(23:real)/(100:real))) * exp (-(22:real)/(100:real)  ) * (1 − exp (-(16:real)/(100:real))  ) *
        (1 − exp (-(57:real)/(100:real))) * exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real)) * exp (-(21:real)/(100:real)  ) *
        (1 − exp (-(16:real)/(100:real))) +
        (1 − exp (-(23:real)/(100:real))) * exp (-(22:real)/(100:real))   * (1 − exp (-(16:real)/(100:real)  )) *
        (1 − exp (-(21:real)/(100:real))  ) * exp (-(21:real)/(100:real)  ) * (1 − exp (-(11:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * exp (-(22:real)/(100:real)  ) * (1 − exp (-(16:real)/(100:real))  ) *
        (1 − exp (-(21:real)/(100:real)  )) * exp (-(21:real)/(100:real)  ) * (1 − exp (-(12:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * exp (-(22:real)/(100:real)  ) * (1 − exp (-(16:real)/(100:real)  )) *
        (1 − exp (-(21:real)/(100:real))  ) * exp (-(21:real)/(100:real)  )* (1 − exp (-(15:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * exp (-(22:real)/(100:real) ) * (1 − exp (-(16:real)/(100:real)  )) *
        (1 − exp (-(21:real)/(100:real)) ) * exp (-(21:real)/(100:real)  ) * (1 − exp (-(16:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real)  )) *
        (1 − exp (-(57:real)/(100:real)  )) * exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real))   * exp (-(21:real)/(100:real)  ) *
        (1 − exp (-(11:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real))  ) *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real))  * exp (-(21:real)/(100:real)  ) *
        (1 − exp (-(12:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real))  ) *
        (1 − exp (-(57:real)/(100:real)  )) *  exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real))  * exp (-(21:real)/(100:real)  ) *
        (1 − exp (-(15:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real))  ) *
        (1 − exp (-(57:real)/(100:real))  ) * exp (-(21:real)/(100:real)) * exp (-(15:real)/(100:real))  * exp (-(21:real)/(100:real)  ) *
        (1 − exp (-(16:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real)  )) *
        (1 − exp (-(21:real)/(100:real))  ) * exp (-(21:real)/(100:real)  ) * (1 − exp (-(11:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real) )) *
        (1 − exp (-(21:real)/(100:real))  ) * exp (-(21:real)/(100:real)  ) * (1 − exp (-(12:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real))  ) *
        (1 − exp (-(21:real)/(100:real))  ) * exp (-(21:real)/(100:real)  ) * (1 − exp (-(15:real)/(100:real)  )) +
        (1 − exp (-(23:real)/(100:real)  )) * (1 − exp (-(22:real)/(100:real))  ) *
        (1 − exp (-(21:real)/(100:real))  ) * exp (-(21:real)/(100:real)  ) * (1 − exp (-(16:real)/(100:real)  ))
	+ (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(57:real)/(100:real) ) *
         exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) * exp (-(21:real)/(100:real) ) * (1 − exp (-(11:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(57:real)/(100:real) ) *
        exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) * exp (-(21:real)/(100:real) ) * (1 − exp (-(12:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(57:real)/(100:real) ) *
        exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) )  * exp (-(21:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(57:real)/(100:real) ) *
        exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) )* exp (-(21:real)/(100:real) ) * (1 − exp (-(16:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(11:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(12:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(16:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(11:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(12:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(23:real)/(100:real) ) *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(16:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(11:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real) ) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(12:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real)) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(57:real)/(100:real) )) * exp (-(21:real)/(100:real )) * exp (-(15:real)/(100:real)) *
        exp (-(21:real)/(100:real) ) * (1 − exp (-(16:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(11:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(12:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) *
        (1 − exp (-(23:real)/(100:real) )) * exp (-(22:real)/(100:real) ) *  exp (-(16:real)/(100:real) )  *
        (1 − exp (-(21:real)/(100:real ))) * exp (-(21:real)/(100:real) ) * (1 − exp (-(16:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(12:real)/(100:real) ) *
        exp (-(46:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real ))) * exp (-(21:real)/(100:real) ) *
        (1 − exp (-(11:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(12:real)/(100:real) ) *
        exp (-(46:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real ))) * exp (-(21:real)/(100:real) ) *
        (1 − exp (-(12:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(12:real)/(100:real) ) *
        exp (-(46:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real ))) * exp (-(21:real)/(100:real) ) *
        (1 − exp (-(15:real)/(100:real) )) +
        (1 − exp (-(42:real)/(100:real) )) * (1 − exp (-(57:real)/(100:real) )) * exp (-(12:real)/(100:real) ) *
        exp (-(46:real)/(100:real) ) * (1 − exp (-(15:real)/(100:real ))) * exp (-(21:real)/(100:real) ) *
        (1 − exp (-(16:real)/(100:real) ))
        +(1 - exp (-(12:real)/(100:real))) * (1 - exp (-(15:real)/(100:real))) * exp (-(21:real)/(100:real)) * (1 - exp (-(11:real)/(100:real))) +
        (1 - exp (-(12:real)/(100:real))) * (1 - exp (-(15:real)/(100:real)))  * exp (-(21:real)/(100:real)) * (1 - exp (-(12:real)/(100:real))) +
        (1 - exp (-(12:real)/(100:real))) * (1 - exp (-(15:real)/(100:real))) * exp (-(21:real)/(100:real)) * (1 - exp (-(15:real)/(100:real))) +
        (1 - exp (-(12:real)/(100:real))) * (1 - exp (-(15:real)/(100:real))) * exp (-(21:real)/(100:real)) * (1 - exp (-(16:real)/(100:real))) +
        exp (-(12:real)/(100:real)) * (1 - exp (-(46:real)/(100:real))) * (1 - exp (-(15:real)/(100:real))) * exp (-(21:real)/(100:real)) *
        (1 - exp (-(11:real)/(100:real))) +
    	exp (-(12:real)/(100:real)) * (1 - exp (-(46:real)/(100:real))) * (1 - exp (-(15:real)/(100:real))) * exp (-(21:real)/(100:real)) *
    	(1 - exp (-(12:real)/(100:real))) +
    	exp (-(12:real)/(100:real)) * (1 - exp (-(46:real)/(100:real))) * (1 - exp (-(15:real)/(100:real))) * exp (-(21:real)/(100:real)) *
    	(1 - exp (-(15:real)/(100:real))) +
    	exp (-(12:real)/(100:real)) * (1 - exp (-(46:real)/(100:real))) * (1 - exp (-(15:real)/(100:real))) * exp (-(21:real)/(100:real)) *
    	(1 - exp (-(16:real)/(100:real)))
    	+ (1 − exp (-(21:real)/(100:real))) * (1 − exp (-(11:real)/(100:real))) +
  	(1 − exp (-(21:real)/(100:real))) * (1 − exp (-(12:real)/(100:real))) +
  	(1 − exp (-(21:real)/(100:real))) * (1 − exp (-(15:real)/(100:real))) +
  	(1 − exp (-(21:real)/(100:real))) * (1 − exp (-(16:real)/(100:real))))``;
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)
(*--------------------------------------------------------------------------------------------------*)



val _ = export_theory();

(*--------------------------------------------------------------------------------------------------*)
        (*------------------------------------------------------------------------------------*)
                     (*-----------------------------------------------------*)
		                   (*---------------------------*)
				           (*-----------*)
					       (*----*)

