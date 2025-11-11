Theory connectivity
Ancestors matching contraction fsgraph genericGraph pred_set list arithmetic rich_list relation combin cardinal
Libs hurdUtils

Overload V[local] = “nodes (G :fsgraph)”
Overload E[local] = “fsgedges (G :fsgraph)”



(* LEMMAS *)

(* list lemmas*)

Theorem HD_FRONT:
  ∀l. l = x::y::zs ⇒ HD (FRONT l) = HD l
Proof
  simp []
QED

Theorem ALL_DISTINCT_HD_EQ_LAST:
  ∀l. l ≠ [] ∧ ALL_DISTINCT l ∧ HD l = LAST l ⇒ ∃x. l = [x]
Proof
  rw [EL_ALL_DISTINCT_EL_EQ]
  >> ‘HD l = EL 0 l’ by METIS_TAC [EL]
  >> drule_then strip_assume_tac LAST_EL
  >> ‘EL 0 l = EL (PRE (LENGTH l)) l’ by fs []
  >> pop_assum mp_tac >> ntac 3 (pop_assum K_TAC) >> disch_tac
  >> rw [GSYM LENGTH_EQ_1]
  >> gvs [NOT_NIL_EQ_LENGTH_NOT_0]
  >> first_x_assum (gvs o wrap o GSYM)
QED

Theorem adjacent_append_iff:
  ∀xs ys a b. adjacent (xs ++ ys) a b ⇔ adjacent xs a b ∨ adjacent ys a b ∨ (xs ≠ [] ∧ ys ≠ [] ∧ a = LAST xs ∧ b = HD ys)
Proof
  rpt gen_tac >> reverse eq_tac
  >- (rpt strip_tac >> simp [adjacent_append1, adjacent_append2]
      >> gvs [] >> rw [adjacent_EL, LAST_EL]
      >> gvs [NOT_NIL_EQ_LENGTH_NOT_0]
      >> qexists ‘PRE $ LENGTH xs’ >> rw [EL_APPEND]
      >> simp [GSYM ADD1, iffLR SUC_PRE]
     )
  >> Cases_on ‘adjacent xs a b’ >- simp []
  >> Cases_on ‘adjacent ys a b’ >- simp []
  >> simp [] >> disch_tac
  >> Cases_on ‘xs = []’ >- gvs []
  >> Cases_on ‘ys = []’ >- gvs []
  >> qpat_x_assum ‘adjacent _ _ _’ mp_tac
  >> simp [adjacent_EL] >> strip_tac
  >> Suff ‘i + 1 = LENGTH xs’
  >- (rw [LAST_EL, EL_APPEND]
      >> ‘i = PRE $ LENGTH xs’ suffices_by (disch_then (simp o wrap))
      >> simp []
     )
  >> Cases_on ‘i + 1 < LENGTH xs’
  >- (‘adjacent xs a b’ suffices_by simp []
      >> irule (iffRL adjacent_EL)
      >> qexists ‘i’ >> gvs [EL_APPEND]
     )
  >> CCONTR_TAC >> ‘LENGTH xs < i + 1’ by simp []
  >> ‘adjacent ys a b’ suffices_by simp []
  >> irule (iffRL adjacent_EL)
  >> qexists ‘i - LENGTH xs’ >> rw [EL_APPEND]
QED


(* There exists a first member satisfying a predicate *)
Theorem MEM_SPLIT_PRED:
  ∀l v P. MEM v l ∧ P v ⇒ ∃pfx sfx u. l = pfx ++ [u] ++ sfx ∧ P u ∧ ∀e. MEM e pfx ⇒ ~P e
Proof
  Induct_on ‘l’ >> simp []
  >> rw []
  >- (qexistsl [‘[]’, ‘l’, ‘h’] >> simp []
     )
  >> Cases_on ‘P h’
  >- (qexistsl [‘[]’, ‘l’, ‘h’] >> simp []
     )
  >> first_x_assum drule_all >> rw []
  >> qexistsl [‘h::pfx’, ‘sfx’, ‘u’] >> simp [DISJ_IMP_THM]
QED

Theorem list_not_adjacent_sing:
  (∀a b. ~adjacent l a b) ⇔ l = [] ∨ ∃e. l = [e]
Proof
  simp [EQ_IMP_THM, DISJ_IMP_THM, PULL_EXISTS] >> CCONTR_TAC >> gvs []
  >> Cases_on ‘l’ >> gvs []
  >> rename [‘t ≠ []’] >> Cases_on ‘t’ >> gvs []
  >> gvs [adjacent_iff] >> METIS_TAC []
QED

(* Set lemmas *)

Theorem MAX_SET_lemma:
  ∀A B. FINITE A ∧ FINITE B ∧ (∀a. a ∈ A ⇒ ∃b. b ∈ B ∧ a ≤ b) ⇒ MAX_SET A ≤ MAX_SET B
Proof
  rw [] >> DEEP_INTRO_TAC MAX_SET_ELIM >> simp []
  >> rw [] >> DEEP_INTRO_TAC MAX_SET_ELIM >> simp []
  >> rpt strip_tac
  >- (ASM_SET_TAC []
     )
  >> METIS_TAC [LE_TRANS]
QED

Theorem MAX_SET_lemma2:
  ∀A B. FINITE A ∧ FINITE B ∧ (∃b. b ∈ B ∧ MAX_SET A ≤ b) ⇒ MAX_SET A ≤ MAX_SET B
Proof
  rw [] >> irule MAX_SET_lemma >> rw []
  >> qexists ‘b’ >> ‘a ≤ MAX_SET A’ suffices_by simp [LE_TRANS]
  >> Cases_on ‘A = ∅’
  >- gvs []
  >> METIS_TAC [MAX_SET_DEF]
QED

Theorem INJ_FINITE_CARD_BIJ:
  ∀f A B. FINITE A ∧ FINITE B ∧ CARD A = CARD B ∧ INJ f A B ⇒ BIJ f A B
Proof
  rw [] >> Suff ‘B = IMAGE f A’
  >- (Rewr' >> irule INJ_IMAGE_BIJ >> qexists ‘B’ >> simp []
     )
  >> drule INJ_IMAGE
  >> drule INJ_IMAGE_SUBSET
  >> drule INJ_CARD_IMAGE_EQ >> rw []
  >> ONCE_REWRITE_TAC [EQ_SYM_EQ]
  >> irule cardinalTheory.CARD_SUBSET_EQ >> rw []
QED

(* Graph lemmas *)
Theorem path_prefix:
  ∀(G :fsgraph) p q. path G p ∧ q ≠ [] ∧ q <<= p ⇒ path G q
Proof
  rw [path_def, walk_def]
  >- (first_x_assum irule
      >> pop_assum mp_tac >> rw [MEM_EL]
      >> qexists ‘n’
      >> drule IS_PREFIX_LENGTH >> drule is_prefix_el >> rw []
     )
  >- (first_x_assum irule >> gvs [IS_PREFIX_APPEND]
      >> irule adjacent_append1 >> simp []
     )
  >> drule_all IS_PREFIX_ALL_DISTINCT >> simp []
QED


Theorem walk_adjoin:
  ∀(G :fsgraph) p q. walk G p ∧ walk G q ∧ LAST p = HD q ⇒ walk G (FRONT p ++ q)
Proof
  rw [walk_def]
  >- (last_x_assum irule >> METIS_TAC [LIST_NOT_NIL, MEM_FRONT])
  >- simp []
  >> Cases_on ‘adjacent p v1 v2’
  >- simp []
  >> Cases_on ‘adjacent q v1 v2’
  >- simp []
  >> gvs [adjacent_append_iff]
  >- (ntac 2 (pop_assum K_TAC) >> ‘adjacent p v1 v2’ suffices_by simp []
      >> pop_assum mp_tac >> rw [adjacent_EL, LENGTH_FRONT]
      >> qexists ‘i’ >> simp []
      >> conj_tac >> irule EL_FRONT >> simp [NULL_EQ_NIL, LENGTH_FRONT]
     )
  >> ONCE_REWRITE_TAC [adjacent_SYM] >> last_x_assum irule
  >> qpat_x_assum ‘_ = HD q’ (ONCE_REWRITE_TAC o wrap o SYM)
  >> simp [FRONT_BY_TAKE, LAST_EL]
  >> ‘PRE (LENGTH p − 1) < LENGTH p − 1’ by gvs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_FRONT, PRE_SUB1]
  >> dxrule_then (simp o wrap) EL_TAKE
  >> irule (iffRL adjacent_EL)
  >> qexists ‘PRE (LENGTH p − 1)’ >> gvs [NOT_NIL_EQ_LENGTH_NOT_0, LENGTH_FRONT, PRE_SUB1]
QED

Theorem path_adjoin:
  ∀(G :fsgraph) p q. path G p ∧ path G q ∧ LAST p = HD q ∧ ALL_DISTINCT (FRONT p ++ q) ⇒ path G (FRONT p ++ q)
Proof
  rw [path_def, walk_adjoin]
QED


(* MAIN THEOREMS *)

(* A-B path *)
Definition AB_path_def:
  AB_path (G :fsgraph) A B p ⇔ path G p ∧ A ⊆ V ∧ B ⊆ V ∧ A ∩ (set p) = {HD p} ∧ B ∩ (set p) = {LAST p}
End

Theorem AB_path_def_alt:
  ∀G A B p. AB_path (G :fsgraph) A B p ⇔ path G p ∧ A ⊆ V ∧ B ⊆ V ∧ (∀v. MEM v p ⇒ (v ∈ A ⇔ v = HD p) ∧ (v ∈ B ⇔ v = LAST p))
Proof
  rw [AB_path_def] >> eq_tac
  >- ASM_SET_TAC []
  >> simp [INTER_DEF, EXTENSION] >> rw []
  >> (eq_tac
      >- ASM_SET_TAC []
      >> disch_tac >> ‘MEM x p’ by gvs [path_def, walk_def, HEAD_MEM, LAST_MEM]
      >> ASM_SET_TAC []
     )
QED

Theorem AB_path_HD_LAST[simp]:
  ∀G A B p. AB_path (G :fsgraph) A B p ⇒ HD p ∈ A ∧ LAST p ∈ B
Proof
  rw [AB_path_def] >> ASM_SET_TAC []
QED

Theorem AB_path_MEM_EQ:
  ∀G A B p v. AB_path (G :fsgraph) A B p ∧ MEM v p ⇒ (v = HD p ⇔ v ∈ A) ∧ (v = LAST p ⇔ v ∈ B)
Proof
  ASM_SET_TAC [AB_path_def_alt]
QED

Theorem AB_path_sing:
  ∀G A B v. A ⊆ V ∧ B ⊆ V ∧ v ∈ V ∧ v ∈ A ∩ B ⇒ AB_path G A B [v]
Proof
  rw [AB_path_def] >> ASM_SET_TAC []
QED


Theorem AB_path_cases:
  ∀G A B p. AB_path (G :fsgraph) A B p ⇔ path G p ∧ A ⊆ V ∧ B ⊆ V ∧
                                         ((∃v. v ∈ A ∩ B ∧ p = [v]) ∨
                                          (∃a b p0. a ∈ (A DIFF B) ∧
                                                    b ∈ (B DIFF A) ∧
                                                    p = a::(SNOC b p0) ∧
                                                    ∀v. MEM v p0 ⇒ v ∉ A ∧ v ∉ B)
                                         )
Proof
  rw [AB_path_def] >> eq_tac >> rw []
  >- (‘p ≠ []’ by gvs [path_def, walk_def]
      >> Cases_on ‘LENGTH p ≤ 1’
      >- (disj1_tac >> ‘1 = LENGTH p’ by gvs [NOT_NIL_EQ_LENGTH_NOT_0]
          >> gvs [LENGTH1] >> ASM_SET_TAC []
         )
      >> disj2_tac >> gvs [EXTENSION, NOT_LE]
      >> CCONTR_TAC >> gvs []
     )
  >> cheat
QED

(* Theorem AB_path_cases: *)
(*   ∀G A B p. AB_path (G :fsgraph) A B p ⇔ path G p ∧ A ⊆ V ∧ B ⊆ V ∧ *)
(*                                ((∃v. v ∈ A ∩ B ∧ p = [v]) ∨ *)
(*                                 (∃a b p0. a ∈ A ∧ b ∈ B ∧ p = a::p0 ⧺ [b] ∧ ∀v. MEM v p0 ⇒ v ∉ A ∧ v ∉ B) *)
(*                                ) *)
(* Proof *)
(*   rw [AB_path_def] >> eq_tac >> rw [] *)
(*   >- (‘ALL_DISTINCT p’ by gvs [path_def] *)
(*       >> ‘p ≠ []’ by gvs [path_def, walk_def] *)
(*       >> Cases_on ‘HD p = LAST p’ *)
(*       >- (gvs [] >> disj1_tac >> qexists ‘LAST p’ *)
(*           >> ‘A ∩ B ≠ ∅’ by (rw [Once EXTENSION] >> qexists ‘LAST p’ >> ASM_SET_TAC []) *)
(*           >> STRONG_CONJ_TAC *)
(*           >- ASM_SET_TAC [] *)
(*           >> drule_all ALL_DISTINCT_HD_EQ_LAST >> rw [] *)
(*          ) *)
(*       >> disj2_tac *)
(*       >> sg ‘2 ≤ LENGTH p’ *)
(*       >- (Suff ‘2 ≤ CARD (set p)’ *)
(*           >- (‘CARD (set p) ≤ LENGTH p’ by METIS_TAC [CARD_LIST_TO_SET] *)
(*               >> simp [] *)
(*              ) *)
(*           >> ‘FINITE (set p)’ by simp [FINITE_LIST_TO_SET] *)
(*           >> sg ‘2 = CARD {HD p; LAST p}’ *)
(*           >- (‘HD p ∉ {LAST p}’ by ASM_SET_TAC [] >> rw [CARD_DEF]) *)
(*           >> POP_ORW >> irule CARD_SUBSET >> ASM_SET_TAC [] *)
(*          ) *)
(*       >> qexistsl [‘HD p’, ‘LAST p’] *)
(*       >> ‘HD p ∈ A ∧ LAST p ∈ B’ by ASM_SET_TAC [] >> simp [] *)
(*       >> gvs [INTER_DEF, EXTENSION] *)
(*       >> sg ‘∃p0. p = HD p::(p0 ⧺ [LAST p])’ *)
(*       >- (qexists ‘FRONT (TL p)’ >> rw [GSYM SNOC_APPEND] *)
(*           >> ‘0 < LENGTH (TL p)’ by rw [LENGTH_TL] >> ‘TL p ≠ []’ by gvs [NOT_NIL_EQ_LENGTH_NOT_0] *)
(*           >> Suff ‘LAST p = LAST (TL p)’ *)
(*           >- (Rewr' >> simp [SNOC_LAST_FRONT] *)
(*              ) *)
(*           >> METIS_TAC [LIST_NOT_NIL, LAST_DEF] *)
(*          ) *)
(*       >> qexists ‘p0’ >> simp [] *)
(*       >> ntac 2 strip_tac *)
(*       >> gvs [EL_ALL_DISTINCT_EL_EQ] *)
(*       >> cheat *)
(*      ) *)
(*   >- (simp [INTER_DEF] >> ASM_SET_TAC []) *)
(*   >- (simp [INTER_DEF] >> ASM_SET_TAC []) *)
(*   >- (simp [] *)
(*      ) *)

(* QED *)





(*   rw [AB_path_def] >> eq_tac *)
(*   >- (rw [] *)
(*       >> ‘ALL_DISTINCT p’ by gvs [path_def] *)
(*       >> ‘p ≠ []’ by gvs [path_def, walk_def] *)
(*       >> Cases_on ‘HD p = LAST p’ *)
(*       >- (gvs [] >> disj1_tac >> qexists ‘LAST p’ *)
(*           >> ‘A ∩ B ≠ ∅’ by (rw [Once EXTENSION] >> qexists ‘LAST p’ >> ASM_SET_TAC []) *)
(*           >> STRONG_CONJ_TAC *)
(*           >- ASM_SET_TAC [] *)
(*           >> drule_all ALL_DISTINCT_HD_EQ_LAST >> rw [] *)
(*          ) *)
(*       >> disj2_tac *)
(*       >> qexistsl [‘HD p’, ‘LAST p’] *)
(*       >> ‘HD p ∈ A ∧ LAST p ∈ B’ by ASM_SET_TAC [] >> simp [] *)
(*       >> sg ‘2 ≤ LENGTH p’ *)
(*       >- (Suff ‘2 ≤ CARD (set p)’ *)
(*           >- (‘CARD (set p) ≤ LENGTH p’ by METIS_TAC [CARD_LIST_TO_SET] *)
(*               >> simp [] *)
(*              ) *)
(*           >> ‘FINITE (set p)’ by simp [FINITE_LIST_TO_SET] *)
(*           >> sg ‘2 = CARD {HD p; LAST p}’ *)
(*           >- (‘HD p ∉ {LAST p}’ by ASM_SET_TAC [] >> rw [CARD_DEF]) *)
(*           >> POP_ORW >> irule CARD_SUBSET >> ASM_SET_TAC [] *)
(*          ) *)
(*       >> ‘(∃P0. p = HD p::(p0 ⧺ [LAST p])) ∧ ∀v p0. p = HD p::(p0 ⧺ [LAST p]) ∧ MEM v p0 ⇒ v ∉ A ∧ v ∉ B’ *)
(*         suffices_by METIS_TAC [] >> STRONG_CONJ_TAC *)
(*       >- (qexists ‘FRONT (TL p)’ *)
(*           >> ‘p = HD p::TL p’ by gvs [Once LIST_NOT_NIL] *)
(*           >> sg ‘TL p ≠ []’ *)
(*           >- (‘2 ≤ LENGTH (HD p :: TL p)’ by METIS_TAC [] *)
(*               >> gvs [LENGTH] *)
(*               >> ‘0 < LENGTH (TL p)’ by simp [] *)
(*               >> rw [NOT_NIL_EQ_LENGTH_NOT_0] *)
(*              ) *)
(*           >> ‘LAST p = LAST (TL p)’ by METIS_TAC [LAST_DEF] *)
(*           >> POP_ORW >> rw [APPEND_FRONT_LAST] *)
(*          ) *)
(*       >> ntac 4 strip_tac *)
(*       >> sg ‘p0' = p0’ *)
(*       >- cheat *)
(*       >> gvs [] *)
(*       >> Suff ‘HD p ∉ set p0 ∧ LAST p ∉ set p0’ *)
(*       >- cheat *)
(*       >> cheat *)
(*       ) *)
(*   >> cheat *)
(* QED *)

Theorem AB_path_sing_iff:
  ∀G A B v. A ⊆ V ∧ B ⊆ V ∧ v ∈ V ⇒ (v ∈ A ∩ B ⇔ AB_path G A B [v])
Proof
  rw [AB_path_def] >> ASM_SET_TAC []
QED

Theorem FINITE_num_path[simp]:
  FINITE {p | path (G :fsgraph) p}
Proof
  irule SUBSET_FINITE_I >> qexists ‘{p | set p ⊆ V ∧ ALL_DISTINCT p}’
  >> irule_at Any FINITE_ALL_DISTINCT_LISTS >> simp [SUBSET_DEF, path_def, walk_def]
QED

Theorem FINITE_num_AB_path[simp]:
  FINITE {p | AB_path G A B p}
Proof
  irule SUBSET_FINITE_I >> qexists ‘{p | path G p}’ >> rw [FINITE_num_path, AB_path_def, SUBSET_DEF]
QED

(* (A-B) Separator *)
Definition separator_def:
  separator (G :fsgraph) A B vs ⇔ A ⊆ V ∧ B ⊆ V ∧ vs ⊆ V ∧ ∀p. AB_path G A B p ⇒ ∃v. MEM v p ∧ v ∈ vs
End

Theorem separator_SYM:
  separator G A B vs ⇔ separator G B A vs
Proof
  ‘∀A B. separator G A B vs ⇒ separator G B A vs’ suffices_by METIS_TAC []
  >> rw [separator_def, AB_path_def]
  >> FIRST_X_ASSUM (Q.SPEC_THEN ‘REVERSE p’ MP_TAC) >> simp [path_reversible]
  >> DISCH_THEN irule >> ‘p ≠ []’ by gvs [path_def, walk_def]
  >> simp [listTheory.HD_REVERSE, listTheory.LAST_REVERSE]
QED

Theorem separator_exists:
  ∀G A B. A ⊆ V ∧ B ⊆ V ⇒ ∃vs. separator G A B vs
Proof
  rw [separator_def, AB_path_def]
  >> qexists ‘V’
  >> rw [path_def, walk_def] >> METIS_TAC [listTheory.MEM, listTheory.list_CASES]
QED

Theorem FINITE_separator[simp]:
  ∀G A B X. separator G A B X ⇒ FINITE X
Proof
  rw [separator_def] >> METIS_TAC [FINITE_nodes, SUBSET_FINITE]
QED

Theorem FINITE_num_separator[simp]:
  ∀G A B. FINITE {X | separator G A B X}
Proof
  rpt strip_tac >> irule SUBSET_FINITE_I >> qexists ‘POW V’ >> conj_tac
  >- (irule FINITE_POW >> simp [FINITE_nodes]
     )
  >> rw [SUBSET_DEF, IN_POW, separator_def]
QED

(* A and B are A-B separators. *)
Theorem separator_AB:
  ∀G A B. A ⊆ V ∧ B ⊆ V ⇒ separator G A B A ∧ separator G A B B
Proof
  Suff ‘∀G A B. A ⊆ V ∧ B ⊆ V ⇒ separator G A B A’
  >- (rw [] >> ‘separator G B A B’ suffices_by PROVE_TAC [separator_SYM]
      >> first_x_assum irule >> simp []
     )
  >> rw [separator_def, AB_path_def]
  >> qexists ‘HD p’
  >> ‘p ≠ []’ by gvs [path_def, walk_def]
  >> gvs [INTER_DEF, Once EXTENSION] >> PROVE_TAC []
QED

Theorem separator_TRANS:
  ∀G A B X Y. separator G A B X ∧ separator G A X Y ⇒ separator G A B Y
Proof
  rw [separator_def]
  >> Suff ‘∃q. q <<= p ∧ AB_path G A X q’
  >- (rw [] >> first_x_assum (drule_then strip_assume_tac)
      >> qexists ‘v’ >> drule LIST_TO_SET_PREFIX >> ASM_SET_TAC []
     )
  >> first_x_assum (drule_then strip_assume_tac)
  >> ‘ALL_DISTINCT p’ by gvs [AB_path_def, path_def]
  >> qabbrev_tac ‘P = λv. v ∈ X’ >> gvs []
  >> drule_all_then assume_tac (MEM_SPLIT_PRED)
  >> qunabbrev_tac ‘P’ >> ntac 3 (pop_assum mp_tac) >> BETA_TAC >> rpt strip_tac
  >> qexists ‘pfx ++ [u]’ >> rw []
  >> sg ‘path G (pfx ⧺ [u])’
  >- (irule path_prefix >> simp []
      >> qexists ‘(pfx ⧺ [u] ⧺ sfx)’ >> reverse conj_tac
      >- (gvs [AB_path_def]
         )
      >> rw [IS_PREFIX_APPEND]
     )
  >> reverse $ rw [AB_path_def]
  >- ASM_SET_TAC []
  >> qpat_x_assum ‘MEM v _’ K_TAC >> qpat_x_assum ‘v ∈ X’ K_TAC
  >> gvs [AB_path_def]
  >> sg ‘ HD (pfx ⧺ [u]) = HD (pfx ⧺ [u] ⧺ sfx)’
  >- (rw [Once EQ_SYM_EQ] >> irule HD_APPEND_NOT_NIL >> simp []
     )
  >> POP_ORW
  >> ‘HD (pfx ⧺ [u] ⧺ sfx) ∉ (set sfx)’ suffices_by ASM_SET_TAC []
  >> gvs [ALL_DISTINCT_APPEND] >> first_x_assum irule
  >> Cases_on ‘pfx = []’
  >- simp []
  >> ‘HD (pfx ⧺ [u] ⧺ sfx) = HD pfx’ suffices_by simp [HEAD_MEM]
  >> simp [HD_APPEND_NOT_NIL]
QED

Theorem adjacent_remove_fsgedge[simp]:
  ∀(G :fsgraph). adjacent (remove_fsgedge e G) v1 v2 ⇔ adjacent G v1 v2 ∧ e ≠ {v1; v2}
Proof
  simp [adjacent_fsg] >> METIS_TAC []
QED



Theorem separator_remove_fsgedge_B:
  ∀G A B X e. separator (remove_fsgedge e G) A B X ∧ e ∈ E ∧ e ⊆ B ⇒ separator G A B X
Proof
  rw [separator_def]
  >> first_x_assum irule >> gvs [AB_path_def]
  >> gvs [path_def, walk_def]
  >> rpt strip_tac >> gvs []
  >> drule_then strip_assume_tac fsgraph_valid
  >> drule_then strip_assume_tac adjacent_MEM
  >> ASM_SET_TAC []
QED

Theorem separator_remove_fsgedge_A:
  ∀G A B X e. separator (remove_fsgedge e G) A B X ∧ e ∈ E ∧ e ⊆ A ⇒ separator G A B X
Proof
  rw []
  >> gvs [Once separator_SYM] >> simp [Once separator_SYM]
  >> drule_all separator_remove_fsgedge_B >> simp []
QED


(* Disjoint path *)
Definition disjoint_path_def:
  disjoint_path (G :fsgraph) p q ⇔ path G p ∧ path G q ∧ DISJOINT (set p) (set q)
End

(* Collection of sets of disjoint A-B paths *)
Definition disjoint_AB_path_sets_def:
  disjoint_AB_path_sets G A B = {paths | (∀p. p ∈ paths ⇒ AB_path G A B p) ∧ pred_set$pairwise (RC $ disjoint_path G) paths}
End

Theorem disjoint_AB_path_sets_def_alt:
  ∀(G :fsgraph) A B. disjoint_AB_path_sets G A B = {paths | (∀p. p ∈ paths ⇒ AB_path G A B p) ∧ ∀p q. p ∈ paths ∧ q ∈ paths ∧ p ≠ q ⇒ disjoint_path G p q}
Proof
  rw [disjoint_AB_path_sets_def, pairwise_def, RC_DEF, EXTENSION] >> METIS_TAC []
QED

Theorem FINITE_num_disjoint_AB_path_sets[simp]:
  ∀(G :fsgraph) A B. FINITE (disjoint_AB_path_sets G A B)
Proof
  rpt strip_tac >> irule SUBSET_FINITE_I
  >> qexists ‘POW {p | path G p}’
  >> rw [FINITE_POW, disjoint_AB_path_sets_def, AB_path_def]
  >> ASM_SET_TAC [POW_DEF]
QED


Theorem disjoint_AB_path_set_assoc:
  ∀(G :fsgraph). A ⊆ V ∧ B ⊆ V ∧ C ⊆ V ∧ separator G A C B ∧
                 CARD P = CARD B ∧ P ∈ disjoint_AB_path_sets G A B ∧
                 CARD Q = CARD B ∧ Q ∈ disjoint_AB_path_sets G B C ⇒
                 ∃R. CARD R = CARD B ∧ R ∈ disjoint_AB_path_sets G A C
Proof
  rw [disjoint_AB_path_sets_def_alt, HAS_SIZE, separator_def]
  >> ‘FINITE A ∧ FINITE B’ by METIS_TAC [FINITE_nodes, SUBSET_FINITE]
  >> sg ‘FINITE P’
  >- (‘P ⊆ {p | path G p}’ by (gvs [AB_path_def] >> ASM_SET_TAC [FINITE_num_path])
      >> METIS_TAC [FINITE_num_path, SUBSET_FINITE]
     )
  >> sg ‘FINITE Q’
  >- (‘Q ⊆ {p | path G p}’ by (gvs [AB_path_def] >> ASM_SET_TAC [FINITE_num_path])
      >> METIS_TAC [FINITE_num_path, SUBSET_FINITE]
     )
  >> sg ‘INJ LAST P B’
  >- (simp [INJ_DEF] >> conj_asm1_tac
      >- (rpt strip_tac >> last_x_assum drule >> simp [AB_path_def] >> ASM_SET_TAC []
         )
      >> rpt strip_tac >> CCONTR_TAC
      >> qpat_x_assum ‘∀p q. p ∈ P ∧ _ ⇒ _’ (drule_all_then assume_tac) >> gvs [disjoint_path_def]
      >> ‘x ≠ [] ∧ y ≠ []’ by gvs [path_def, walk_def]
      >> ntac 2 (dxrule_then assume_tac LAST_MEM) >> gvs [DISJOINT_DEF, INTER_DEF]
      >> ntac 3 (pop_assum mp_tac) >> SET_TAC [] (* optimisation *)
     )
  >> sg ‘INJ HD Q B’
  >- (simp [INJ_DEF] >> conj_asm1_tac
      >- (rpt strip_tac >> last_x_assum drule >> simp [AB_path_def] >> ASM_SET_TAC []
         )
      >> rpt strip_tac >> CCONTR_TAC
      >> qpat_x_assum ‘∀p q. p ∈ Q ∧ _ ⇒ _’ (drule_all_then assume_tac) >> gvs [disjoint_path_def]
      >> ‘x ≠ [] ∧ y ≠ []’ by gvs [path_def, walk_def]
      >> ntac 2 (dxrule_then assume_tac HEAD_MEM) >> gvs [DISJOINT_DEF, INTER_DEF]
      >> ntac 3 (pop_assum mp_tac) >> SET_TAC [] (* optimisation *)
     )
  >> ‘BIJ LAST P B’ by (irule INJ_FINITE_CARD_BIJ >> simp [])
  >> ‘BIJ HD Q B’ by (irule INJ_FINITE_CARD_BIJ >> simp [])
  >> drule_then strip_assume_tac BIJ_INV
  >> ‘BIJ (g o LAST) P Q’ by (irule BIJ_COMPOSE >> qexists ‘B’ >> simp [])
  >> qabbrev_tac ‘f = (λp. FRONT p ++ (g o LAST) p)’
  >> sg ‘∀p. p ∈ P ⇒ AB_path G B C ((g o LAST) p)’
  >- (ntac 2 strip_tac >> first_x_assum irule
      >> METIS_TAC [BIJ_DEF, INJ_DEF]
     )
  >> sg ‘∀p. p ∈ P ⇒ HD ((g o LAST) p) = LAST p’
  >- (rpt strip_tac >> qabbrev_tac ‘q = g (LAST p)’
      >> ‘q ∈ Q’ by METIS_TAC [BIJ_THM]
      >> ‘g (HD q) = q’ by gvs []
      >> simp [o_DEF]
      >> ‘INJ g B Q’ by gvs [BIJ_DEF] >> METIS_TAC [INJ_DEF]
     )
  >> sg ‘∀p. p ∈ P ⇒ HD (f p) = HD p ∧ LAST (f p) = LAST ((g o LAST) p)’
  >- (rw [Abbr ‘f’] >> ‘p ≠ []’ by METIS_TAC [AB_path_def, path_def, walk_def]
      >- (Cases_on ‘p’ >- gvs []
          >> Cases_on ‘t’
          >- (first_x_assum drule >> simp []
             )
          >> simp []
         )
      >> irule LAST_APPEND_NOT_NIL
      >> ‘(g o LAST) p ∈ Q’ by METIS_TAC [BIJ_DEF, INJ_DEF]
      >> METIS_TAC [o_DEF, AB_path_def, path_def, walk_def]
     )
  >> sg ‘∀p q. p ∈ P ∧ q ∈ Q ⇒ DISJOINT (set (FRONT p)) (set q)’
  >- (rw [DISJOINT_DEF, Once EXTENSION, Once (GSYM IMP_DISJ_THM)] >> strip_tac >> rename [‘MEM v q’]
      >> ‘ALL_DISTINCT p ∧ ALL_DISTINCT q’ by METIS_TAC [AB_path_def, path_def, BIJ_DEF, INJ_DEF]
      >> ntac 2 (qpat_x_assum ‘MEM v _’ mp_tac >> ONCE_REWRITE_TAC [MEM_SPLIT]) >> rpt strip_tac
      >> sg ‘∀n. MEM n (FRONT p) ⇒ n ∉ B’
      >- (ntac 2 strip_tac >> ‘LAST p ∈ B’ by METIS_TAC [BIJ_DEF, INJ_DEF]
          >> qpat_x_assum ‘FRONT p = _’ K_TAC
          >> qpat_x_assum ‘∀p. _ ⇒ AB_path G A B p’ drule >> simp [AB_path_def]
          >> rw [] >> ‘p ≠ []’ by gvs [path_def, walk_def]
          >> ‘MEM n p’ by METIS_TAC [MEM_FRONT_NOT_NIL]
          >> drule_all MEM_FRONT_NOT_LAST >> rw []
          >> qpat_x_assum ‘_ = {LAST p}’ mp_tac >> rw [INTER_DEF]
          >> ‘n ≠ LAST p’ by METIS_TAC []
          >> ASM_SET_TAC []
         )
      >> sg ‘∀n. MEM n l2' ⇒ n ∉ B’
      >- (ntac 2 strip_tac
          >> qpat_x_assum ‘∀p. _ ⇒ AB_path G B C p’ drule >> simp [AB_path_def]
          >> rw []
          >> cheat
         )
      >> qabbrev_tac ‘r = l1 ++ v::l2'’
      >> sg ‘AB_path G A C r’
      >- (cheat
         )
      >> last_x_assum drule >> rw [Abbr ‘r’] >> gvs [] >> METIS_TAC []
     )
  >> qexists ‘IMAGE f P’ >> conj_asm1_tac
  >- (Know ‘CARD B = CARD P’
      >- gvs []
      >> Rewr'
      >> irule INJ_CARD_IMAGE >> simp []
      >> qexists ‘IMAGE f P’ >> rw [INJ_DEF]
      >> CCONTR_TAC >> gvs [Abbr ‘f’]
      (* >> ‘HD (FRONT x ⧺ g (LAST x)) = HD (FRONT y ⧺ g (LAST y))’ by simp [] *)
      >> ‘x ≠ [] ∧ y ≠ []’ by gvs [AB_path_def, path_def, walk_def]
      >> ‘disjoint_path G x y’ by simp []
      >> sg ‘LAST x ≠ LAST y’
      >- (pop_assum mp_tac >> KILL_TAC
          >> rw [disjoint_path_def, DISJOINT_DEF, path_def, walk_def, INTER_DEF]
          >> CCONTR_TAC >> gvs []
          >> ‘MEM (LAST x) x ∧ MEM (LAST y) y’ by simp [LAST_MEM]
          >> gvs [EXTENSION] >> METIS_TAC []
         )
      >> qabbrev_tac ‘z = g (LAST x)’ >> qabbrev_tac ‘w = g (LAST y)’
      >> ‘z ≠ w ∧ z ∈ Q ∧ w ∈ Q’ by METIS_TAC [BIJ_DEF, INJ_DEF]
      >> ‘disjoint_path G z w’ by simp []
      >> sg ‘LAST z ≠ LAST w’
      >- (pop_assum mp_tac >> KILL_TAC
          >> rw [disjoint_path_def, DISJOINT_DEF, path_def, walk_def, INTER_DEF]
          >> CCONTR_TAC >> gvs []
          >> ‘MEM (LAST z) z ∧ MEM (LAST w) w’ by simp [LAST_MEM]
          >> gvs [EXTENSION] >> METIS_TAC []
         )
      >> ‘LAST (FRONT x ⧺ z) = LAST (FRONT y ⧺ w)’ by simp []
      >> ‘z ≠ [] ∧ w ≠ []’ by gvs [AB_path_def, path_def, walk_def]
      >> gvs [LAST_APPEND_NOT_NIL]
     )
  >> reverse (conj_asm1_tac >> rw [])
  >- (rename [‘f p1 ≠ f p2’]
      >> simp [disjoint_path_def] >> rpt conj_asm1_tac
      >- METIS_TAC [IN_IMAGE, AB_path_def]
      >- METIS_TAC [IN_IMAGE, AB_path_def]
      >> cheat
     )
  >> simp [AB_path_def] >> rpt $ reverse conj_asm2_tac
  >- (cheat)
  >- (cheat)
  >> simp [Abbr ‘f’] >> fs [BETA_THM]
  >> irule path_adjoin >> simp [] >> reverse conj_asm2_tac
  >- gvs [AB_path_def]
  >> rw [ALL_DISTINCT_APPEND]
  >- (irule ALL_DISTINCT_FRONT >> gvs [AB_path_def, path_def, walk_def]
     )
  >- gvs [AB_path_def, path_def, walk_def]
  >> CCONTR_TAC >> rename [‘MEM v (FRONT p)’] >> gvs []
  >> ntac 2 (qpat_x_assum ‘MEM v _’ mp_tac >> ONCE_REWRITE_TAC [MEM_SPLIT]) >> rpt strip_tac
  >> ‘ALL_DISTINCT p ∧ p ≠ []’ by gvs [path_def, walk_def]
  >> sg ‘∀n. MEM n (FRONT p) ⇒ n ∉ B’
  >- (ntac 2 strip_tac >> sg ‘n ≠ LAST p’
      >- (CCONTR_TAC >> qpat_x_assum ‘FRONT p = _’ K_TAC >> gvs [MEM_FRONT_NOT_LAST]
         )
      >> ‘MEM n p’ by METIS_TAC [LIST_NOT_NIL, MEM_FRONT]
      >> METIS_TAC [AB_path_MEM_EQ]
     )
  >> sg ‘∀n. MEM n l2' ⇒ n ∉ B’
  >- (ntac 2 strip_tac >> qabbrev_tac ‘q = (g (LAST p))’
      >> cheat
     )
  >> qabbrev_tac ‘r = l1 ++ v::l2'’
  >> sg ‘AB_path G A C r’
  >- (cheat
     )
QED







(* Definition disj_path_count_def: *)
(*   disj_path_count G A B = MAX_SET (IMAGE CARD {ps | (∀p. p ∈ ps ⇒ AB_path G A B p) ∧ pred_set$pairwise (RC $ disjoint_path G) ps}) *)
(* End *)


(* Theorem disj_path_count_econtract: *)
(*   MAX_SET (IMAGE CARD $ disjoint_AB_path_sets (G / e) A B) ≤ MAX_SET (IMAGE CARD $ disjoint_AB_path_sets G A B) *)
(* Proof *)
(*   irule MAX_SET_lemma2 >> rw [PULL_EXISTS] *)
(*   >> assume_tac (Q.SPECL [‘G / e’, ‘A’, ‘B’]) *)
(*   >> qabbrev_tac ‘k' = MAX_SET (IMAGE CARD (disjoint_AB_path_sets (G / e) A B))’ *)
(*   >> gvs [MAX_SET_TEST] *)


(*   rw [disjoint_AB_path_sets_def] >> irule MAX_SET_lemma2 >> rw [] *)
(*   >- (simp [PULL_EXISTS] >> rename [‘pairwise _ P’] *)
(*       >> reverse $ Cases_on ‘e ∈ E’ *)
(*       >- (gvs [econtract_def] >> qexists ‘P’ >> simp [] *)
(*          ) *)
(*       >> *)
(*      ) *)
(* QED *)



(* Let G = (V, E) be a graph and A, B ⊆ V. Then the minimum number of vertices separating A from B in G is equal to the maximum number of disjoint A–B paths in G. *)
Theorem mengers_thm_vertex:
  ∀(G :fsgraph) A B. A ⊆ V ∧ B ⊆ V ⇒
                     MIN_SET (IMAGE CARD {vs | separator G A B vs}) =
                     MAX_SET (IMACE CARD disjoint_AB_path_sets G A B)
Proof
  completeInduct_on ‘CARD E’ >> gvs [PULL_FORALL] >> rpt strip_tac
  >> simp [GSYM LE_ANTISYM, IMP_CONJ_THM, FORALL_AND_THM] >> gvs []
  (* >> simp [GSYM LE_ANTISYM, IMP_CONJ_THM, FORALL_AND_THM] *)
  >> reverse conj_asm2_tac
  >- (CCONTR_TAC >> gvs [NOT_LE, disj_path_count_def]
      >> qmatch_assum_abbrev_tac ‘k < MAX_SET CP’
      >> ‘MAX_SET CP ∈ CP’ by (
        irule MAX_SET_IN_SET
        >> simp [] >> rpt strip_tac
        >- (simp [Abbr ‘CP’] >> irule IMAGE_FINITE >> irule SUBSET_FINITE_I
            >> qexists ‘POW {p | path G p}’ >> simp []
            >> simp [SUBSET_DEF, IN_POW, AB_path_def]
           )
        >> gvs []
        )
      >> qabbrev_tac ‘j = MAX_SET CP’ >> markerLib.RM_ABBREV_TAC "j"
      >> gvs [Abbr ‘CP’]
      >> rename [‘k < CARD P’]
      >> ‘FINITE P’ by (
        irule SUBSET_FINITE_I >> qexists ‘{p | AB_path G A B p}’ >> simp [SUBSET_DEF, FINITE_AB_path]
        )
      >> sg ‘k ∈ (IMAGE CARD {vs | separator G A B vs})’
      >- (qunabbrev_tac ‘k’ >> irule MIN_SET_IN_SET
          >> simp [EXTENSION] >> METIS_TAC [separator_exists]
         )
      >> gvs [] >> rename [‘separator G A B X’]
      >> drule_then ASSUME_TAC FINITE_separator
      >> drule_all_then assume_tac PHP
      >> pop_assum mp_tac >> simp []
      >> ‘∀p. p ∈ P ⇒ ∃v. v ∈ X ∧ MEM v p’ by METIS_TAC [separator_def]
      >> gvs [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM]
      >> rename [‘MEM (f _) _’] >> qexists ‘f’ >> simp [INJ_DEF]
      >> rpt strip_tac >> gvs [disjoint_path_def, pairwise_def, relationTheory.RC_DEF]
      >> rename [‘f v1 = f v2’]
      >> first_x_assum $ qspecl_then [‘v1’, ‘v2’] mp_tac >> rw []
      >> ‘MEM (f v1) v1 ∧ MEM (f v2) v2’ by METIS_TAC []
      >> gvs [] >> ASM_SET_TAC []
     )
  >> rw [LE_ANTISYM]
  (* >> completeInduct_on ‘CARD E’ >> gvs [PULL_FORALL] >> rw [] *)
  >> qmatch_abbrev_tac ‘(k:num) ≤ _’
  >> sg ‘k ∈ (IMAGE CARD {vs | separator G A B vs})’
  >- (qunabbrev_tac ‘k’ >> irule MIN_SET_IN_SET
      >> simp [EXTENSION] >> METIS_TAC [separator_exists]
     )
  >> gvs [] >> rename [‘CARD X ≤ _’]
  >> Cases_on ‘E = ∅’
  >- (sg ‘∀v1 v2. ~adjacent G v1 v2’
      >- (rw [adjacent_fsg])
      >> gvs [disj_path_count_def] (*  *)
      >> sg ‘X = A ∩ B’
      >- (qpat_x_assum ‘MIN_SET _ = _’ mp_tac >> qpat_x_assum ‘separator _ _ _ _’ mp_tac
          >> DEEP_INTRO_TAC MIN_SET_ELIM >> rw []
          >- (simp [EXTENSION] >> METIS_TAC [separator_exists]
             )
          >> gvs [PULL_EXISTS]
          >> simp [EXTENSION]
          >> sg ‘∀p. AB_path G A B p ⇒ ∃x. p = [x] ∧ x ∈ A ∧ x ∈ B’
          >- (rw [AB_path_def, path_def, walk_def, list_not_adjacent_sing]
              >> gvs [] >> ASM_SET_TAC []
             )
          >> sg ‘∀x. x ∈ A ∧ x ∈ B ⇒ x ∈ X’
          >- (rw [] >> gvs [separator_def]
              >> sg ‘AB_path G A B [x]’
              >- (rw [AB_path_def] >> ASM_SET_TAC []
                 )
              >> METIS_TAC [MEM]
             )
          >> rw [EQ_IMP_THM]
          >- (CCONTR_TAC >> sg ‘separator G A B (X DELETE x)’
              >- (rw [separator_def]
                  >- ASM_SET_TAC [separator_def]
                  >> first_x_assum drule >> simp [PULL_EXISTS]
                 )
              >> first_x_assum drule
              >> ‘FINITE X’ by METIS_TAC [FINITE_separator] >> simp [CARD_DELETE]
              >> ‘CARD x' ≠ 0’ by (strip_tac >> gvs []) >> simp []
             )
          >> CCONTR_TAC >> sg ‘separator G A B (X DELETE x)’
          >- (rw [separator_def]
              >- ASM_SET_TAC [separator_def]
              >> first_x_assum drule >> simp [PULL_EXISTS]
             )
          >> first_x_assum drule
          >> ‘FINITE X’ by METIS_TAC [FINITE_separator] >> simp [CARD_DELETE]
          >> ‘CARD x' ≠ 0’ by (strip_tac >> gvs []) >> simp []
         )
      >> qabbrev_tac ‘P = IMAGE (λx. [x]) X’
      >> qmatch_abbrev_tac ‘CARD X ≤ MAX_SET (IMAGE CARD Ps)’
      >> sg ‘FINITE Ps’
      >- (irule SUBSET_FINITE_I >> qexists ‘POW {l | set l ⊆ V ∧ LENGTH l ≤ CARD V}’ >> conj_tac
          >- (simp[FINITE_POW] >> irule FINITE_BOUNDED_LISTS >> simp []
             )
          >> simp [SUBSET_DEF] >> simp [IN_POW, Abbr ‘Ps’] >> rw [SUBSET_DEF]
          >- (rename [‘p ∈ ps’, ‘MEM v p’]
              >> ‘AB_path G A B p’ by simp []
              >> pop_assum mp_tac
              >> simp [NoAsms, AB_path_def, path_def, walk_def] >> METIS_TAC []
             )                  (* ALL_DISTINCT_CARD_LIST_TO_SET *)
          >> rename [‘p ∈ ps’]
          >> ‘ALL_DISTINCT p’ by METIS_TAC [AB_path_def, path_def]
          >> simp [GSYM ALL_DISTINCT_CARD_LIST_TO_SET]
          >> irule CARD_SUBSET >> simp []
          >> gvs [AB_path_def, path_def, walk_def] >> ASM_SET_TAC []
         )
      >> irule X_LE_MAX_SET >> simp []
      >> qexists ‘P’ >> conj_tac
      >- (‘FINITE A’ by METIS_TAC [SUBSET_FINITE, FINITE_nodes] >> simp [Abbr ‘P’, CARD_IMAGE_INJ])
      >> simp [Abbr ‘Ps’, Abbr ‘P’, PULL_EXISTS] >> rw [pairwise_def]
      >- (rw [AB_path_def] >> ASM_SET_TAC []
         )
      >> rw [RC_DEF, disjoint_path_def] >> ASM_SET_TAC []
     )
  >> CCONTR_TAC >> gvs [NOT_LE]

  >> ‘∃e. e ∈ E’ by (pop_assum mp_tac >> SET_TAC [])
  >> drule_then strip_assume_tac alledges_valid >> rename [‘e = {x; y}’]
  >> drule_then strip_assume_tac econtract_nodes
  >> qabbrev_tac ‘G' = econtract G e’
  >> qabbrev_tac ‘v = freshnode G’
  >> qabbrev_tac ‘A' = if x ∈ A ∨ y ∈ A then (v INSERT (A ∩ nodes G')) else A’
  >> qabbrev_tac ‘B' = if x ∈ B ∨ y ∈ B then (v INSERT (B ∩ nodes G')) else B’
  >> sg ‘CARD (fsgedges G') < CARD E’
  >- (simp [Abbr ‘G'’] >> irule econtract_fsgedges_CARD >> gvs []
     )
  >> sg ‘A' ⊆ nodes G'’
  >- (simp [Abbr ‘A'’]
      >> Cases_on ‘x ∈ A ∨ y ∈ A’
      >- (simp [])
      >> simp [] >> ASM_SET_TAC []
     )
  >> last_assum $ drule_then drule
  >> sg ‘B' ⊆ nodes G'’
  >- (simp [Abbr ‘B'’]
      >> Cases_on ‘x ∈ B ∨ y ∈ B’
      >- (simp [])
      >> simp [] >> ASM_SET_TAC []
     )
  >> disch_then (drule_then strip_assume_tac)


  >> qabbrev_tac ‘k' = MIN_SET (IMAGE CARD {vs | separator G' A' B' vs})’
  >> sg ‘k' ∈ IMAGE CARD {vs | separator G' A' B' vs}’
  >- (qunabbrev_tac ‘k'’ >> irule MIN_SET_IN_SET
      >> simp [EXTENSION] >> METIS_TAC [separator_exists]
     )
  >> gvs [] >> rename [‘separator G' A' B' Y’]

QED
