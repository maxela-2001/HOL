Theory connectivity
Ancestors matching contraction fsgraph genericGraph pred_set list arithmetic rich_list
Libs hurdUtils

Overload V[local] = “nodes (G :fsgraph)”
Overload E[local] = “fsgedges (G :fsgraph)”


(* Notion of A-B path *)
(* Definition abpath_def: *)
(*   abpath (G :fsgraph) A B p ⇔ path G p ∧ A ⊆ V ∧ B ⊆ V ∧ HD p ∈ A ∧ LAST p ∈ B *)
(* End *)
Definition AB_path_def:
  AB_path (G :fsgraph) A B p ⇔ path G p ∧ A ⊆ V ∧ B ⊆ V ∧ A ∩ (set p) = {HD p} ∧ B ∩ (set p) = {LAST p}
End

Theorem AB_path_sing_inter:
  ∀G A B v. A ⊆ V ∧ B ⊆ V ∧ v ∈ V ∧ v ∈ A ∩ B ⇒ AB_path G A B [v]
Proof
  rw [AB_path_def] >> ASM_SET_TAC []
QED

Theorem FINITE_path[simp]:
  FINITE {p | path (G :fsgraph) p}
Proof
  irule SUBSET_FINITE_I >> qexists ‘{p | set p ⊆ V ∧ ALL_DISTINCT p}’
  >> irule_at Any FINITE_ALL_DISTINCT_LISTS >> simp [SUBSET_DEF, path_def, walk_def]
QED

Theorem FINITE_AB_path:
  FINITE {p | AB_path G A B p}
Proof
  irule SUBSET_FINITE_I >> qexists ‘{p | path G p}’ >> rw [FINITE_path, AB_path_def, SUBSET_DEF]
QED

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

Theorem FINITE_separator:
  ∀G A B X. separator G A B X ⇒ FINITE X
Proof
  rw [separator_def] >> METIS_TAC [FINITE_nodes, SUBSET_FINITE]
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

Definition disjoint_path_def:
  disjoint_path (G :fsgraph) p q ⇔ path G p ∧ path G q ∧ DISJOINT (set p) (set q)
End


(* TODO. rewrite wrt disjoint_path *)
Definition independent_path_def:
  independent_path (G :fsgraph) p q ⇔ path G p ∧ path G q ∧ DISJOINT (set (TL (FRONT p))) (set (TL (FRONT q)))
End

(* Theorem independent_path_sing: *)
(*   independent_path G p q ∧ AB_path G {a} {b} p ∧ AB_path G {a} {b} q ⇒ set p ∩ set q = {a; b} *)
(* Proof *)
(*   rw [independent_path_def, AB_path_def] *)
(*   >> ‘a = HD p ∧ a = HD q ∧ b = LAST p ∧ b = LAST q’ by ASM_SET_TAC [] *)
(*   >> gvs [DISJOINT_DEF] >> MP_TAC (Q.SPEC ‘p’ $ INST_TYPE listTheory.list_CASES) *)
(* QED *)


Theorem list_not_adjacent_sing:
  (∀a b. ~adjacent l a b) ⇔ l = [] ∨ ∃e. l = [e]
Proof
  simp [EQ_IMP_THM, DISJ_IMP_THM, PULL_EXISTS] >> CCONTR_TAC >> gvs []
  >> Cases_on ‘l’ >> gvs []
  >> rename [‘t ≠ []’] >> Cases_on ‘t’ >> gvs []
  >> gvs [adjacent_iff] >> METIS_TAC []
QED

(* Let G = (V, E) be a graph and A, B ⊆ V. Then the minimum number of vertices separating A from B in G is equal to the maximum number of disjoint A–B paths in G. *)
Theorem mengers_thm_vertex:
  ∀(G :fsgraph) A B. A ⊆ V ∧ B ⊆ V ⇒
                     MIN_SET (IMAGE CARD {vs | separator G A B vs}) =
                     MAX_SET (IMAGE CARD {ps | (∀p. p ∈ ps ⇒ AB_path G A B p) ∧ pred_set$pairwise (RC $ disjoint_path G) ps})
Proof
  simp [GSYM LE_ANTISYM, IMP_CONJ_THM, FORALL_AND_THM] >> reverse conj_tac
  >- (CCONTR_TAC >> gvs [NOT_LE]
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
  >> completeInduct_on ‘CARD E’ >> gvs [PULL_FORALL] >> rw []
  >> qmatch_abbrev_tac ‘(k:num) ≤ _’
  >> sg ‘k ∈ (IMAGE CARD {vs | separator G A B vs})’
  >- (qunabbrev_tac ‘k’ >> irule MIN_SET_IN_SET
      >> simp [EXTENSION] >> METIS_TAC [separator_exists]
     )
  >> gvs [] >> rename [‘CARD X ≤ _’]
  >> Cases_on ‘E = ∅’
  >- (sg ‘∀v1 v2. ~adjacent G v1 v2’
      >- (rw [adjacent_fsg])
      >> gvs []
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

     )
QED

      >> ‘FINITE P’ by (
        irule SUBSET_FINITE_I >> qexists ‘{p | abpath G A B p}’ >> simp [SUBSET_DEF, FINITE_abpath]
        )
      >> i
is_separator_def
