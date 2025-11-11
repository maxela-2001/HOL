Theory contraction
Ancestors fsgraph genericGraph pred_set

open bossLib hurdUtils;


Overload V[local] = “nodes (G :fsgraph)”
Overload E[local] = “fsgedges (G :fsgraph)”


(* An ordering on vertices *)
Definition vlt_def[simp]:
  (vlt (INL (x :unit)) (INL (y :unit)) ⇔ F) ∧
  (vlt (INR k) (INL y) ⇔ T) ∧
  (vlt (INL x) (INR m) ⇔ F) ∧
  (vlt (INR k) (INR m) ⇔ k < m)
End

Theorem vlt_TRANS:
  ∀v1 v2 v3. vlt v1 v2 ∧ vlt v2 v3 ⇒ vlt v1 v3
Proof
  Cases >> Cases >> Cases >> simp []
QED

Theorem vlt_REFL[simp]:
  ∀v. ~vlt v v
Proof
  Cases >> simp []
QED

Theorem vlt_ANTISYM:
  ∀v1 v2. ~(vlt v1 v2 ∧ vlt v2 v1)
Proof
  Cases >> Cases >> simp []
QED

Theorem vlt_CASES:
  ∀v1 v2. vlt v1 v2 ∨ v1 = v2 ∨ vlt v2 v1
Proof
  Cases >> Cases >> simp []
QED

(* A way to express nodes within an edge *)
Theorem ev_lemma:
  ∀e. FINITE e ∧ CARD e = 2 ⇒ ∃m n. vlt m n ∧ e = {m; n}
Proof
  rw [] >> gvs [CARDEQ2, INSERT2_lemma] >> METIS_TAC [vlt_CASES]
QED

val ev_def = new_specification ("ev_def", ["ev1", "ev2"], SRULE [SKOLEM_THM, GSYM RIGHT_EXISTS_IMP_THM] ev_lemma)

Theorem ev_in_nodes:
  ∀(G :fsgraph) e. e ∈ E ⇒ ev1 e ∈ e ∧ ev2 e ∈ e ∧ ev1 e ∈ V ∧ ev2 e ∈ V ∧ ev1 e ≠ ev2 e
Proof
  rw [] >> drule_then strip_assume_tac alledges_valid
  >> ‘FINITE e ∧ CARD e = 2’ by simp []
  >> drule_all ev_def >> gvs [] >> rw [INSERT2_lemma] >> METIS_TAC []
QED

Theorem alledges_valid_vlt:
  ∀(G :fsgraph). e ∈ E ⇒ ∃a b. a ∈ V ∧ b ∈ V ∧ a ≠ b ∧ e = {a; b} ∧ vlt a b ∧ ev1 e = a ∧ ev2 e = b
Proof
  ntac 2 strip_tac
  >> drule_then strip_assume_tac alledges_valid
  >> ‘FINITE e ∧ CARD e = 2’ by gvs []
  >> rw [] >> metis_tac [ev_in_nodes, ev_def]
QED


Definition vmin_def:
  vmin v1 v2 = if vlt v1 v2 then v1 else v2
End

Definition vmax_def:
  vmax v1 v2 = if vlt v1 v2 then v2 else v1
End

(* Introduction to a fresh node to a graph. *)
Theorem freshness_lemma:
  ∀(G : fsgraph). ∃n. n ∉ V
Proof
  gen_tac >> irule $ iffLR NOT_IN_FINITE >> simp []
  >> sg ‘INJ INR univ(:num) univ(:unit + num)’
  >- (simp [INJ_DEF])
  >> drule FINITE_INJ >> simp []
QED

val freshnode_def = new_specification ("freshnode_def", ["freshnode"], CONV_RULE SKOLEM_CONV freshness_lemma);

(* A “contraction” without requiring {x;y} to be an edge. *)
Definition vertex_merge_def:
  vertex_merge G x y = if x ∈ V ∧ y ∈ V ∧ x ≠ y then
                         let
                           v = freshnode G;
                           vs = v INSERT (V DIFF {x; y});
                           es = {e | e ∈ E ∧ x ∉ e ∧ y ∉ e} ∪ {{w; v} | w ≠ y ∧ {w; x} ∈ E} ∪ {{w; v} | w ≠ x ∧ {w; y} ∈ E};
                         in
                           fsgAddEdges es (fsgAddNodes vs emptyG)
                       else G
End

Theorem vertex_merge_SYM:
  vertex_merge G x y = vertex_merge G y x
Proof
  rw [vertex_merge_def] >> gvs []
  >> cong_tac (SOME 1)
  >- SET_TAC []
  >> cong_tac (SOME 1)
  >> SET_TAC []
QED

(* Edge Contraction e = {x; y} *)
Definition econtract_def:
  econtract (G :fsgraph) e = if e ∈ E then
                               vertex_merge G (ev1 e) (ev2 e)
                             else G
End

Theorem econtract_def_alt:
  ∀(G :fsgraph) v1 v2. econtract (G :fsgraph) {v1; v2} = if {v1; v2} ∈ E then
                                                           vertex_merge G v1 v2
                                                         else G
Proof
  rw [econtract_def]
  >> qabbrev_tac ‘e = {v1;v2}’
  >> drule_then strip_assume_tac ev_in_nodes
  >> wlog_tac ‘ev1 e = v1’ [‘v1’, ‘v2’]
  >- (Suff ‘ev1 e = v2’
      >- (rw [] >> ‘ev2 e = v1’ by ASM_SET_TAC [] >> gvs [vertex_merge_SYM]
         )
      >> ASM_SET_TAC []
     )
  >> Suff ‘ev2 e = v2’
  >- gvs [vertex_merge_SYM]
  >> ASM_SET_TAC []
QED

val _ = set_fixity "/" (Infixl 600)
Overload "/" = “econtract”



Theorem gen_freshnode_in_econtract:
  ∀(G :fsgraph) e. e ∈ E ⇒ freshnode G ∈ nodes (G / e)
Proof
  rw [econtract_def, freshnode_def, vertex_merge_def, ev_def] >> METIS_TAC [ev_in_nodes]
QED

Theorem freshnode_in_econtract:
  ∀(G :fsgraph) e. e ∈ E ⇒ ∃v. v ∈ nodes (G / e) ∧ v ∉ V
Proof
  rw [] >> qexists ‘freshnode G’ >> rw [gen_freshnode_in_econtract, freshnode_def]
QED

Theorem freshnode_fsgedges:
  ∀(G :fsgraph) e. freshnode G ∈ e ⇒ e ∉ E
Proof
  rpt strip_tac >> drule_then strip_assume_tac alledges_valid
  >> ‘freshnode G ∉ V’ by simp [freshnode_def] >> ASM_SET_TAC []
QED

Theorem freshnode_fsgedges_alt:
  ∀(G :fsgraph) v. {v; freshnode G} ∉ E ∧ {freshnode G; v} ∉ E
Proof
  rw [] >> irule freshnode_fsgedges >> SET_TAC []
QED


Theorem econtract_nodes:
  ∀(G :fsgraph) e. e ∈ E ⇒ nodes (G / e) = (freshnode G) INSERT V DIFF e
Proof
  rw [econtract_def]
  >> drule_then strip_assume_tac alledges_valid_vlt
  >> ntac 3 POP_ORW >> rw [vertex_merge_def]
QED

Theorem econtract_fsgedges:
  ∀(G :fsgraph) e. e ∈ E ⇒ fsgedges (G / e) =
                           {e' | e' ∈ E ∧ e' ∩ e = ∅} ∪
                           {{v; freshnode G} | v ∉ e ∧ ∃w. w ∈ e ∧ {v; w} ∈ E}
Proof
  rw [econtract_def] >> drule_then strip_assume_tac alledges_valid_vlt >> ntac 3 POP_ORW
  >> rw [vertex_merge_def, fsgedges_fsgAddEdges, Once EXTENSION] >> eq_tac
  >- (Cases_on ‘freshnode G ∈ x’
      >- (wlog_tac ‘m = freshnode G’ [‘m’, ‘n’]
          >- gvs []
          >> ‘x ∉ E’ by simp [freshnode_fsgedges]
          >> rw [] >> ASM_SET_TAC [freshnode_def]
         )
      >> disch_tac >> disj1_tac
      >> gvs [] >> ASM_SET_TAC []
     )
  >> strip_tac >> gvs []
  >- (drule_then strip_assume_tac alledges_valid >> rename [‘x = {m; n}’]
      >> ‘∀v. v ∈ V ⇒ v ≠ freshnode G’ by METIS_TAC [freshnode_def]
      >> ‘m ≠ freshnode G ∧ n ≠ freshnode G’ by METIS_TAC []
      >> qexistsl [‘m’, ‘n’] >> simp []
      >> conj_asm1_tac
      >- (CCONTR_TAC >> gvs [INSERT_INTER])
      >> conj_asm1_tac
      >- (CCONTR_TAC >> gvs [INSERT_INTER])
      >> gvs []
     )
  >> qexistsl [‘v’, ‘freshnode G’]
  >- (drule_then strip_assume_tac fsgraph_valid >> simp [] >> reverse conj_asm2_tac
      >- METIS_TAC [freshnode_def]
      >> disj1_tac >> disj2_tac >> qexists ‘v’ >> simp []
     )
  >> drule_then strip_assume_tac fsgraph_valid >> simp [] >> reverse conj_asm2_tac
  >- METIS_TAC [freshnode_def]
  >> disj2_tac >> qexists ‘v’ >> simp []
QED

Theorem econtract_fsgedges_CARD:
  ∀(G :fsgraph) e. e ∈ E ⇒ CARD (fsgedges (econtract G e)) < CARD E
Proof
  rw [econtract_fsgedges]
  >> drule_then strip_assume_tac alledges_valid
  >> qabbrev_tac ‘fv = freshnode G’ >> ‘fv ∉ V’ by simp [Abbr ‘fv’, freshnode_def]
  >> qabbrev_tac ‘E' = E DELETE e’
  >> sg ‘CARD E' < CARD E’
  >- (rw [Abbr ‘E'’, CARD_DELETE]
      >> CCONTR_TAC >> gvs []
     )
  >> irule arithmeticTheory.LESS_EQ_LESS_TRANS >> first_assum (irule_at Any)
  >> irule INJ_CARD >> conj_asm1_tac
  >- simp [Abbr ‘E'’]
  >> qabbrev_tac ‘f = λe'. if e' ∈ E ∧ e' ∩ e = ∅ then e' else
                             let v = @v'. e' = {v'; fv}
                             in
                               if {v; a} ∈ E then {v; a} else {v; b}
                 ’
  >> qexists ‘f’ >> ONCE_REWRITE_TAC [INJ_DEF] >> conj_tac
  >- (simp [UNION_DEF] >> ntac 2 strip_tac
      >- (simp [Abbr ‘f’, Abbr ‘E'’] >> pop_assum mp_tac >> SET_TAC []
         )
      >- (‘x ∉ E’ by gvs [Abbr ‘fv’, freshnode_fsgedges] >> simp [Abbr ‘f’, Abbr ‘E'’]
          >> SELECT_ELIM_TAC >> conj_tac
          >- (qexists ‘v’ >> simp [])
          >> strip_tac >> disch_tac >> ‘v = x'’ by ASM_SET_TAC []
          >> gvs [] >> ASM_SET_TAC []
         )
      >> ‘x ∉ E’ by gvs [Abbr ‘fv’, freshnode_fsgedges] >> simp [Abbr ‘f’, Abbr ‘E'’]
      >> SELECT_ELIM_TAC >> conj_tac
      >- (qexists ‘v’ >> simp [])
      >> strip_tac >> disch_tac >> ‘v = x'’ by ASM_SET_TAC [] >> gvs []
      >> conj_tac
      >- METIS_TAC []
      >> ASM_SET_TAC []
     )
  >> ntac 3 strip_tac
  >> Cases_on ‘x ∈ E ∧ x ∩ e = ∅’
  >- (Cases_on ‘y ∈ E ∧ y ∩ e = ∅’
      >- (rw [Abbr ‘f’]
         )
      >> rw [Abbr ‘f’] >> ASM_SET_TAC []
     )
  >> Cases_on ‘y ∈ E ∧ y ∩ e = ∅’
  >- (rw [Abbr ‘f’] >> ASM_SET_TAC [])
  >> ‘∀v1. {v1; fv} ∉ E’ by METIS_TAC [freshnode_fsgedges_alt]
  >> (gvs [Abbr ‘f’]
      >> ‘(@v'. {v; fv} = {v'; fv}) = v’ by SET_TAC [] >> POP_ORW
      >> ‘(@v''. {v'; fv} = {v''; fv}) = v'’ by SET_TAC [] >> POP_ORW
      >> ASM_SET_TAC []
     )
QED


(* conterparts of U ⊆ V(G) in V(G / e) *)
Definition nodes_merge_def:
  nodes_merge G x y U = if U ⊆ V ∧ (x ∈ V ∨ y ∈ V) then
                    (freshnode G) INSERT (U DIFF {x; y})
                  else
                    U
End

Definition nodes_merge'_def:
  nodes_merge' G e U = nodes_merge G ev1 ev2 U
End

Theorem nodes_merge_econtract:
  ∀G e U. U ⊆ V ∧ e ∈ E ∧ e = {x; y} ⇒ nodes_merge G x y U ⊆ nodes (G / e)
Proof
  rw [nodes_merge_def]
  >> rw [gen_freshnode_in_econtract, econtract_nodes]
  >> ASM_SET_TAC []
QED
