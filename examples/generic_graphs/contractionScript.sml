Theory contraction
Ancestors fsgraph genericGraph pred_set

open bossLib hurdUtils;


Overload V[local] = “nodes (G :fsgraph)”
Overload E[local] = “fsgedges (G :fsgraph)”

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

Definition vmin_def:
  vmin v1 v2 = if vlt v1 v2 then v1 else v2
End

Definition vmax_def:
  vmax v1 v2 = if vlt v1 v2 then v2 else v1
End


Definition vertex_merge_def:
  vertex_merge G x y = if x ∈ V ∧ y ∈ V ∧ x ≠ y then
                         let
                           v = vmin x y;
                           u = vmax x y;
                           vs = V DELETE u;
                           es = {e | e ∈ E ∧ u ∉ e} ∪ {{w; v} | w | w ≠ v ∧ {w; u} ∈ E};
                         in
                           fsgAddEdges es (fsgAddNodes vs emptyG)
                       else G
End




(* Edge Contraction e = {x; y} *)
Definition econtract_def:
  econtract (G :fsgraph) e = if e ∈ E then
                    let
                      x = CHOICE e;
                      y = CHOICE (REST e);
                    in
                      vertex_merge G x y
                  else G
End

val _ = set_fixity "/" (Infixl 600)
Overload "/" = “econtract”

(* Theorem CHOICE_DISJ: *)
(*   ∀x s. CHOICE (x INSERT s) = x ∨ CHOICE (x INSERT s) ∈ s *)
(* Proof *)
(*   rw [] >> qabbrev_tac ‘t = x INSERT s’ *)
(*   >> qsuff_tac ‘CHOICE t ∈ t’ *)
(*   >- ASM_SET_TAC [] *)
(*   >> irule CHOICE_DEF >> rw [Abbr ‘t’] *)
(* QED *)

(* Theorem econtract_def_alt: *)
(*   ∀G x y. econtract G {x; y} = if {x; y} ∈ E then *)
(*                                  vertex_merge G x y *)
(*                                else G *)
(* Proof *)
(*   rw [econtract_def] *)
(*   >> mp_tac (Q.SPECL [‘x’, ‘{y}’] $ INST_TYPE [alpha |-> “:unit+num”] CHOICE_DISJ) >> rw [] >> POP_ORW *)
(*   >- (POP_ORWb *)
(*      ) *)
(* QED *)


(* Theorem econtract_fsgedges_CARD_LT: *)
(*   ∀(G :fsgraph) e. e ∈ E ⇒ (CARD o fsgedges) (econtract e G) < CARD E *)
(* Proof *)
(*   rw [econtract_def] >> qabbrev_tac ‘x = CHOICE e’ >> qabbrev_tac ‘y = CHOICE (e DELETE x)’ *)
(*   >> *)
(* QED *)
