import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableEmbeddingLevM

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section aux

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

def ARel (T : V →ₗ[ℂ] V') (M : Wd.SlopeTestRemainingChoices S (Pr V)) (M' : Wd.SlopeTestRemainingChoices S (Pr V')) : Prop := ∀ x y, Rel T (M x y) (M' x y)

def BRel (T : V →ₗ[ℂ] V') (M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Pr V))) (M' : Wd.M2 (Wd.SlopeTestRemainingChoices S (Pr V'))) : Prop :=
  ∀ i j, ARel T (M i j) (M' i j)

theorem arel_neg {M : Wd.SlopeTestRemainingChoices S (Pr V)} {M' : Wd.SlopeTestRemainingChoices S (Pr V')} (hM : ARel T M M') : ARel T (-M) (-M') := by
  intro x y
  exact rel_neg (hM x y)

theorem arel_sub {M N : Wd.SlopeTestRemainingChoices S (Pr V)} {M' N' : Wd.SlopeTestRemainingChoices S (Pr V')} (hM : ARel T M M') (hN : ARel T N N') :
    ARel T (M - N) (M' - N') := by
  intro x y
  rw [Matrix.sub_apply, Matrix.sub_apply, sub_eq_add_neg, sub_eq_add_neg]
  exact rel_add (hM x y) (rel_neg (hN x y))

theorem arel_zero : ARel T (0 : Wd.SlopeTestRemainingChoices S (Pr V)) 0 := by
  intro x y
  exact rel_zero

theorem arel_one : ARel T (1 : Wd.SlopeTestRemainingChoices S (Pr V)) 1 := by
  intro x y
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact rel_one
  · exact rel_zero

theorem arel_mul {M N : Wd.SlopeTestRemainingChoices S (Pr V)} {M' N' : Wd.SlopeTestRemainingChoices S (Pr V')} (hM : ARel T M M') (hN : ARel T N N') :
    ARel T (M * N) (M' * N') := by
  intro x y
  simp only [Matrix.mul_apply]
  exact rel_sum _ (fun c _ => rel_mul (hM x c) (hN c y))

theorem arel_smul (s : ℂ) {M : Wd.SlopeTestRemainingChoices S (Pr V)} {M' : Wd.SlopeTestRemainingChoices S (Pr V')} (hM : ARel T M M') :
    ARel T (s • M) (s • M') := by
  intro x y
  exact rel_smul s (hM x y)

theorem arel_sum {ι : Type*} (s : Finset ι) {M : ι → Wd.SlopeTestRemainingChoices S (Pr V)} {M' : ι → Wd.SlopeTestRemainingChoices S (Pr V')}
    (h : ∀ i ∈ s, ARel T (M i) (M' i)) : ARel T (∑ i ∈ s, M i) (∑ i ∈ s, M' i) := by
  intro x y
  simp only [Matrix.sum_apply]
  exact rel_sum s (fun i hi => h i hi x y)

theorem arel_io {a : Pr V} {a' : Pr V'} (h : Rel T a a') : ARel T (Wd.io (S := S) a) (Wd.io a') := by
  intro x y
  simp only [Wd.io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact h
  · exact rel_zero

theorem arel_eU (a : S) (i j : Fin 2) : ARel T (Wd.eU (A := Pr V) a i j) (Wd.eU (A := Pr V') a i j) := by
  intro x y
  simp only [Wd.eU, Matrix.of_apply]
  split_ifs
  · exact rel_one
  · exact rel_zero

theorem brel_sub {M N : Wd.M2 (Wd.SlopeTestRemainingChoices S (Pr V))} {M' N' : Wd.M2 (Wd.SlopeTestRemainingChoices S (Pr V'))} (hM : BRel T M M')
    (hN : BRel T N N') : BRel T (M - N) (M' - N') := by
  intro i j
  rw [Matrix.sub_apply, Matrix.sub_apply]
  exact arel_sub (hM i j) (hN i j)

theorem brel_smul (s : ℂ) {M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Pr V))} {M' : Wd.M2 (Wd.SlopeTestRemainingChoices S (Pr V'))} (hM : BRel T M M') :
    BRel T (s • M) (s • M') := by
  intro i j
  exact arel_smul s (hM i j)

theorem brel_one : BRel T (1 : Wd.M2 (Wd.SlopeTestRemainingChoices S (Pr V))) 1 := by
  intro i j
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact arel_one
  · exact arel_zero

theorem brel_mul {M N : Wd.M2 (Wd.SlopeTestRemainingChoices S (Pr V))} {M' N' : Wd.M2 (Wd.SlopeTestRemainingChoices S (Pr V'))} (hM : BRel T M M')
    (hN : BRel T N N') : BRel T (M * N) (M' * N') := by
  intro i j
  simp only [Matrix.mul_apply]
  exact arel_sum _ (fun c _ => arel_mul (hM i c) (hN c j))

theorem brel_transpose {M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Pr V))} {M' : Wd.M2 (Wd.SlopeTestRemainingChoices S (Pr V'))} (hM : BRel T M M') :
    BRel T Mᵀ M'ᵀ := by
  intro i j
  exact hM j i

theorem brel_lift0 {M : Wd.M2 (Pr V)} {M' : Wd.M2 (Pr V')} (hM : MRel T M M') :
    BRel T (Wd.lift0 (S := S) M) (Wd.lift0 M') := fun i j => arel_io (hM i j)

theorem arel_ins (a : S) {M : Wd.M2 (Wd.SlopeTestRemainingChoices S (Pr V))} {M' : Wd.M2 (Wd.SlopeTestRemainingChoices S (Pr V'))} (hM : BRel T M M') :
    ARel T (Wd.ins a M) (Wd.ins a M') := by
  unfold Wd.ins
  exact arel_sum _ fun i _ => arel_sum _ fun j _ => arel_mul (arel_eU a i j) (hM i j)

theorem block_relation_basisP (a : S) : BRel T (Wd.P0 (A := Pr V) a) (Wd.P0 (A := Pr V') a) :=
  fun i j => arel_eU a j i

theorem block_relation_basisQ (a : S) : BRel T (Wd.Q0 (A := Pr V) a) (Wd.Q0 (A := Pr V') a) :=
  fun i j => arel_eU a i j

theorem block_relation_height (a : S) (D : ℂ) : BRel T (Wd.Rh0 (A := Pr V) a D) (Wd.Rh0 (A := Pr V') a D) := by
  unfold Wd.Rh0
  exact brel_smul _ (brel_sub (brel_smul _ brel_one) (block_relation_basisP a))

theorem block_relation_twisted_height (a : S) (D : ℂ) : BRel T (Wd.Rht0 (A := Pr V) a D) (Wd.Rht0 (A := Pr V') a D) := by
  unfold Wd.Rht0
  exact brel_smul _ (brel_sub (brel_smul _ brel_one) (block_relation_basisQ a))

theorem brel_TTw {QQ : ℂ → Wd.M2 (Pr V)} {QQ' : ℂ → Wd.M2 (Pr V')} (hQ : ∀ Y, MRel T (QQ Y) (QQ' Y)) :
    ∀ (w : List (Wd.Letter ℂ S)) (Y : ℂ), BRel T (Wd.TTw QQ w Y) (Wd.TTw QQ' w Y)
  | [], Y => by
    unfold Wd.TTw; exact brel_lift0 (hQ Y)
  | l :: w, Y => by
    unfold Wd.TTw
    split_ifs
    · exact brel_mul (brel_TTw hQ w Y) (block_relation_height _ _)
    · exact brel_mul (block_relation_twisted_height _ _) (brel_TTw hQ w Y)

theorem arel_RRw {QQ : ℂ → Wd.M2 (Pr V)} {QQ' : ℂ → Wd.M2 (Pr V')} (hQ : ∀ Y, MRel T (QQ Y) (QQ' Y)) :
    ∀ w : List (Wd.Letter ℂ S), ARel T (Wd.RRw QQ w) (Wd.RRw QQ' w)
  | [] => by unfold Wd.RRw; exact arel_one
  | l :: w => by
    unfold Wd.RRw
    refine arel_mul (arel_RRw hQ w) (arel_ins _ ?_)
    split_ifs
    · exact brel_TTw hQ w _
    · exact brel_transpose (brel_TTw hQ w _)

end aux

section form

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}
  {S : Type} [Fintype S] [DecidableEq S]

theorem act_tr {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
    {M : Wd.SlopeTestRemainingChoices S (Pr V)} {M' : Wd.SlopeTestRemainingChoices S (Pr V')} (hM : ARel T M M') (x : Wd.Ix S → V) (a : Wd.Ix S) :
    T (∑ b, (M a b).1 (x b)) = ∑ b, (M' a b).1 (T (x b)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  exact (LinearMap.congr_fun (hM a b).1 (x b)).symm

theorem one_val (ρ : ℕ) : ((1 : Fin (1 + ρ + 1)) : ℕ) = 1 := by
  rw [Fin.val_one']
  exact Nat.mod_eq_of_lt (by omega)

def cfEquiv (ρ : ℕ) : {l : Fin ρ // (0 : Fin (ρ + 1)).val ≤ l.val} ≃ {l : Fin (1 + ρ) // (1 : Fin (1 + ρ + 1)).val ≤ l.val} where
  toFun l := ⟨shS l.1, by rw [one_val]; simp [shS]⟩
  invFun l := ⟨⟨l.1.val - 1, by have h := (one_val ρ).symm.trans_le l.2; omega⟩, Nat.zero_le _⟩
  left_inv l := by ext; simp [shS]
  right_inv l := by
    have h := (one_val ρ).symm.trans_le l.2
    ext; simp [shS]; omega

theorem glue_cf (c : Fin (1 + ρ) → ℂ) (c'' : P5.Cf ρ 0) :
    P5.glue 1 c (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (cfEquiv ρ) c'') =
      consC (c ⟨0, by omega⟩) (P5.glue 0 (0 : Fin ρ → ℂ) c'') := by
  funext l
  by_cases hl : l.val = 0
  · have e : l = ⟨0, by omega⟩ := Fin.ext hl
    rw [e, consC_zero]
    unfold P5.glue
    split_ifs with h
    · rw [one_val] at h; simp at h
    · rfl
  · have e : l = shS ⟨l.val - 1, by omega⟩ := Fin.ext (by simp [shS]; omega)
    rw [e, consC_sh]
    unfold P5.glue
    have h : ((1 : Fin (1 + ρ + 1)) : ℕ) ≤ (shS (⟨l.val - 1, by omega⟩ : Fin ρ)).val := by
      rw [one_val]; simp [shS]
    have h' : ((0 : Fin (ρ + 1)) : ℕ) ≤ (⟨l.val - 1, by omega⟩ : Fin ρ).val := Nat.zero_le _
    rw [dif_pos h, dif_pos h']
    have : (⟨shS ⟨l.val - 1, by omega⟩, h⟩ : {l : Fin (1 + ρ) // (1 : Fin (1 + ρ + 1)).val ≤ l.val}) =
        cfEquiv ρ ⟨⟨l.val - 1, by omega⟩, h'⟩ := rfl
    rw [this, MeasurableEquiv.piCongrLeft_apply_apply]

theorem glue_zero (c c' : Fin ρ → ℂ) (c'' : P5.Cf ρ 0) : P5.glue 0 c c'' = P5.glue 0 c' c'' := by
  funext l
  unfold P5.glue
  have h : ((0 : Fin (ρ + 1)) : ℕ) ≤ l.val := Nat.zero_le _
  rw [dif_pos h, dif_pos h]

theorem prod_cf (c'' : P5.Cf ρ 0) :
    (∏ l, ‖MeasurableEquiv.piCongrLeft (fun _ => ℂ) (cfEquiv ρ) c'' l‖ ^ (-2 : ℤ)) = ∏ l, ‖c'' l‖ ^ (-2 : ℤ) := by
  refine (Fintype.prod_equiv (cfEquiv ρ) _ _ fun l => ?_).symm
  rw [MeasurableEquiv.piCongrLeft_apply_apply]

theorem form_tr {t : ℂ} (ht : t ≠ 0) {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}
    (hmap : μs.map (B2.levM k ρ) = μ) (x y : Wd.Ix S → RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (c : Fin (1 + ρ) → ℂ) (hc : c ⟨0, by omega⟩ = t) (c₀ : Fin ρ → ℂ) :
    P5.form μ 1 x y c =
      P5.form μs 0 (fun a => trL ht z z' π π' (x a)) (fun a => trL ht z z' π π' (y a)) c₀ := by
  unfold P5.form
  rw [← (volume_measurePreserving_piCongrLeft (fun _ => ℂ) (cfEquiv ρ)).integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun c'' => ?_)
  simp only
  rw [prod_cf, glue_cf, hc]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pairAt_tr ht hmap]
  rw [glue_zero 0 c₀]

end form

section words

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}
  {S : Type} [Fintype S] [DecidableEq S]
  {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
  {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
  {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
  {st : Fr.Start (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'))}
  {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
  {sts : Fr.Start (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))))} {s : ℂ}
  {μ : Measure (Mt k (1 + ρ))} {μs : Measure (Mt k ρ)}

theorem rrform_tr {t : ℂ} (ht : t ≠ 0) (hz : inWb k ρ z) (hz' : inWb k ρ z')
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y) (hmap : μs.map (B2.levM k ρ) = μ) (w : List (Wd.Letter ℂ S))
    (x y : Wd.Ix S → RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (c : Fin (1 + ρ) → ℂ) (hc : c ⟨0, by omega⟩ = t) (c₀ : Fin ρ → ℂ) :
    P5.RRform L st μ 1 w x y c =
      P5.RRform Ls sts μs 0 w (fun a => trL ht z z' π π' (x a)) (fun a => trL ht z z' π π' (y a)) c₀ := by
  unfold P5.RRform
  rw [form_tr ht hmap _ _ c hc c₀]
  congr 1
  funext a
  exact act_tr (arel_RRw (fun Y => qqi_rel ht hz hz' hL hLs hst hsts Y) w) x a

theorem ph_tr {t : ℂ} (ht : t ≠ 0) (hz : inWb k ρ z) (hz' : inWb k ρ z')
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y) (hmap : μs.map (B2.levM k ρ) = μ) (w : List (Wd.Letter ℂ S))
    (x y : Wd.Ix S → RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (c : Fin (1 + ρ) → ℂ) (c₀ : Fin ρ → ℂ) :
    P5.ph L st μ ⟨0, by omega⟩ w x y c t =
      ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        P5.RRform Ls sts μs 0 w (fun a => trL ht z z' π π' (P5.act (P5.bTl L ⟨0, by omega⟩ w) x a))
          (fun a => trL ht z z' π π' (P5.act (P5.bTl L ⟨0, by omega⟩ w) y a)) c₀ := by
  unfold P5.ph
  have e : (⟨0, by omega⟩ : Fin (1 + ρ)).succ = (1 : Fin (1 + ρ + 1)) := by
    ext; rw [one_val]; rfl
  rw [e, rrform_tr ht hz hz' hL hLs hst hsts hmap w _ _ _ (by simp) c₀]

end words

end Formalism.FourierDecayAlt.P.PBH
