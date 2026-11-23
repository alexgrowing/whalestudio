import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZpowMulMemPow

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.LatClass

variable {k : Type} [Field k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [Fintype n] [DecidableEq n] [DecidableEq n'] in
theorem aff_low (x₀ : Matrix n n' k) (y) (w : n' → k) (s : k) :
    affPt (c := c + 1) 1 x₀ y *ᵥ Sum.elim w (Pi.single 0 s) = Sum.elim (x₀ *ᵥ w) (Pi.single 0 s) := by
  ext (r | l)
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, affPt, basePt, Free, Pi.single_apply]
  · simp [mulVec, dotProduct, Fintype.sum_sum_type, affPt, basePt, Free, Pi.single_apply]

omit [Fintype n] [DecidableEq n] [DecidableEq n'] in
theorem aff_row (x₀ : Matrix n n' k) (y) (w : n' → k) (i : Fin (c + 1)) (s : k) (l : Fin c) :
    (affPt (c := c) 1 x₀ y *ᵥ Sum.elim w (Pi.single i s)) (.inr l) = affPt 1 x₀ y (.inr l) (.inr i) * s := by
  have : ∀ r, affPt (c := c) 1 x₀ y (.inr l) (.inl r) = 0 := fun r => by simp [affPt, basePt, Free]
  simp [mulVec, dotProduct, Fintype.sum_sum_type, this, Pi.single_apply]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem aff_diag (x₀ : Matrix n n' k) (y) (i l : Fin c) (h : i ≤ l) :
    affPt (c := c) 1 x₀ y (.inr l) (.inr i.castSucc) = if l = i then 1 else 0 := by
  have : ¬ l < i := not_lt.2 h
  simp [affPt, basePt, Free, this, Fin.ext_iff]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
  {ϖ : kˣ} {ψ : AddChar k Circle} {ν : Measure k}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [BorelSpace k] [DecidableEq n]
  [DecidableEq n'] in
theorem exists_supp {p : ℕ} {Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} {x₀ : Matrix n n' k}
    (h : opE ψ ν p Ψ x₀ ≠ 0) : ∃ y, Ψ (affPt p x₀ y) ≠ 0 := by
  by_contra H
  push Not at H
  exact h (by simp [opE, H])

theorem bounds (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1) [ν.IsAddHaarMeasure]
    {g' : GL n' k} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k} {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ g' e' z')) (latOf h))
    (hp : ∀ x y, MapsLat y (latOf (nfBasis ϖ g' e' z')) (latOf h) → Ψ (x + (ϖ : k) • y) = Ψ x)
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) (i : Fin (c + 1)) {a : ℤ}
    (ha : topCoord (latOf h) i = powInt ϖ a) : e' i.succ - 1 ≤ a ∧ a ≤ e' i.castSucc := by
  constructor
  · obtain ⟨v, hv, hv0, hvi⟩ : (ϖ : k) ^ a ∈ topCoord (latOf h) i := ha ▸ (zpow_mem_pow hϖ).2 le_rfl
    have key : -((ϖ : k) * ((ϖ : k) ^ (-e' i.succ) * (ϖ : k) ^ a)) ∈ 𝒪[k] := by
      refine Unram.mem_of_psi hψ fun t ht => ?_
      let y : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k :=
        Matrix.of fun r s => if s = .inr i.succ then t * (ϖ : k) ^ (-e' i.succ) * v r else 0
      have hy : MapsLat y (latOf (nfBasis ϖ g' e' z')) (latOf h) := fun w hw => by
        have : y *ᵥ w = (t * ((ϖ : k) ^ (-e' i.succ) * w (.inr i.succ))) • v := by
          ext r; simp [y, mulVec, dotProduct]; ring
        rw [this]
        refine smul_mem_lat (mul_mem ht ?_) hv
        rw [← mem_pow_zero (ϖ := ϖ), zpow_mul_mem_pow]
        simpa using (mem_nf.1 hw).2 i.succ
      have := Unram.psi_ch_eq_one ψ ν Ψ x₀ h0 ((ϖ : k) • y) (fun r s hf => ?_) fun x => hp x y hy
      · convert this using 2
        simp [ch, y, hvi]; ring
      · simp only [y, Matrix.smul_apply, Matrix.of_apply]
        split_ifs with e
        · subst e
          rcases r with r | r
          · simp [Free] at hf
          · rw [hv0 r (by simp only [Free, Fin.val_succ] at hf; rw [Fin.lt_def]; omega)]; simp
        · simp
    rw [neg_mem_iff, ← mem_pow_zero (ϖ := ϖ), ← zpow_add₀ ϖ.ne_zero, ← zpow_one_add₀ ϖ.ne_zero,
      zpow_mem_pow hϖ] at key
    omega
  · obtain ⟨y, hy⟩ := exists_supp h0
    have := hs _ hy _ (col_mem_nf i.castSucc ((zpow_mem_pow hϖ).2 le_rfl))
    rw [← zpow_mem_pow hϖ, ← ha]
    refine ⟨_, this, fun l hl => ?_, ?_⟩
    · rw [aff_row, aff_diag _ _ _ _ hl.le, if_neg hl.ne', zero_mul]
    · rw [aff_row, aff_diag _ _ _ _ le_rfl, if_pos rfl, one_mul]

omit [BorelSpace k] in
theorem first_mem (hϖ : valuation k (ϖ : k) = uniformizer k)
    {g' : GL n' k} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k} {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ g' e' z')) (latOf h))
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) :
    ((ϖ ^ e' 0 : kˣ) : k) • (Sum.elim (x₀ *ᵥ z') (Pi.single 0 1) : n ⊕ Fin (c + 1) → k) ∈ latOf h ∧
      ∀ w ∈ latOf g', (Sum.elim (x₀ *ᵥ w) 0 : n ⊕ Fin (c + 1) → k) ∈ latOf h := by
  obtain ⟨y, hy⟩ := exists_supp h0
  constructor
  · have := hs _ hy _ (col_mem_nf 0 ((zpow_mem_pow hϖ).2 le_rfl))
    rw [aff_low] at this
    convert this using 1
    ext (r | l)
    · simp [mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
    · simp [Pi.single_apply]
  · intro w hw
    have := hs _ hy (Sum.elim w (Pi.single 0 0)) (mem_nf.2 ⟨by simpa using hw, fun i => by simpa using zero_mem_pow⟩)
    rw [aff_low] at this
    simpa using this

theorem step_normal (H : NormalFormModN k) (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1)
    [ν.IsAddHaarMeasure] {j : ℕ} {e' : Fin (c + 1 + 1) → ℤ} {z' : n' → k}
    (he' : ∀ i, -(j : ℤ) ≤ e' i ∧ e' i ≤ 0) (hz' : ∀ i, z' i ∈ 𝒪[k]) {h : GL (n ⊕ Fin (c + 1)) k}
    {Ψ : Matrix (n ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1 + 1)) k → ℂ}
    (hs : ∀ x, Ψ x ≠ 0 → MapsLat x (latOf (nfBasis ϖ 1 e' z')) (latOf h))
    (hp : ∀ x y, MapsLat y (latOf (nfBasis ϖ 1 e' z')) (latOf h) → Ψ (x + (ϖ : k) • y) = Ψ x)
    {x₀ : Matrix n n' k} (h0 : opE ψ ν 1 Ψ x₀ ≠ 0) :
    ∃ r ∈ R k n (c + 1) 1, ∃ (e : Fin (c + 1) → ℤ) (z : n → k),
      (∀ i, -((j + 1 : ℕ) : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (∀ i, z i ∈ 𝒪[k]) ∧
        latOf (r * h) = latOf (normalBasis ϖ e z) := by
  obtain ⟨u, hu, g, e, z, hl, hm⟩ := H ϖ hϖ n (c + 1) h
  have ht : ∀ i, topCoord (latOf h) i = powInt ϖ (e i) := fun i => by
    rw [← topCoord_R (Subgroup.mem_sup_right hu) h i, hl, topCoord_nf]
  refine ⟨embX _ g⁻¹ * u, mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right hu), e,
    (g⁻¹).val *ᵥ z, fun i => ?_, ?_, ?_⟩
  · have := bounds hϖ hψ hs hp h0 i (ht i)
    have := he' i.succ
    have := he' i.castSucc
    push_cast
    omega
  · obtain ⟨h1, h2⟩ := first_mem hϖ hs h0
    have h3 := (hm _).1 (h2 z' (mem_latOf_one.2 hz'))
    rw [← mulVec_mem_latOf u, N_fix hu _ (fun l hl => by simp [Fin.ext_iff, hl.ne']), hl] at h1
    have h4 := smul_mem_lat (t := (ϖ : k) ^ (-e' 0))
      (mem_pow_zero.1 ((zpow_mem_pow hϖ).2 (by have := he' 0; omega))) (mem_nf.1 h1).1
    have h5 := sub_mem h3 h4
    change z ∈ latOf g
    convert h5 using 1
    have : (ϖ : k) ^ e' 0 ≠ 0 := zpow_ne_zero _ ϖ.ne_zero
    ext r
    simp
    field_simp
    ring
  · rw [mul_assoc, latOf_mul_congr _ hl, embX_mul_nf, inv_mul_cancel, nfBasis_one]

end GlobalTheory.LatClass
