import Mathlib

noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.Inj

theorem cup_fil {K B : Type*} [Field K] [CommRing B] (P : Subring B) (t : B) (ht : t ∈ P) (o : K →+* B)
    (ho : ∀ k, o k ∈ P) {H1 H2 H3 : Type*} [AddCommGroup H1] [Module K H1] [AddCommGroup H2] [Module K H2]
    [AddCommGroup H3] [Module K H3] (F1 : ℕ → Set H1) (F2 : ℕ → Set H2) (F3 : ℕ → Set H3)
    (cup : H1 →ₗ[K] H2 →ₗ[K] H3) (hcup : ∀ r s, ∀ x ∈ F1 r, ∀ y ∈ F2 s, cup x y ∈ F3 (r + s))
    (d : ℕ) (hd : ∀ e, d < e → ∀ x ∈ F3 e, x = 0)
    {m m' : ℕ} (b : Module.Basis (Fin m) K H1) (w : Fin m → ℕ)
    (hb : ∀ s, b s ∈ F1 (w s) ∧ ∀ x ∈ F1 (w s + 1), b.coord s x = 0)
    (b' : Module.Basis (Fin m') K H2) (w' : Fin m' → ℕ)
    (hb' : ∀ s, b' s ∈ F2 (w' s) ∧ ∀ x ∈ F2 (w' s + 1), b'.coord s x = 0)
    (C1 : Module.Dual K H1 → B) (hC1 : ∀ r φ, (∀ x ∈ F1 (r + 1), φ x = 0) → t ^ r * C1 φ ∈ P)
    (C2 : Module.Dual K H2 → B) (hC2 : ∀ r φ, (∀ x ∈ F2 (r + 1), φ x = 0) → t ^ r * C2 φ ∈ P)
    (φ : Module.Dual K H3) :
    t ^ d * ∑ s, ∑ s', C1 (b.coord s) * C2 (b'.coord s') * o (φ (cup (b s) (b' s'))) ∈ P := by
  rw [Finset.mul_sum]
  refine P.sum_mem fun s _ => ?_
  rw [Finset.mul_sum]
  refine P.sum_mem fun s' _ => ?_
  by_cases h : w s + w' s' ≤ d
  · have h1 := hC1 (w s) (b.coord s) (hb s).2
    have h2 := hC2 (w' s') (b'.coord s') (hb' s').2
    have e : t ^ d * (C1 (b.coord s) * C2 (b'.coord s') * o (φ (cup (b s) (b' s')))) =
        t ^ (d - (w s + w' s')) * (t ^ w s * C1 (b.coord s)) * (t ^ w' s' * C2 (b'.coord s')) *
          o (φ (cup (b s) (b' s'))) := by
      have : d = (d - (w s + w' s')) + w s + w' s' := by omega
      conv_lhs => rw [this]
      ring
    rw [e]
    exact P.mul_mem (P.mul_mem (P.mul_mem (P.pow_mem ht _) h1) h2) (ho _)
  · have h0 : cup (b s) (b' s') = 0 :=
      hd _ (by omega) _ (hcup _ _ _ (hb s).1 _ (hb' s').1)
    rw [h0, map_zero, map_zero, mul_zero, mul_zero]
    exact P.zero_mem

theorem exists_int_mul {p : ℕ} [Fact p.Prime] {T : Type*} [AddCommGroup T] [Module ℤ_[p] T]
    (v : ℚ_[p] ⊗[ℤ_[p]] T) : ∃ s : ℤ_[p], s ≠ 0 ∧ ∃ x : T, (s : ℚ_[p]) • v = (1 : ℚ_[p]) ⊗ₜ x := by
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | tmul q y =>
    obtain ⟨⟨ζ, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[p]) q
    refine ⟨s, nonZeroDivisors.ne_zero s.2, ζ • y, ?_⟩
    simp only at hs
    rw [TensorProduct.smul_tmul', TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    calc ((s : ℤ_[p]) : ℚ_[p]) • q = q * algebraMap ℤ_[p] ℚ_[p] s := by rw [smul_eq_mul, mul_comm]; rfl
      _ = algebraMap ℤ_[p] ℚ_[p] ζ := hs
      _ = ζ • (1 : ℚ_[p]) := by rw [Algebra.smul_def, mul_one]
  | add v v' hv hv' =>
    obtain ⟨s, hs, x, hx⟩ := hv
    obtain ⟨s', hs', x', hx'⟩ := hv'
    refine ⟨s * s', mul_ne_zero hs hs', s' • x + s • x', ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← hx, ← hx', smul_add]
    simp only [PadicInt.coe_mul]
    rw [← algebraMap_smul ℚ_[p] s', ← algebraMap_smul ℚ_[p] s, smul_smul, smul_smul]
    congr 2 <;> simp [PadicInt.algebraMap_apply] <;> ring

end CrystallineSemistableComparison.Inj
