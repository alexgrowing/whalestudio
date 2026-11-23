import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FdProps

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

theorem det_nU (H : Matrix (Fin n) (Fin n) ℂ) : (nU H).det = 1 := by
  simp [nU, Matrix.det_fromBlocks_zero₂₁]

theorem fz_twist (m : ℕ) (e : ℤ) (z : ℂ) (y : M2 n) : fz m e z y = y.det ^ e * fz m 0 z y := by
  simp [fz, mul_assoc]

theorem det_unit_of_inK {k : M2 n} (hk : InK k) : star k.det * k.det = 1 := by
  have h := congrArg Matrix.det hk.2
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
  exact h

theorem rhoP_twist {Kg : Type} (ι : Kg → M2 n) (hK : ∀ k, InK (ι k)) (m : ℕ) (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (k : Kg) : rhoP ι m e Y k * (ι k).det ^ e = rhoP ι m 0 Y k := by
  unfold rhoP
  rw [fz_twist m e 0 (ι k)]
  simp only [star_mul, star_zpow₀]
  have hu : star (ι k).det * (ι k).det = 1 := det_unit_of_inK (hK k)
  have h1 : star (ι k).det ^ e * (ι k).det ^ e = 1 := by
    rw [← mul_zpow, hu, _root_.one_zpow]
  linear_combination (star ((u2 (ι k))⁻¹ * Y * u1 (ι k)).trace * star (fz m 0 0 (ι k))) * h1

theorem tOp_twist {Kg : Type} [MeasurableSpace Kg] (μ : Measure Kg) (ι : Kg → M2 n) (hK : ∀ k, InK (ι k)) (m : ℕ)
    (e : ℤ) (Y : Matrix (Fin n) (Fin n) ℂ) (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b x : M2 n) (z : ℂ) :
    tOp μ ι (rhoP ι m e Y) ψ a b (fz m e z) x =
      (x.det ^ e * a.det ^ e * b.det ^ e) * tOp μ ι (rhoP ι m 0 Y) ψ a b (fz m 0 z) x := by
  unfold tOp
  rw [← integral_const_mul]
  congr 1
  funext k
  have hin : (∫ (t : Fin n → Fin n → ℝ), fz m e z (x * ι k * a * nU (herm t) * b) * ψ t)
      = (x.det ^ e * (ι k).det ^ e * a.det ^ e * b.det ^ e) *
        ∫ (t : Fin n → Fin n → ℝ), fz m 0 z (x * ι k * a * nU (herm t) * b) * ψ t := by
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [fz_twist m e z, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, det_nU, mul_one,
      mul_zpow, mul_zpow, mul_zpow]
    ring
  rw [hin, ← rhoP_twist ι hK m e Y k]
  ring

theorem eRed : ERed := by
  intro h n m e hmn Kg _ _ _ _ _ _ μ _ ι hι hK
  obtain ⟨P, ψ, a, b, x, h1, h2, h3, h4, h5⟩ := h n m hmn Kg μ ι hι hK
  refine ⟨P, ψ, a, b, x, h1, h2, h3, h4, ?_⟩
  have hKk : ∀ k, InK (ι k) := fun k => (hK (ι k)).2 ⟨k, rfl⟩
  have hfun : (fun z : ℂ => tOp μ (⇑ι) (rhoP (⇑ι) m e P) ψ a b (fz m e z) x)
      = fun z : ℂ => (x.det ^ e * a.det ^ e * b.det ^ e) * tOp μ (⇑ι) (rhoP (⇑ι) m 0 P) ψ a b (fz m 0 z) x := by
    funext z
    exact tOp_twist μ ι hKk m e P ψ a b x z
  rw [hfun, deriv_const_mul_field']
  refine mul_ne_zero ?_ h5
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · exact zpow_ne_zero _ (isUnit_det_of_InG h4).ne_zero
  · exact zpow_ne_zero _ (isUnit_det_of_InG h2).ne_zero
  · exact zpow_ne_zero _ (isUnit_det_of_InG h3).ne_zero

end PositivityTheory.Rg.Sw.HSt
