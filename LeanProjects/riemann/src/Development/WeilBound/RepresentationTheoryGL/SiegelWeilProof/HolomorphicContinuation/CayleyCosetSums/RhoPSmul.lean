import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.MultiplicityOneTestOperators

noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.LoweringDerivative

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem rhoP_add {Kg : Type} (ι : Kg → M2 n) (m : ℕ) (e : ℤ) (X Y : Matrix (Fin n) (Fin n) ℂ) (k : Kg) :
    rhoP ι m e (X + Y) k = rhoP ι m e X k + rhoP ι m e Y k := by
  simp only [rhoP, Matrix.mul_add, Matrix.add_mul, trace_add, mul_add, star_add]

theorem rhoP_smul {Kg : Type} (ι : Kg → M2 n) (m : ℕ) (e : ℤ) (c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (k : Kg) :
    rhoP ι m e (c • X) k = star c * rhoP ι m e X k := by
  simp only [rhoP, Matrix.mul_smul, Matrix.smul_mul, trace_smul, smul_eq_mul, star_mul']; ring

section Main

variable {Kg : Type} [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg] [MeasurableSpace Kg]
  [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n) (hι : Continuous ι)
  (hK : ∀ g, InK g ↔ ∃ k, ι k = g) (m : ℕ) (e : ℤ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : Continuous ψ)
  (hψc : HasCompactSupport ψ) {a b : M2 n} (ha : InG a) (hb : InG b)

def abelian₂ (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  tOp μ ι (rhoP ι m e X) ψ a b (fz m e z) 1

theorem Lam_eq (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z X = ∫ k, rhoP ι m e X k * Hf m e ψ a b z (ι k) ∂μ := by
  simp only [abelian₂, tOp, Hf, one_mul]

include hι hK hψ hψc ha hb in
theorem continuous_integrand (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun k => rhoP ι m e X k * Hf m e ψ a b z (ι k) := by
  have hG : ∀ k, InG (ι k) := fun k => LoweringDerivative.inG_of_inK ((hK (ι k)).2 ⟨k, rfl⟩)
  have h1 : Continuous (rhoP (⇑ι) m e X) := LoweringDerivative.continuous_rhoP (⇑ι) hι hG m e X
  have h2 := continuous_Hf m e hψ hψc ha hb
  have h3 : Continuous fun k : Kg => ((⟨ι k, hG k⟩ : Gs n), z) :=
    (Continuous.subtype_mk hι (fun k => hG k)).prodMk continuous_const
  have h4 : Continuous fun k : Kg => Hf m e ψ a b z (ι k) := by
    have h5 := h2.comp h3
    simp only [Function.comp_def] at h5
    exact h5
  exact h1.mul h4

include hι hK hψ hψc ha hb in
theorem integrable_integrand (z : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Integrable (fun k => rhoP ι m e X k * Hf m e ψ a b z (ι k)) μ := by
  exact (continuous_integrand ι hι hK m e hψ hψc ha hb z X).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

include hι hK hψ hψc ha hb in
theorem Lam_add (z : ℂ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z (X + Y) = abelian₂ μ ι m e ψ a b z X + abelian₂ μ ι m e ψ a b z Y := by
  simp only [Lam_eq, rhoP_add, add_mul]
  exact integral_add (integrable_integrand μ ι hι hK m e hψ hψc ha hb z X)
    (integrable_integrand μ ι hι hK m e hψ hψc ha hb z Y)

theorem Lam_smul (z c : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    abelian₂ μ ι m e ψ a b z (c • X) = star c * abelian₂ μ ι m e ψ a b z X := by
  simp only [Lam_eq, rhoP_smul, mul_assoc, integral_const_mul]

private theorem inK_fromBlocks_unitary_diag (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) :
    InK (Matrix.fromBlocks U 0 0 U : M2 n) := by
  refine ⟨?_, ?_⟩
  · simp [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU]
  · simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hU]

private theorem u1_fromBlocks_diag_mul (U : Matrix (Fin n) (Fin n) ℂ) (y : M2 n) :
    u1 (Matrix.fromBlocks U 0 0 U * y) = U * u1 y := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks y]
  simp [u1, Matrix.fromBlocks_multiply, Matrix.mul_add, Matrix.mul_smul]

private theorem u2_fromBlocks_diag_mul (U : Matrix (Fin n) (Fin n) ℂ) (y : M2 n) :
    u2 (Matrix.fromBlocks U 0 0 U * y) = U * u2 y := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks y]
  simp [u2, Matrix.fromBlocks_multiply, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_neg]

include hK ha hb in
theorem Lam_inv (z : ℂ) {U X : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) (hX : Xᴴ * X = 1) :
    abelian₂ μ ι m e ψ a b z (U * X * Uᴴ) = abelian₂ μ ι m e ψ a b z X := by
  obtain ⟨k0, hk0⟩ := (hK _).1 (inK_fromBlocks_unitary_diag U hU)
  have hG : ∀ k, InG (ι k) := fun k => LoweringDerivative.inG_of_inK ((hK (ι k)).2 ⟨k, rfl⟩)
  have hpG : InG (Matrix.fromBlocks U 0 0 U : M2 n) := LoweringDerivative.inG_of_inK (inK_fromBlocks_unitary_diag U hU)
  have hp21 : Matrix.toBlocks₂₁ (Matrix.fromBlocks U 0 0 U : M2 n) = 0 :=
    Matrix.toBlocks_fromBlocks₂₁ _ _ _ _
  have hUi : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hU
  have hd : star U.det * U.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, hU, Matrix.det_one]
  have hn : Complex.normSq U.det = 1 := by
    have h : (Complex.normSq U.det : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact hd
    exact_mod_cast h
  have hl : ∀ w : ℂ, lam m e w (Matrix.fromBlocks U 0 0 U : M2 n) =
      (U.det * U.det) ^ e * U.det ^ (-(m : ℤ)) := by
    intro w
    simp only [lam, Matrix.toBlocks_fromBlocks₂₂, Matrix.det_fromBlocks_zero₂₁, hn, Complex.ofReal_one,
      Complex.one_cpow, mul_one]
  have h1 : star ((U.det * U.det) ^ e) * (U.det * U.det) ^ e = 1 := by
    rw [star_zpow₀, ← mul_zpow, star_mul',
      show star U.det * star U.det * (U.det * U.det) = (star U.det * U.det) * (star U.det * U.det) by ring,
      hd, one_mul, _root_.one_zpow]
  have h2 : star (U.det ^ (-(m : ℤ))) * U.det ^ (-(m : ℤ)) = 1 := by
    rw [star_zpow₀, ← mul_zpow, hd, _root_.one_zpow]
  have hlam : star (lam m e 0 (Matrix.fromBlocks U 0 0 U : M2 n)) *
      lam m e z (Matrix.fromBlocks U 0 0 U : M2 n) = 1 := by
    rw [hl, hl]
    calc star ((U.det * U.det) ^ e * U.det ^ (-(m : ℤ))) * ((U.det * U.det) ^ e * U.det ^ (-(m : ℤ)))
        = (star ((U.det * U.det) ^ e) * (U.det * U.det) ^ e) *
          (star (U.det ^ (-(m : ℤ))) * U.det ^ (-(m : ℤ))) := by
          rw [star_mul']
          ring
      _ = 1 := by rw [h1, h2, one_mul]
  have aux : ∀ A B C : ℂ, star (lam m e 0 (Matrix.fromBlocks U 0 0 U : M2 n)) * A * B *
      (lam m e z (Matrix.fromBlocks U 0 0 U : M2 n) * C) = A * B * C := by
    intro A B C
    linear_combination (A * B * C) * hlam
  have key : ∀ k, rhoP ι m e (U * X * Uᴴ) (k0 * k) * Hf m e ψ a b z (ι (k0 * k)) =
      rhoP ι m e X k * Hf m e ψ a b z (ι k) := by
    intro k
    have hm : (u2 (ι k))⁻¹ * Uᴴ * (U * X * Uᴴ) * (U * u1 (ι k)) = (u2 (ι k))⁻¹ * X * u1 (ι k) := by
      calc (u2 (ι k))⁻¹ * Uᴴ * (U * X * Uᴴ) * (U * u1 (ι k))
          = (u2 (ι k))⁻¹ * (Uᴴ * U) * X * (Uᴴ * U) * u1 (ι k) := by
            simp only [Matrix.mul_assoc]
        _ = (u2 (ι k))⁻¹ * X * u1 (ι k) := by
            rw [hU]
            simp only [Matrix.mul_one]
    simp only [rhoP]
    rw [map_mul, hk0, Hf_up m e ψ ha hb hpG hp21 (hG k) z, fz_up hpG hp21 (hG k) m e 0,
      u1_fromBlocks_diag_mul, u2_fromBlocks_diag_mul, Matrix.mul_inv_rev, hUi, hm]
    simp only [star_mul']
    exact aux _ _ _
  have hinv := integral_mul_left_eq_self (μ := μ)
    (fun k => rhoP ι m e (U * X * Uᴴ) k * Hf m e ψ a b z (ι k)) k0
  simp only [key] at hinv
  rw [Lam_eq, Lam_eq]
  exact hinv.symm

end Main

end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
