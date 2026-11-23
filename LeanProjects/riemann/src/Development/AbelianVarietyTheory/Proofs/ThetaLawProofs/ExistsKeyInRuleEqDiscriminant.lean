import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalAtScale
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsEllipticKeyDataValueEqDiscriminant
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyPBId
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHomogeneousData

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KeyTest

open GlobalTheory.KeyPow

theorem exists_normalAt (x : KeyIn ℂ) :
    ∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
      charHalf x.P.g a b ∧ c ≠ 0 ∧ M.det ≠ 0 ∧ NormalAt x τ M a b c :=
  (GlobalTheory.KeyNormalExists.exists_normalAt GlobalTheory.thetaUnifAV_all x).1

theorem value_of_normalAt (κ : KeyIn ℂ → ℂˣ)
    (hH : ∀ (P : Out.PolAV (Sp ℂ)) (hg rig hr th hth v hv th' hth' v' hv') (a : ℂ)
      (M : Matrix (Fin P.g) (Fin P.g) ℂ), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (M i) v (v' i)) →
      a ^ 8 * (κ ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : ℂ) = M.det ^ 4 * κ ⟨P, hg, rig, hr, th, hth, v, hv⟩)
    (hN : ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ)
      (a b : Fin x.P.g → ℂ), (τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ i, a i = 0 ∨ a i = 1 / 2) ∧
        (∀ i, b i = 0 ∨ b i = 1 / 2) ∧
        (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
        u.IsRig x.rig ∧ u.IsFn x.th (thetaChar τ a b) ∧
        (∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i))) → κ x = 1)
    (x : KeyIn ℂ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ)
    (hab : charHalf x.P.g a b) (hc : c ≠ 0) (hM : M.det ≠ 0) (hx : NormalAt x τ M a b c) :
    (κ x : ℂ) = M.det ^ 4 / c ^ 8 := by
  have hdet : M⁻¹.det = M.det⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  obtain ⟨th', hth', v', hv', h₁, h₂⟩ :=
    GlobalTheory.KeyHomogInhab.exists_homogeneous_data ℂ x c⁻¹ M⁻¹ (inv_ne_zero hc) (by rw [hdet]; exact inv_ne_zero hM)
  obtain ⟨P, hg, rig, hr, th, hth, v, hv⟩ := x
  have h₃ := (GlobalTheory.KeyEq.normalAt_scale P hg rig hr th hth v hv th' hth' v' hv' c⁻¹ M⁻¹ h₁ h₂).2.2 τ M a b c hx
  rw [Matrix.nonsing_inv_mul M (Ne.isUnit hM), inv_mul_cancel₀ hc] at h₃
  obtain ⟨u, k₁, k₂, k₃, k₄, k₅, k₆⟩ :=
    (normalAt_one_iff ⟨P, hg, rig, hr, th', hth', v', hv'⟩ τ a b).1 h₃
  have h₄ := hN ⟨P, hg, rig, hr, th', hth', v', hv'⟩ u τ a b ⟨k₁, k₂, hab.1, hab.2, k₃, k₄, k₅, k₆⟩
  have h₅ := hH P hg rig hr th hth v hv th' hth' v' hv' c⁻¹ M⁻¹ h₁ h₂
  rw [h₄, hdet, Units.val_one] at h₅
  generalize (κ ⟨P, hg, rig, hr, th, hth, v, hv⟩ : ℂ) = k at h₅ ⊢
  generalize M.det = d at h₅ hM ⊢
  field_simp at h₅ ⊢
  linear_combination -h₅

theorem exists_keyIn_rule_eq_discriminant :
    ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic], ∃ x : KeyIn ℂ, x.P.g = 1 ∧ ∀ κ : KeyIn ℂ → ℂˣ, (∀ (P : Out.PolAV (Sp ℂ)) (hg rig hr th hth v hv th' hth' v' hv') (a : ℂ) (M : Matrix (Fin P.g) (Fin P.g) ℂ), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → a ^ 8 * (κ ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : ℂ) = M.det ^ 4 * κ ⟨P, hg, rig, hr, th, hth, v, hv⟩) → (∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ), (τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧ (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ u.IsRig x.rig ∧ u.IsFn x.th (thetaChar τ a b) ∧ (∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i))) → κ x = 1) → (κ x : ℂ) = W.Δ := by
  intro W _
  obtain ⟨x, hg, hx⟩ := GlobalTheory.EllipticKey.exists_keyIn_value_eq_discriminant GlobalTheory.thetaUnifAV_all ℂ W
  refine ⟨x, hg, fun κ hH hN => ?_⟩
  obtain ⟨τ, M, a, b, c, hab, hc, hM, hn⟩ := exists_normalAt x
  rw [value_of_normalAt κ hH hN x τ M a b c hab hc hM hn]
  exact hx (RingHom.id ℂ) x τ M a b c (GlobalTheory.keyPB_id ℂ x) hab hc hn

end GlobalTheory.KeyTest
