import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EntireEqZeroOrEqZeroOfMulEqZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfSemicharacterMultiplier
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpMove

section
open Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

theorem thetaChar_half {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (n n' : Fin g → ℤ) (z : Fin g → ℂ) :
    thetaChar τ (fun i => (n i : ℂ) / 2) (fun i => (n' i : ℂ) / 2) z = theta (halfVec n) (halfVec n') z τ := by
  refine tsum_congr fun l => ?_
  have e : ((fun i => (l i : ℂ)) + fun i => (n i : ℂ) / 2) = shiftVec (halfVec n) l := by
    funext i; simp [shiftVec, halfVec]
  have e' : (fun i => (n' i : ℂ) / 2) = ofRealVec (halfVec n') := by
    funext i; simp [ofRealVec, halfVec]
  rw [e, e', thetaTerm, eC]
  congr 1
  ring

theorem jAut_transpose_mulVec_period {g : ℕ} {δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hδ : δ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) (w : Fin g ⊕ Fin g → ℤ) :
    (jAut δ τ)ᵀ *ᵥ ((fun i => (w (Sum.inr i) : ℂ)) + spAct δ τ *ᵥ (fun i => (w (Sum.inl i) : ℂ))) =
      (fun i => ((δᵀ *ᵥ w) (Sum.inr i) : ℂ)) + τ *ᵥ (fun i => ((δᵀ *ᵥ w) (Sum.inl i) : ℂ)) := by
  have hj := jAut_isUnit hδ hτ
  have hs := spAct_isSymm hδ hτ.1 hj
  have h1 : (jAut δ τ)ᵀ * spAct δ τ = (nAut δ τ)ᵀ := by
    rw [← hs.eq, ← Matrix.transpose_mul, spAct_eq, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hj,
      Matrix.mul_one]
  have h2 : (fun i => ((δᵀ *ᵥ w) (Sum.inr i) : ℂ)) =
      (cMat δ).toBlocks₁₂ᵀ *ᵥ (fun i => (w (Sum.inl i) : ℂ)) +
        (cMat δ).toBlocks₂₂ᵀ *ᵥ (fun i => (w (Sum.inr i) : ℂ)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, cMat, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Fintype.sum_sum_type]
  have h3 : (fun i => ((δᵀ *ᵥ w) (Sum.inl i) : ℂ)) =
      (cMat δ).toBlocks₁₁ᵀ *ᵥ (fun i => (w (Sum.inl i) : ℂ)) +
        (cMat δ).toBlocks₂₁ᵀ *ᵥ (fun i => (w (Sum.inr i) : ℂ)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, cMat, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Fintype.sum_sum_type]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, h2, h3, jAut_eq, nAut_eq]
  simp only [Matrix.transpose_add, Matrix.transpose_mul, hτ.1.eq, Matrix.add_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_mulVec]
  abel

theorem jAut_transpose_mulVec_mem_iff {g : ℕ} {δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hδ : δ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) (z : Fin g → ℂ) :
    (∃ m n : Fin g → ℤ, (jAut δ τ)ᵀ *ᵥ z = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) ↔
      ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + spAct δ τ *ᵥ (fun i => (n i : ℂ)) := by
  have hj := jAut_isUnit hδ hτ
  constructor
  · rintro ⟨m, n, h⟩
    have hu : IsUnit δᵀ := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
      exact SymplecticGroup.symplectic_det hδ
    obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu (Sum.elim n m)
    have h1 := jAut_transpose_mulVec_period hδ hτ w
    rw [hw] at h1
    refine ⟨fun i => w (Sum.inr i), fun i => w (Sum.inl i), ?_⟩
    have hinj : Function.Injective (jAut δ τ)ᵀ.mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
      exact hj
    apply hinj
    rw [h, h1]
    rfl
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, _, jAut_transpose_mulVec_period hδ hτ (Sum.elim n m)⟩

theorem exists_theta_law {g : ℕ} {δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hδ : δ ∈ Matrix.symplecticGroup (Fin g) ℤ) {n n' k k' : Fin g → ℤ}
    (h : KeyPow.ThetaLaw g δ n n' k k') {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) :
    ∃ r : ℂ, r ^ 8 = (jAut δ τ).det ^ 4 ∧ ∀ z,
      theta (halfVec k) (halfVec k') (zAct δ τ z) (spAct δ τ) =
        r * Complex.exp (Real.pi * Complex.I * expArg δ τ z) * theta (halfVec n) (halfVec n') z τ := by
  obtain ⟨c, hc, h⟩ := h
  have hz : Differentiable ℂ (zAct δ τ) :=
    (Matrix.mulVecLin ((jAut δ τ)⁻¹)ᵀ).toContinuousLinearMap.differentiable
  have hq : Differentiable ℂ fun z => Real.pi * Complex.I * expArg δ τ z := by
    simp only [expArg, dotProduct, mulVec]
    fun_prop
  obtain ⟨r, hr, H⟩ := entire_eq_mul_of_sq_eq_mul_sq g
    (fun z => theta (halfVec k) (halfVec k') (zAct δ τ z) (spAct δ τ))
    (fun z => theta (halfVec n) (halfVec n') z τ) _ (c * (jAut δ τ).det)
    ((differentiable_theta (spAct_mem hδ hτ) _ _).comp hz) (differentiable_theta hτ _ _) hq
    (fun z => by
      rw [h τ hτ z, eC]
      congr 3
      ring)
  refine ⟨r, ?_, H⟩
  calc r ^ 8 = (r ^ 2) ^ 4 := by ring
    _ = _ := by rw [hr, mul_pow, hc, _root_.one_mul]

end

theorem normalAt_spAct : ∀ (x : KeyIn ℂ) (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c : ℂ) (sp : Matrix (Fin x.P.g ⊕ Fin x.P.g) (Fin x.P.g ⊕ Fin x.P.g) ℤ) (n n' k k' : Fin x.P.g → ℤ), sp ∈ Matrix.symplecticGroup (Fin x.P.g) ℤ → GlobalTheory.KeyPow.ThetaLaw x.P.g sp n n' k k' → c ≠ 0 → GlobalTheory.KeyPow.NormalAt x τ M (fun i => (n i : ℂ) / 2) (fun i => (n' i : ℂ) / 2) c → ∃ (M' : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (c' : ℂ), c' ≠ 0 ∧ M'.det ^ 4 / c' ^ 8 = M.det ^ 4 / c ^ 8 ∧ GlobalTheory.KeyPow.NormalAt x (Key.Chi.spAct sp τ) M' (fun i => (k i : ℂ) / 2) (fun i => (k' i : ℂ) / 2) c' := by
  intro x τ M c sp n n' k k' hsp hlaw hc hN
  have hτ := hN.mem_siegelH
  obtain ⟨u, -, -, hΛ, hrig, hfn, hv⟩ := hN
  have hj := Key.Chi.jAut_isUnit hsp hτ
  have hτ' := Key.Chi.spAct_mem hsp hτ
  obtain ⟨r, hr, H⟩ := exists_theta_law hsp hlaw hτ
  set j := Key.Chi.jAut sp τ with hjdef
  have hj0 : j.det ≠ 0 := hj.ne_zero
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact pow_ne_zero 4 hj0 (by rw [← hr]; simp)
  have e1 : j.transpose * (j⁻¹).transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hj, Matrix.transpose_one]
  have e2 : (j⁻¹).transpose * j.transpose = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hj, Matrix.transpose_one]
  let φ : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := Matrix.toLin'OfInv e2 e1
  have hφ : ∀ z, φ z = j.transpose.mulVec z := fun _ => rfl
  have hE : Differentiable ℂ fun z => Complex.exp (Real.pi * Complex.I * Key.Chi.expArg sp τ (φ z)) := by
    simp only [hφ, Key.Chi.expArg, dotProduct, Matrix.mulVec]
    fun_prop
  obtain ⟨u', -, hΛ', hrig', hfn', hv'⟩ := exists_holUnif_reparam x.P.A x.P.L x.P.g u φ _ hE
    (fun _ => Complex.exp_ne_zero _) (by simp [Key.Chi.expArg])
  refine ⟨M * j⁻¹, c / r, div_ne_zero hc hr0, ?_, u', hτ'.1, hτ'.2, fun z => ?_, hrig' _ hrig, ?_,
    fun i => hv' _ _ ?_⟩
  · rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', div_pow, hr]
    field_simp
  · rw [hΛ', hΛ, hφ]
    exact jAut_transpose_mulVec_mem_iff hsp hτ z
  · convert hfn' _ _ hfn using 2 with z
    have h1 := H (φ z)
    have h2 : Key.Chi.zAct sp τ (φ z) = z := by
      rw [Key.Chi.zAct, hφ, Matrix.mulVec_mulVec, e2, Matrix.one_mulVec]
    rw [h2] at h1
    rw [thetaChar_half, thetaChar_half, h1]
    field_simp
  · have h3 : φ ((M * j⁻¹) i) = M i := by
      rw [hφ, Matrix.mulVec_transpose]
      change ((M * j⁻¹) * j) i = M i
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hj, Matrix.mul_one]
    rw [map_smul, h3]
    exact hv i

end GlobalTheory.SpMove
