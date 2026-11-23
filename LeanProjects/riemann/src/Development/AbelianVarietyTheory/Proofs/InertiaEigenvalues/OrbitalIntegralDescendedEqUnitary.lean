import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMatMemUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryGroupPositiveCharacterTrivialAndUnimodulaStatement

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.DescOrb

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem mulMat_comm (A : Et F E) {r : ℕ} (τ : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (Ax : Matrix (Fin r) (Fin r) E)
    (hA : ∀ z, j (algebraMap A.K A.L τ * z) = Ax *ᵥ j z) (t : A.L) :
    Ax * A.mulMat j t = A.mulMat j t * Ax := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨z, rfl⟩ := j.surjective v
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Et.mulMat_mulVec_apply, ← hA]
  congr 1; ring

theorem actU_actU {r : ℕ} (g h : unitaryGroup (Fin r) E) (X : Hn r F E) :
    actU g (actU h X) = actU (g * h) X := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · show g.1 * (h.1 * X.1.1 * star h.1) * star g.1 = (g.1 * h.1) * X.1.1 * star (g.1 * h.1)
    rw [star_mul]; simp only [Matrix.mul_assoc]
  · show g.1 *ᵥ (h.1 *ᵥ X.2.1) = (g.1 * h.1) *ᵥ X.2.1
    rw [Matrix.mulVec_mulVec]

end GlobalTheory.JR.DescOrb

namespace GlobalTheory.JR.DescOrb

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_mulMat [hU : Unram F E] (A : Et F E) {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) :
    Continuous fun t : A.L => A.mulMat j t := by
  haveI := hU.lcF
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hj : Continuous (j : A.L → Fin r → E) :=
    IsModuleTopology.continuous_of_linearMap ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  refine continuous_matrix fun i k => ?_
  simp only [Et.mulMat, LinearMap.toMatrix'_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    LinearEquiv.coe_coe]
  exact (continuous_apply i).comp (hj.comp (continuous_id.mul continuous_const))

theorem orbL_descFn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (τ : A.K) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hx : A.IsIsom x j) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ (lam : F) (ν : Measure (unitary A.L)), ν.IsHaarMeasure → ∀ (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → (∀ g, 0 ≤ α g) → ∀ Z : Set (Matrix (Fin r) (Fin r) E), (∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * Ax.1 * star g.1 ∈ Z → ∫ t, α (g * (A.uHom hx t)⁻¹) ∂ν = 1) → ∀ f₀ : Hn r F E → ℂ, Continuous f₀ → (∀ X, f₀ X ≠ 0 → X.1.1 ∈ Z) → ∀ y : A.L, (letI := M.mU; Integrable (fun g => f₀ (actU g (Ax, j y, lam))) M.μU) → A.orbL ν (A.descFn M Ax j lam α f₀) y = orbU M f₀ (Ax, j y, lam) := by
  intro F E _ _ _ _ hU A r M τ x j hx Ax hA lam ν hν α hα hα0 Z hZ f₀ hf₀ hf₀Z y hint
  letI := M.mU
  haveI := M.bU
  haveI := M.haarU
  haveI := hU.ultraE; haveI := hU.lcE; haveI := hU.ultraF; haveI := hU.lcF
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : NormedStarGroup E := ⟨fun y => (hU.norm_star y).le⟩
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) E) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → E))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) E) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → E))
  haveI : LocallyCompactSpace (unitaryGroup (Fin r) E) :=
    (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).locallyCompactSpace
  haveI : SecondCountableTopology (unitaryGroup (Fin r) E) :=
    (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  haveI : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
  haveI : LocallyCompactSpace (unitary A.L) := (isClosed_unitary (R := A.L)).locallyCompactSpace
  haveI : SecondCountableTopology (unitary A.L) :=
    (isClosed_unitary (R := A.L)).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite M.μU := inferInstance
  haveI : M.μU.IsMulRightInvariant := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E r).2 M
  have huc : Continuous (A.uHom hx) := continuous_induced_rng.2 ((continuous_mulMat A j).comp continuous_subtype_val)
  have hinvc : Continuous fun g : unitaryGroup (Fin r) E => g⁻¹ := continuous_inv

  set X : Hn r F E := (Ax, j y, lam) with hXdef
  have hcomm : ∀ t : unitary A.L, ((A.uHom hx t : Matrix (Fin r) (Fin r) E)) * Ax.1 = Ax.1 * A.uHom hx t := fun t =>
    (mulMat_comm A τ j Ax.1 hA t).symm
  have hshift : ∀ t : unitary A.L, ((Ax, j (t.1 * y), lam) : Hn r F E) = actU (A.uHom hx t) X := by
    intro t
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
    · show Ax.1 = (A.uHom hx t : Matrix (Fin r) (Fin r) E) * Ax.1 * star (A.uHom hx t : Matrix (Fin r) (Fin r) E)
      rw [hcomm, Matrix.mul_assoc, Unitary.mul_star_self_of_mem (A.uHom hx t).2, Matrix.mul_one]
    · show j (t.1 * y) = (A.uHom hx t : Matrix (Fin r) (Fin r) E) *ᵥ j y
      rw [Et.uHom_apply, Et.mulMat_mulVec_apply]
  have step1 : ∀ t : unitary A.L, A.descFn M Ax j lam α f₀ (t.1 * y) =
      ∫ g, f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ) ∂M.μU := by
    intro t
    have h := integral_mul_right_eq_self (μ := M.μU)
      (fun g => f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) (A.uHom hx t)
    simp only [mul_inv_cancel_right] at h
    rw [← h]
    show (∫ g, f₀ (actU g ((Ax, j (t.1 * y), lam) : Hn r F E)) * (α g : ℂ) ∂M.μU) = _
    simp only [hshift t, actU_actU]
  have hact : Continuous fun g : unitaryGroup (Fin r) E => actU g X := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ continuous_const)
    · exact (((continuous_subtype_val.matrix_mul continuous_const).matrix_mul
        (continuous_subtype_val.star))).subtype_mk _
    · exact continuous_subtype_val.matrix_mulVec continuous_const
  have hcont : Continuous (Function.uncurry fun (t : unitary A.L) (g : unitaryGroup (Fin r) E) =>
      f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) :=
    (hf₀.comp (hact.comp continuous_snd)).mul (Complex.continuous_ofReal.comp
      (hα.continuous.comp (continuous_snd.mul (hinvc.comp (huc.comp continuous_fst)))))
  have hαint : ∀ g : unitaryGroup (Fin r) E, f₀ (actU g X) ≠ 0 →
      Integrable (fun t => α (g * (A.uHom hx t)⁻¹)) ν := by
    intro g hg
    by_contra hn
    have h1 := integral_undef hn
    rw [hZ g (hf₀Z _ hg)] at h1
    exact one_ne_zero h1
  have hInt : Integrable (Function.uncurry fun (t : unitary A.L) (g : unitaryGroup (Fin r) E) =>
      f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) (ν.prod M.μU) := by
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => ?_, ?_⟩
    · by_cases hg : f₀ (actU g X) = 0
      · simp [Function.uncurry, hg]
      · exact ((hαint g hg).ofReal).const_mul (f₀ (actU g X))
    · refine hint.norm.congr (Eventually.of_forall fun g => ?_)
      simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [integral_const_mul]
      by_cases hg : f₀ (actU g X) = 0
      · simp [hg]
      · rw [integral_congr_ae (Eventually.of_forall fun t => abs_of_nonneg (hα0 _)), hZ g (hf₀Z _ hg), mul_one]
  show ∫ t : unitary A.L, A.descFn M Ax j lam α f₀ (t.1 * y) ∂ν = ∫ g, f₀ (actU g X) ∂M.μU
  simp_rw [step1]
  rw [integral_integral_swap hInt]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  rw [integral_const_mul, integral_complex_ofReal]
  by_cases hg : f₀ (actU g X) = 0
  · simp [hg]
  · rw [hZ g (hf₀Z _ hg)]; simp

end GlobalTheory.JR.DescOrb
