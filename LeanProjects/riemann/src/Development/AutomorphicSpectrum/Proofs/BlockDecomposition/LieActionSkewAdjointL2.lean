import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary PositivityTheory.S2.Clozel Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.PeterssonSkew

theorem integral_deriv_eq_zero {Q : Type*} [MeasurableSpace Q] (ν : Measure Q) [IsFiniteMeasure ν]
    (u v u' v' : ℝ → Q → ℂ) (C : ℝ)
    (hu : ∀ t q, HasDerivAt (fun s => u s q) (u' t q) t) (hv : ∀ t q, HasDerivAt (fun s => v s q) (v' t q) t)
    (bu : ∀ t q, ‖u t q‖ ≤ C) (bv : ∀ t q, ‖v t q‖ ≤ C) (bu' : ∀ t q, ‖u' t q‖ ≤ C) (bv' : ∀ t q, ‖v' t q‖ ≤ C)
    (mu : ∀ t, AEStronglyMeasurable (u t) ν) (mv : ∀ t, AEStronglyMeasurable (v t) ν)
    (mu' : AEStronglyMeasurable (u' 0) ν) (mv' : AEStronglyMeasurable (v' 0) ν)
    (hc : ∀ t, ∫ q, u t q * conj (v t q) ∂ν = ∫ q, u 0 q * conj (v 0 q) ∂ν) :
    ∫ q, (u' 0 q * conj (v 0 q) + u 0 q * conj (v' 0 q)) ∂ν = 0 := by
  have mc : ∀ {f : Q → ℂ}, AEStronglyMeasurable f ν → AEStronglyMeasurable (fun q => conj (f q)) ν :=
    fun h => Complex.continuous_conj.comp_aestronglyMeasurable h
  have hC : 0 ≤ C ∨ IsEmpty Q := by
    by_cases h : Nonempty Q
    · obtain ⟨q⟩ := h
      exact Or.inl ((norm_nonneg _).trans (bu 0 q))
    · exact Or.inr (not_nonempty_iff.1 h)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun t q => u t q * conj (v t q))
    (F' := fun t q => u' t q * conj (v t q) + u t q * conj (v' t q))
    (bound := fun _ => C * C + C * C) Filter.univ_mem
    (Eventually.of_forall fun t => (mu t).mul (mc (mv t)))
    (Integrable.of_bound ((mu 0).mul (mc (mv 0))) (C * C) (Eventually.of_forall fun q => by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (bu 0 q) (bv 0 q) (norm_nonneg _) ((norm_nonneg _).trans (bu 0 q))))
    ((mu'.mul (mc (mv 0))).add ((mu 0).mul (mc mv')))
    (Eventually.of_forall fun q t _ => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul, RCLike.norm_conj]
      · exact mul_le_mul (bu' t q) (bv t q) (norm_nonneg _) ((norm_nonneg _).trans (bu' t q))
      · exact mul_le_mul (bu t q) (bv' t q) (norm_nonneg _) ((norm_nonneg _).trans (bu t q)))
    (integrable_const _)
    (Eventually.of_forall fun q t _ => (hu t q).mul (hv t q).star)
  have h0 : HasDerivAt (fun t : ℝ => ∫ q, u t q * conj (v t q) ∂ν) 0 0 := by
    simp only [hc]
    exact hasDerivAt_const _ _
  exact key.2.unique h0

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

open scoped Matrix.Norms.Operator in

theorem exists_curve (X : Lie E a) : ∃ c : ℝ → Matrix.GeneralLinearGroup (Fin a) (Cinf E), c 0 = 1 ∧
    (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => toL (c t).val) X 0 := by
  set Y : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of X with hY
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  have hadd : ∀ s t : ℝ, NormedSpace.exp ((s + t) • Y) = NormedSpace.exp (s • Y) * NormedSpace.exp (t • Y) := fun s t => by
    rw [add_smul]
    exact NormedSpace.exp_add_of_commute (((Commute.refl Y).smul_left s).smul_right t)
  have hone : ∀ t : ℝ, NormedSpace.exp (t • Y) * NormedSpace.exp ((-t) • Y) = 1 := fun t => by
    rw [← hadd, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  refine ⟨fun t => ⟨NormedSpace.exp (t • Y), NormedSpace.exp ((-t) • Y), hone t, by simpa using hone (-t)⟩,
    Units.ext (by simp [NormedSpace.exp_zero]), fun s t => Units.ext (hadd s t), ?_⟩
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_translate {X : Lie E a} {c : ℝ → Matrix.GeneralLinearGroup (Fin a) (Cinf E)} (h0 : c 0 = 1)
    (hadd : ∀ s t, c (s + t) = c s * c t) (hX : HasDerivAt (fun t => toL (c t).val) X 0) (φ : Sm E a) (g : GA E a)
    (t : ℝ) : HasDerivAt (fun s => φ.1 (g * infGL E a (c s))) (lieD X φ.1 (g * infGL E a (c t))) t := by
  have h := hasDerivAt_curve φ (g * infGL E a (c t)) c X h0 hX
  have h2 : HasDerivAt (fun s => φ.1 (g * infGL E a (c t) * infGL E a (c (s - t))))
      (lieD X φ.1 (g * infGL E a (c t))) t := HasDerivAt.comp_sub_const t t (by simpa using h)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [mul_assoc, ← map_mul, ← hadd]
  simp

theorem pet_mul_right (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {φ ψ : GA E a → ℂ}
    (hφ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ) (hψ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ ψ) (g : GA E a) :
    pet (GlobalTheory.UnitaryBC.latticeGL E a) μ (fun x => φ (x * g)) (fun x => ψ (x * g)) =
      pet (GlobalTheory.UnitaryBC.latticeGL E a) μ φ ψ := by
  rw [← MemL2Quotient.inner_toL2_eq_theta_pairing (hφ.mul_right g) (hψ.mul_right g), ← right_translate_toL2, ← right_translate_toL2, ← MemL2Quotient.inner_toL2_eq_theta_pairing hφ hψ]
  exact LinearIsometry.inner_map_map
    { toLinearMap := (R (GlobalTheory.UnitaryBC.latticeGL E a) μ g :
        L2 (GlobalTheory.UnitaryBC.latticeGL E a) μ →L[ℂ] L2 (GlobalTheory.UnitaryBC.latticeGL E a) μ).toLinearMap
      norm_map' := norm_R g } _ _

theorem pet_lie_add (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : Lie E a) (φ ψ : Sm E a)
    (hφ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1) (hψ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ ψ.1)
    (hφ' : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X φ).1)
    (hψ' : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X ψ).1)
    (C : ℝ) (bφ : ∀ g, ‖φ.1 g‖ ≤ C) (bψ : ∀ g, ‖ψ.1 g‖ ≤ C)
    (bφ' : ∀ g, ‖(lie E a X φ).1 g‖ ≤ C) (bψ' : ∀ g, ‖(lie E a X ψ).1 g‖ ≤ C) :
    pet (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X φ).1 ψ.1 +
      pet (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 (lie E a X ψ).1 = 0 := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  obtain ⟨c, h0, hadd, hX⟩ := exists_curve X
  have e0 : infGL E a (c 0) = 1 := by rw [h0, map_one]
  have key := integral_deriv_eq_zero (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GlobalTheory.UnitaryBC.latticeGL E a) μ)
    (fun t q => φ.1 (q.out * infGL E a (c t))) (fun t q => ψ.1 (q.out * infGL E a (c t)))
    (fun t q => lieD X φ.1 (q.out * infGL E a (c t))) (fun t q => lieD X ψ.1 (q.out * infGL E a (c t))) C
    (fun t q => hasDerivAt_translate h0 hadd hX φ q.out t) (fun t q => hasDerivAt_translate h0 hadd hX ψ q.out t)
    (fun _ _ => bφ _) (fun _ _ => bψ _) (fun _ _ => bφ' _) (fun _ _ => bψ' _)
    (fun t => (hφ.mul_right (infGL E a (c t))).2.1) (fun t => (hψ.mul_right (infGL E a (c t))).2.1)
    (by simp only [e0, mul_one]; exact hφ'.2.1) (by simp only [e0, mul_one]; exact hψ'.2.1)
    (fun t => by
      have h1 := pet_mul_right μ hφ hψ (infGL E a (c t))
      simp only [e0, mul_one]
      exact h1)
  simp only [e0, mul_one] at key
  exact (integral_add (hφ'.integrable_mul_conj hψ) (hφ.integrable_mul_conj hψ')).symm.trans key

theorem lie_skew_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a) (hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1), (∀ φ ∈ π.V, ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) → ∀ (X : Lie E a) (φ ψ : π.V), inner ℂ (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm ψ) (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm (π.op (.lie X) φ)) = -inner ℂ (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm (π.op (.lie X) ψ)) (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm φ) := by
  intro E _ _ _ a μ _ _ π hm hb X φ ψ
  have hL : ∀ f : π.V, ∃ C : ℝ, ∀ g, ‖f.1.1 g‖ ≤ C := fun f => hb f.1 f.2
  obtain ⟨C₁, b₁⟩ := hL φ
  obtain ⟨C₂, b₂⟩ := hL ψ
  obtain ⟨C₃, b₃⟩ := hL (π.op (.lie X) φ)
  obtain ⟨C₄, b₄⟩ := hL (π.op (.lie X) ψ)
  have h := pet_lie_add μ X φ.1 ψ.1 (hm _ φ.2) (hm _ ψ.2) (hm _ (π.op (.lie X) φ).2) (hm _ (π.op (.lie X) ψ).2)
    (max (max C₁ C₂) (max C₃ C₄))
    (fun g => (b₁ g).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (fun g => (b₂ g).trans ((le_max_right _ _).trans (le_max_left _ _)))
    (fun g => (b₃ g).trans ((le_max_left _ _).trans (le_max_right _ _)))
    (fun g => (b₄ g).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have e1 := MemL2Quotient.inner_toL2_eq_theta_pairing (hm _ (π.op (.lie X) φ).2) (hm _ ψ.2)
  have e2 := MemL2Quotient.inner_toL2_eq_theta_pairing (hm _ φ.2) (hm _ (π.op (.lie X) ψ).2)
  change inner ℂ (hm _ ψ.2).toL2 (hm _ (π.op (.lie X) φ).2).toL2 =
    -inner ℂ (hm _ (π.op (.lie X) ψ).2).toL2 (hm _ φ.2).toL2
  rw [e1, e2]
  exact eq_neg_of_add_eq_zero_left h

end GlobalTheory.CompanionTheory.PeterssonSkew
