import Mathlib
import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspCentral
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsMeasure
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableConv
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableLaplacian

noncomputable section

namespace GroundTheory.Automorphic

namespace UnitaryAdmissible

open MeasureTheory Filter Topology NumberField AutomorphicForm CuspidalSpectrum Reduction RightCosetSpace
open scoped NumberField.AdeleRing

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => Reduction.rationalGLOne K n

theorem aeval_laplacian_sliceL_eq_zero {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (isExpLieAlgebra K n).lieSubalgebra) (P : Polynomial ℂ) {φ : cuspForms K n}
    (hφ : Polynomial.aeval (uActionCusp K n (laplacianU K n b)) P φ = 0) (g : AdelicGLn.AdelicGL K n) :
    Polynomial.aeval ((isExpLieAlgebra K n).laplacian (F := ℂ) b) P
      (sliceL g ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩) = 0 := by
  set incl : cuspForms K n →ₗ[ℂ] archSmooth K n :=
    Submodule.inclusion (cuspForms_le_automorphicForms.trans automorphicForms_le_archSmooth)
  have h1 := map_aeval_apply_of_intertwine incl (A := uActionCusp K n (laplacianU K n b))
    (B := uAction (laplacianU K n b)) (fun m => rfl) P φ
  rw [hφ, map_zero] at h1
  have h2 := map_aeval_apply_of_intertwine (sliceL g) (A := uAction (laplacianU K n b))
    (B := (isExpLieAlgebra K n).laplacian (F := ℂ) b)
    (fun m => by rw [sliceL_uAction, rightUAction_laplacianU]) P (incl φ)
  rw [← h1, map_zero] at h2
  exact h2.symm

theorem finiteDimensional_of_map_mem {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N]
    [Module ℂ N] {S : Submodule ℂ M} {E : Submodule ℂ N} [FiniteDimensional ℂ E] (f : M →ₗ[ℂ] N)
    (hf : ∀ x ∈ S, f x ∈ E) (hinj : ∀ x ∈ S, f x = 0 → x = 0) : FiniteDimensional ℂ S := by
  let g : S →ₗ[ℂ] E := (f.domRestrict S).codRestrict E fun x => hf x x.2
  have hg : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun x hx => Subtype.ext (hinj x x.2 ?_)
    exact congrArg Subtype.val hx
  exact Module.Finite.of_injective g hg

theorem cuspRep_integrated_eq_smul (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (F : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (c : ℂ) (φ : cuspForms K n)
    (hΘ : ∀ y : normOneGL K n,
      ∫ x, F x * (φ : AdelicGLn.AdelicGL K n → ℂ) ((y : AdelicGLn.AdelicGL K n) * x) ∂μ =
        c * (φ : AdelicGLn.AdelicGL K n → ℂ) y) :
    (cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ F) (cuspToL2 μ φ) = c • cuspToL2 μ φ := by
  have hrc : rconv Γ₁ μ F ((cuspToL2 μ φ : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ)) =
      fun y : normOneGL K n => c * (φ : AdelicGLn.AdelicGL K n → ℂ) (y : AdelicGLn.AdelicGL K n) := by
    funext y
    have hae : (fun z : normOneGL K n =>
        ((cuspToL2 μ φ : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (mk Γ₁ z)) =ᵐ[μ]
          fun z => cuspQuot φ.2.1.isLeftInvariant (mk Γ₁ z) :=
      (quasiMeasurePreserving_mk Γ₁ μ).ae_eq (coeFn_cuspToL2 μ φ)
    unfold rconv
    have h2 : ∫ z, F (y⁻¹ * z) *
        ((cuspToL2 μ φ : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ)) (mk Γ₁ z) ∂μ =
          ∫ z, F (y⁻¹ * z) * (φ : AdelicGLn.AdelicGL K n → ℂ) z ∂μ := by
      refine integral_congr_ae (hae.mono fun z hz => ?_)
      simp only at hz ⊢
      rw [hz, cuspQuot_mk]
    rw [h2, ← integral_mul_left_eq_self (fun z => F (y⁻¹ * z) * (φ : AdelicGLn.AdelicGL K n → ℂ) z) y]
    simp only [Subgroup.coe_mul, inv_mul_cancel_left]
    exact hΘ y
  have hR : (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ F)
      ((cuspToL2 μ φ : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ)) =
        c • ((cuspToL2 μ φ : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ)) := by
    have hc := isContRep_rconv (μ := μ) F ((cuspToL2 μ φ : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ))
    have h1 := hc.ae_eq_quotFun
    have hq' : ∀ q : RightCosetSpace Γ₁, quotFun (rconv Γ₁ μ F ((cuspToL2 μ φ : cuspidalL2 μ) :
        Lp ℂ 2 (quotientMeasure Γ₁ μ))) hc.2.1 q = c * cuspQuot φ.2.1.isLeftInvariant q :=
      (mk_surjective Γ₁).forall.2 fun y => by rw [quotFun_mk, cuspQuot_mk, hrc]
    have h2 : (fun q => c * cuspQuot φ.2.1.isLeftInvariant q) =ᵐ[quotientMeasure Γ₁ μ]
        ⇑(c • ((cuspToL2 μ φ : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ))) := by
      filter_upwards [coeFn_cuspToL2 μ φ,
        Lp.coeFn_smul c ((cuspToL2 μ φ : cuspidalL2 μ) : Lp ℂ 2 (quotientMeasure Γ₁ μ))] with q hq hs
      rw [hs, Pi.smul_apply, hq, smul_eq_mul]
    exact Lp.ext (h1.trans ((EventuallyEq.of_eq (funext hq')).trans h2))
  apply Subtype.ext
  have h := congrArg (fun L => L (cuspToL2 μ φ)) (subtypeL_comp_integrated μ (UnitaryRep.ccToL1 μ F))
  exact h.trans (hR.trans (Submodule.coe_smul c (cuspToL2 μ φ)).symm)

theorem finiteDimensional_of_eigen {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (isExpLieAlgebra K n).lieSubalgebra) (P : Polynomial ℂ) (hP : P.Monic)
    (hPd : 0 < P.natDegree) (c : ℂ) (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))) (S : Submodule ℂ (cuspForms K n))
    (hS : ∀ φ ∈ S, Polynomial.aeval (uActionCusp K n (laplacianU K n b)) P φ = 0 ∧
      lieActionCusp K n (centralZ K n) φ = c • φ ∧
      ∀ u ∈ U, finRepCusp K n (u : AdelicGLn.FiniteAdelicGL K n) φ = φ) :
    FiniteDimensional ℂ S := by
  set μ : Measure (normOneGL K n) := Measure.haar with hμ
  set ν : Measure (archGroup K n) := Measure.haar with hν

  obtain ⟨κ, hκs, hκc, -, hκ⟩ := (isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian ν b P
    hP hPd (Filter.univ_mem)
  have hκcont : Continuous κ := by
    let _ := (isExpLieAlgebra K n).chartedSpace
    exact hκs.continuous
  have hconv : ∀ φ ∈ S, ∀ g : AdelicGLn.AdelicGL K n, (φ : AdelicGLn.AdelicGL K n → ℂ) g =
      ∫ a, (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n a) * κ a ∂ν := by
    intro φ hφ g
    have h := hκ (sliceL g ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩)
      (aeval_laplacian_sliceL_eq_zero b P (hS φ hφ).1 g) 1
    have e1 : ∀ x, ((sliceL g ⟨(φ : AdelicGLn.AdelicGL K n → ℂ), φ.2.1.isSmooth.1⟩ :
        (isExpLieAlgebra K n).smoothFuns (F := ℂ)) : archGroup K n → ℂ) x =
          (φ : AdelicGLn.AdelicGL K n → ℂ) (g * infEmb K n x) := fun x => rfl
    simp only [e1, one_mul, map_one, mul_one] at h
    exact h

  have hcent : ∀ φ ∈ S, ∀ (y : AdelicGLn.AdelicGL K n) (a : archGroup K n),
      (φ : AdelicGLn.AdelicGL K n → ℂ) (y * infEmb K n a) =
        Complex.exp (c * Real.log (detA K n a)) *
          (φ : AdelicGLn.AdelicGL K n → ℂ) (y * (archP K n a : AdelicGLn.AdelicGL K n)) := by
    intro φ hφ y a
    have e : infEmb K n a = (archP K n a : AdelicGLn.AdelicGL K n) * centralSection K n (detA K n a) := by
      rw [← retract_infEmb, coe_retractOne]
      exact (inv_mul_cancel_right _ _).symm
    rw [e, ← mul_assoc, apply_mul_centralSection (hS φ hφ).2.1]

  set κc : archGroup K n → ℂ := fun a => κ a * Complex.exp (c * Real.log (detA K n a)) with hκcdef
  have hκccont : Continuous κc := by
    refine hκcont.mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp ?_)))
    exact (continuous_subtype_val.comp continuous_detA).log fun a => (detA K n a).2.ne'
  have hκcc : HasCompactSupport κc := hκc.mul_right
  obtain ⟨F₀, c', hc', -, hint⟩ := exists_cc_integral_mul_eq μ ν U hU κc hκccont hκcc

  have hΘ : ∀ φ ∈ S, ∀ y : normOneGL K n,
      ∫ x, F₀ x * (φ : AdelicGLn.AdelicGL K n → ℂ) ((y : AdelicGLn.AdelicGL K n) * x) ∂μ =
        c' * (φ : AdelicGLn.AdelicGL K n → ℂ) y := by
    intro φ hφ y
    have hfin : ∀ u ∈ U, ∀ z, (φ : AdelicGLn.AdelicGL K n → ℂ)
        (z * finEmb K n (u : AdelicGLn.FiniteAdelicGL K n)) = (φ : AdelicGLn.AdelicGL K n → ℂ) z := by
      intro u hu z
      exact congrFun (congrArg Subtype.val ((hS φ hφ).2.2 u hu)) z
    rw [hint (fun x => (φ : AdelicGLn.AdelicGL K n → ℂ) ((y : AdelicGLn.AdelicGL K n) * x))
      (φ.2.1.continuous.comp (continuous_const.mul continuous_subtype_val))
      (fun u hu x => by
        show (φ : AdelicGLn.AdelicGL K n → ℂ) ((y : AdelicGLn.AdelicGL K n) *
          ((x : AdelicGLn.AdelicGL K n) * finEmb K n (u : AdelicGLn.FiniteAdelicGL K n))) = _
        rw [← mul_assoc, hfin u hu])]
    congr 1
    rw [hconv φ hφ y]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [hκcdef]
    rw [hcent φ hφ]
    ring

  have hTφ : ∀ φ ∈ S, (cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ F₀) (cuspToL2 μ φ) =
      (c' : ℂ) • cuspToL2 μ φ :=
    fun φ hφ => cuspRep_integrated_eq_smul μ F₀ (c' : ℂ) φ (hΘ φ hφ)
  have hcomp : IsCompactOperator ((cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ F₀)) :=
    isCompactOperator_cuspRep μ F₀
  have hc0 : (c' : ℂ) ≠ 0 := by exact_mod_cast hc'.ne'
  have hE := ContinuousLinearMap.finite_dimensional_eigenspace hcomp (c' : ℂ) hc0
  exact finiteDimensional_of_map_mem (E := Module.End.eigenspace
      ((cuspRep μ).integrated μ (UnitaryRep.ccToL1 μ F₀)).toLinearMap (c' : ℂ)) (cuspToL2 μ)
    (fun φ hφ => Module.End.mem_eigenspace_iff.2 (hTφ φ hφ))
    (fun φ hφ h0 => eq_zero_of_cuspFormLp_eq_zero μ (hS φ hφ).2.1 h0)

end UnitaryAdmissible

end GroundTheory.Automorphic
