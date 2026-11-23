import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.BwdSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvFacts
open UpperTheory.V.Lit.Dr
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

private theorem lift_alt {ι V M N : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N] (e : M →ₗ[ℝ] N) (he : Function.Injective e) (F : V [⋀^ι]→ₗ[ℝ] N)
    (h : ∀ X, ∃ m, e m = F X) : ∃ α : V [⋀^ι]→ₗ[ℝ] M, ∀ X, e (α X) = F X := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap.compAlternatingMap
    (F.codRestrict (LinearMap.range e) h), fun X => ?_⟩
  exact congrArg Subtype.val ((LinearEquiv.ofInjective e he).apply_symm_apply (F.codRestrict (LinearMap.range e) h X))

private def piMultilinearForm {ι V N J : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup N] [Module ℝ N]
    (F : J → V [⋀^ι]→ₗ[ℝ] N) : V [⋀^ι]→ₗ[ℝ] (J → N) where
  toMultilinearMap := MultilinearMap.pi fun j => (F j).toMultilinearMap
  map_eq_zero_of_eq' v _ _ h hne := funext fun j => (F j).map_eq_zero_of_eq v h hne

theorem UpperTheory.V.Lit.Dr.corrBwd :
    CorrBwd := by
  intro E _ _ _ a ho U Ξ q w
  obtain ⟨hinj, -, hsurj⟩ := evFacts E a Ξ.d
  obtain ⟨α, hα⟩ := lift_alt ((ev (E := E) (a := a) (d := Ξ.d)).restrictScalars ℝ) hinj
    (piMultilinearForm fun g : GA E a => (mulVecL (Ξ.mat (GeneralLinearGroup.map (pInf E) g)⁻¹)).toLinearMap.compAlternatingMap
      ((w.1 (GeneralLinearGroup.map (pFin E) g : GL (Fin a) (Af E) ⧸ U)
        (sand (GeneralLinearGroup.map (pInf E) g) (hOne E a))).toAlternatingMap.compLinearMap
        ((2 : ℝ) • ((sand (GeneralLinearGroup.map (pInf E) g)).toLinearMap ∘ₗ (hv (E := E) (a := a)).toLinearMap))))
    (fun X => hsurj _ (bwdSmooth E a ho U Ξ q w X))
  refine ⟨α, fun g x X => ?_⟩
  have h1 : GeneralLinearGroup.map (pInf E) (infGL E a g * finGL E a x) = g := by
    rw [map_mul, pInf_infGL, pInf_finGL, mul_one]
  have h2 : GeneralLinearGroup.map (pFin E) (infGL E a g * finGL E a x) = x := by
    rw [map_mul, pFin_infGL, pFin_finGL, one_mul]
  have h3 : ev (α X) (infGL E a g * finGL E a x) =
      Ξ.mat (GeneralLinearGroup.map (pInf E) (infGL E a g * finGL E a x))⁻¹ *ᵥ
      w.1 (GeneralLinearGroup.map (pFin E) (infGL E a g * finGL E a x) : GL (Fin a) (Af E) ⧸ U)
        (sand (GeneralLinearGroup.map (pInf E) (infGL E a g * finGL E a x)) (hOne E a))
        fun i => (2 : ℝ) • sand (GeneralLinearGroup.map (pInf E) (infGL E a g * finGL E a x)) (hv (X i)) :=
    congrFun (hα X) _
  rw [h3, h1, h2, Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
