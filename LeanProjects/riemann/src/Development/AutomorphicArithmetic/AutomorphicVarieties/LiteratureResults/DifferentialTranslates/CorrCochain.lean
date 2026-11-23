import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvK
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.EvFacts

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open scoped TensorProduct

private theorem mat_cancel {E : Type} [Field E] [NumberField E] {a : ℕ} (Ξ : AlgRep E a) (g : GL (Fin a) (Cinf E))
    {v v' : Fin Ξ.d → ℂ} (h : Ξ.mat g *ᵥ v = Ξ.mat g *ᵥ v') : v = v' := by
  have h2 := congrArg (fun z => Ξ.mat g⁻¹ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] using h2

private theorem sand_unit_one {E : Type} [Field E] [NumberField E] {a : ℕ} (k : Kinf E a) :
    sand (Unitary.toUnits k) (hOne E a) = hOne E a := Subtype.ext (by
  change k.1 * (1 : Matrix (Fin a) (Fin a) (Cinf E)) * star k.1 = (1 : Matrix (Fin a) (Fin a) (Cinf E))
  rw [mul_one]
  exact k.2.2)

private theorem sand_unit_hv {E : Type} [Field E] [NumberField E] {a : ℕ} (k : Kinf E a) (X : Herm E a) :
    sand (Unitary.toUnits k) (hv X) = hv (adHerm k X) := rfl

theorem UpperTheory.V.Lit.Dr.corrCochain :
    CorrCochain := by
  intro E _ _ _ a U Ξ q α w h
  refine ⟨fun k X => ?_, fun X u hu g => ?_⟩
  · refine (evFacts E a Ξ.d).1 (funext fun g => ?_)
    rw [evK, ← infGL_mul_finGL g]
    generalize GeneralLinearGroup.map (pInf E) g = y
    generalize GeneralLinearGroup.map (pFin E) g = x
    refine mat_cancel Ξ y ?_
    have h1 := h (y * Unitary.toUnits k) x X
    rw [← h y x, Matrix.mulVec_mulVec, ← map_mul, mul_assoc, ← infGL_comm, ← mul_assoc, ← map_mul, ← h1]
    simp only [map_mul, ContinuousLinearMap.mul_apply, sand_unit_one, sand_unit_hv]
  · rw [← infGL_mul_finGL g]
    generalize GeneralLinearGroup.map (pInf E) g = y
    generalize GeneralLinearGroup.map (pFin E) g = x
    refine mat_cancel Ξ y ?_
    rw [mul_assoc, ← map_mul, ← h y x, ← h y (x * u), QuotientGroup.mk_mul_of_mem x hu]
