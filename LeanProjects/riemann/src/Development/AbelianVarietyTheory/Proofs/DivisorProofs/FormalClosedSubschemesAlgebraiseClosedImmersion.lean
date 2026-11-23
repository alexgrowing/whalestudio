import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemMapImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem alg_of_isClosedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (i : W' ⟶ W), IsSeparated f → IsClosedImmersion i → Alg f I →
    Alg (i ≫ f) I := by
  intro R _ I W W' f i hf hi hA t ht hp
  obtain ⟨hs, hsp, hc⟩ := GlobalTheory.T.compatibleReductionSystem_map_immersion R I W W' f i hf inferInstance t ht hp
  obtain ⟨T, hT, hred⟩ := hA _ hs hsp
  refine ⟨T.comap i, ?_, fun e => ?_⟩
  · have h1 : (T.comap i).subschemeι ≫ i ≫ f =
        (T.comapIso i).hom ≫ pullback.snd i T.subschemeι ≫ T.subschemeι ≫ f := by
      rw [← T.comapIso_hom_fst_assoc i, pullback.condition_assoc]
    rw [h1]
    infer_instance
  · rw [← (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1 R W W' f i, ← Scheme.IdealSheafData.comap_sup, hred e]
    exact hc e

end GlobalTheory.FormalAlg
