import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below finiteAdeleMap_apply)

theorem UpperTheory.Gal.W2.Seed.pIdemP :
    IdemP := by
  classical
  intro p _ E _ _
  let e : AfQ := ⟨fun v => if (p : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0,
    Filter.Eventually.of_forall fun v => by
      by_cases h : (p : 𝓞 ℚ) ∈ v.asIdeal
      · simpa [h] using one_mem (v.adicCompletionIntegers ℚ)
      · simpa [h] using zero_mem (v.adicCompletionIntegers ℚ)⟩
  have he : ∀ v : Plc ℚ, e v = if (p : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0 := fun v => rfl
  refine ⟨e, fun v => ⟨fun h => by rw [he, if_pos h], fun h => by rw [he, if_neg h]⟩, fun w => ?_⟩
  have hiff : (p : 𝓞 ℚ) ∈ (below ℚ w).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
    show (p : 𝓞 ℚ) ∈ w.asIdeal.under (𝓞 ℚ) ↔ _
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
  have hl : pLoc E w (finiteAdeleMap ℚ E e) =
      GroundTheory.Global.SemiLocal.completionMap (below ℚ w) w (e (below ℚ w)) := rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hl, he, if_pos (hiff.2 h), map_one]
  · rw [hl, he, if_neg (fun h' => h (hiff.1 h')), map_zero]
