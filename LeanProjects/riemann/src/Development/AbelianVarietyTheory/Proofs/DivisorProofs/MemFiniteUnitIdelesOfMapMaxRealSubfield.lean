import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupDivEqMulDivMulInvDiv
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitDown

theorem exists_above {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v := by
  haveI := v.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hP.over, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  refine ⟨⟨P, hPm.isPrime, hne⟩, ?_⟩
  ext1
  rw [HeightOneSpectrum.under_asIdeal]
  exact hP.over.symm

theorem unit_down : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b ∈ GlobalTheory.Mem.Chr.unitIdl E → b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) := by
  intro E _ _ _ b hb v
  obtain ⟨w, rfl⟩ := exists_above (E := E) v
  have h := hb w
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b : AdeleRing (𝓞 E) E).2 w) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap (maximalRealSubfield E) E w
        ((b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 (w.under _)) := rfl
  rw [e, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap] at h
  have he : (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under _).ne_bot
  set x := Valued.v ((b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 (w.under _))
  set n := (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal
  have h' : x ^ n = 1 := h
  rcases lt_trichotomy x 1 with hx | hx | hx
  · exact absurd h' (pow_lt_one₀ zero_le' hx he).ne
  · exact hx
  · exact absurd h' (one_lt_pow₀ hx he).ne'

end GlobalTheory.UnitDown
