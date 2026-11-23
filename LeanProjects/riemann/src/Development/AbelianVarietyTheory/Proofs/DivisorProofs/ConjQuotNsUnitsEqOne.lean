import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupDivEqMulDivMulInvDiv
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ConsEta
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele

theorem under_under_of_compat {F K L : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra F K] [Algebra F L] [alg : Algebra K L]
    (hc : ∀ x : F, algebraMap K L (algebraMap F K x) = algebraMap F L x) (w : HeightOneSpectrum (𝓞 L)) :
    (w.under (𝓞 K)).under (𝓞 F) = w.under (𝓞 F) := by
  ext x
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.mem_under]
  have : algebraMap (𝓞 K) (𝓞 L) (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap (𝓞 F) (𝓞 L) x := by
    apply RingOfIntegers.ext
    exact hc (x : F)
  rw [this]

theorem finEval_ideleMap_localIdele {F K L : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra F K] [Algebra F L] [alg : Algebra K L]
    (hc : ∀ x : F, algebraMap K L (algebraMap F K x) = algebraMap F L x) (w : HeightOneSpectrum (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.under (𝓞 F) ≠ w.under (𝓞 F)) (a : (v.adicCompletion K)ˣ) :
    Units.map (GlobalTheory.IdeleNormChar.finEval w) (ideleMap K L (Neutral.B1.localIdele K v a)) = 1 := by
  have hne : w.under (𝓞 K) ≠ v := fun h => hv (h ▸ under_under_of_compat hc w)
  apply Units.ext
  show finiteCompletionMap K L w ((Neutral.B1.localIdele K v a : AdeleRing (𝓞 K) K).2 (w.under (𝓞 K))) = 1
  rw [(Neutral.B1.localIdele_isSupportedAt K v a).2 _ hne, map_one]

theorem isSplitAt_of_under_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {v w : HeightOneSpectrum (𝓞 E)}
    (hw : GlobalTheory.UnitaryBC.IsSplitAt w)
    (h : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) :
    GlobalTheory.UnitaryBC.IsSplitAt v := by
  obtain ⟨u, hu, hu'⟩ := hw
  by_cases hvw : v = w
  · subst hvw; exact ⟨u, hu, hu'⟩
  · exact ⟨w, Ne.symm hvw, h.symm⟩

theorem conjQuot_nsUnits_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.UnitaryBC.IsSplitAt w → ∀ u ∈ GlobalTheory.MuExist.nsUnits E, GlobalTheory.ConsEta.conjQuot E w u = 1 := by
  intro E _ _ _ w hw u hu
  have key : GlobalTheory.MuExist.nsUnits E ≤ (conjQuot E w).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨w', a, hw', -, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have hne : w' ≠ w := fun h => hw' (h ▸ hw)
    have hunder : w'.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
      fun h => hw' (isSplitAt_of_under_eq hw h)
    have h1 : Units.map (GlobalTheory.IdeleNormChar.finEval w) (Neutral.B1.localIdele E w' a) = 1 :=
      Units.ext ((Neutral.B1.localIdele_isSupportedAt E w' a).2 w hne.symm)
    have h2 : Units.map (GlobalTheory.IdeleNormChar.finEval w)
        (ideleConj (maximalRealSubfield E) E (Neutral.B1.localIdele E w' a)) = 1 :=
      finEval_ideleMap_localIdele (F := maximalRealSubfield E)
        (alg := (conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra)
        (fun x => (conj (maximalRealSubfield E) E).commutes x) w w' hunder a
    simp only [conjQuot, MonoidHom.comp_apply, MonoidHom.div_apply, MonoidHom.id_apply, _root_.map_div, h1, h2, div_one]
  exact key hu

end GlobalTheory.ConsEta
