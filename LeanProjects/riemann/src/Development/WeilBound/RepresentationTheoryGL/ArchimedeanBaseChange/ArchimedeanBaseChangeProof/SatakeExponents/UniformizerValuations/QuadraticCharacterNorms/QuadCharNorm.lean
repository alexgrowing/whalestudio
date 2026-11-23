import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterNormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinityTypeUnitaryHeckeCharCMRestrictingToEtaStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.QuadraticCharacterSquare
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.InertCharacterUnramified

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Fok.Mu3
open GlobalTheory.MuExist

theorem quadChar_norm (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)) :
    ‖(((GlobalTheory.GalOfCusp.quadChar E).1 b : ℂˣ) : ℂ)‖ = 1 := by
  change ‖((Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E b) : ℂˣ) : ℂ)‖ = 1
  rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E b) with h | h <;> rw [h] <;> simp

theorem muExists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e := by
  intro E _ _ _ hU
  obtain ⟨U, ψ, hUo, hψc, hψu, hc⟩ := PositivityTheory.Rg.BcB.F.Fok.Mu2.quadratic_character_square E hU
  let α : Eˣ × (Neutral.B1.Ideles (maximalRealSubfield E) × nsUnits E) →* Neutral.B1.Ideles E :=
    (Neutral.B1.diagUnits E).coprod ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E).coprod (nsUnits E).subtype)
  let a : Eˣ × (Neutral.B1.Ideles (maximalRealSubfield E) × nsUnits E) →* ℂˣ :=
    (GlobalTheory.GalOfCusp.quadChar E).1.comp ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _))
  have hα : ∀ y, α y = Neutral.B1.diagUnits E y.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E y.2.1 *
      (y.2.2 : Neutral.B1.Ideles E) := fun y => by
    simp only [α, MonoidHom.coprod_apply, Subgroup.coe_subtype, mul_assoc]
  obtain ⟨χ, hχc, hχu, -, hχα⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Neutral.B1.Ideles E) _ U hUo α a ψ
    hψc hψu (fun y => quadChar_norm E y.2.1) (fun y hy => by
      rw [hα] at hy ⊢
      exact hc y.1 y.2.1 y.2.2 y.2.2.2 hy)
  have hk : ∀ k : Eˣ, χ (Neutral.B1.diagUnits E k) = 1 := fun k => by
    have h := hχα (k, 1, 1)
    rw [hα] at h
    simpa [a] using h
  let μ : HChar E := ⟨χ, hχc, hk⟩
  have hres : ∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x :=
    fun x => by
      have h := hχα (1, x, 1)
      rw [hα] at h
      simpa [a] using h
  have hns : ∀ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ IsSplitAt w →
      Valued.v (u : w.adicCompletion E) = 1 → μ.1 (Neutral.B1.localIdele E w u) = 1 := fun w u hw hu => by
    have h := hχα (1, 1, ⟨_, localIdele_mem_nsUnits w u hw hu⟩)
    rw [hα] at h
    simpa [a] using h
  have hunit : μ.IsUnitary := hχu
  obtain ⟨e, he, hz⟩ := GlobalTheory.T.infinityType_unitaryHeckeCharCM_restricting_to_eta E μ hunit hres
  exact ⟨μ, e, hunit, hres, PositivityTheory.Rg.BcB.F.Fok.Mu3Aux1.inert_character_unramified E hU μ hres hns, he, hz⟩

end PositivityTheory.Rg.BcB.F.Fok.Mu3
