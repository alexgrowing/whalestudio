import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyConjunctionMono
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
namespace GlobalTheory.CoefDuty.LargeRing
theorem evO_laws_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (P₁ P₂ : D7 → Prop), (_root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₂ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup fun D' => P₁ D' ∧ P₂ D') ∧ ((∀ D', P₁ D' → P₂ D') → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₂) ∧ (_root_.GlobalTheory.CoefDuty.AutomorphicSideExists A M C tup → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tup P₁ → ∀ (big₀ : D.what₂.places.Pl → Finset ℂ), ∃ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big₀ w ⊆ big w) ∧ _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L ∧ P₁ (withLoc L)) ∧ ∀ (big big' : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big w ⊆ big' w) → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big' L → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L := by
  classical
  intro D cf jE A M C tup P₁ P₂
  have anti : ∀ (big big' : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), (∀ w, big w ⊆ big' w) →
      _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big' L → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L := by
    intro big big' L h hL
    obtain ⟨Sp, hA, hs⟩ := hL
    exact ⟨{ Sp with iq_big := fun i z hz => Sp.iq_big i z (h _ hz) }, hA, hs⟩
  refine ⟨?_, ?_, ?_, anti⟩
  · rintro ⟨b, hb⟩ ⟨c, hc⟩
    exact ⟨fun w => b w ∪ c w, fun L hL => ⟨hb L (anti _ _ L (fun _ => Finset.subset_union_left) hL),
      hc L (anti _ _ L (fun _ => Finset.subset_union_right) hL)⟩⟩
  · rintro h ⟨b, hb⟩
    exact ⟨b, fun L hL => h _ (hb L hL)⟩
  · rintro hE ⟨b, hb⟩ big₀
    obtain ⟨L, hL⟩ := hE fun w => big₀ w ∪ b w
    exact ⟨fun w => big₀ w ∪ b w, L, fun _ => Finset.subset_union_left, hL,
      hb L (anti _ _ L (fun _ => Finset.subset_union_right) hL)⟩
end GlobalTheory.CoefDuty.LargeRing
end
end
