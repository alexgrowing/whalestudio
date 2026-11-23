import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUnitaryAdelicIsoMapHaarAndFundamentalDo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjUIntegral

theorem setIntegral_conjU_eq : ∀ {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E), c ≠ 0 →
    ∀ (h : J = c • V.gram) (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) fd ν →
    ∀ dom : Set (UB J), IsFundamentalDomain (ratU D.sp.cm.sig J) dom (ν.map (conjU V c h)) →
    ∀ f : UB J → ℂ, (∀ γ ∈ ratU D.sp.cm.sig J, ∀ x, f (γ * x) = f x) →
      ∫ u in fd, f (conjU V c h u) ∂ν = ∫ x in dom, f x ∂(ν.map (conjU V c h)) := by
  intro D V J c hc h ν fd hν hfd dom hdom f hf
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  have : BorelSpace (UB J) := ⟨rfl⟩
  let φ := GlobalTheory.ConjUTransport.conjEquiv V c hc h
  have c1 : Continuous φ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU V c h
  have c2 : Continuous φ.symm := GlobalTheory.ConjUTransport.continuous_conjUInv V c hc h
  let H : GA D V ≃ₜ UB J := ⟨φ.toEquiv, c1, c2⟩
  have hme : MeasurableEmbedding (conjU V c h) := H.measurableEmbedding
  obtain ⟨hH, hfd'⟩ := GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain V c hc h ν fd hν hfd
  have e1 : ∫ x in conjU V c h '' fd, f x ∂(ν.map (conjU V c h)) = ∫ u in fd, f (conjU V c h u) ∂ν := by
    rw [hme.setIntegral_map, Set.preimage_image_eq _ hme.injective]
  rw [← e1]
  haveI := GlobalTheory.UnitaryVol.countable_ratU D.sp.cm.sig J
  haveI := hH
  haveI : SMulInvariantMeasure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (UB J) (ν.map (conjU V c h)) :=
    ⟨fun γ A _ => measure_preimage_mul (ν.map (conjU V c h)) γ.1 A⟩
  exact hfd'.setIntegral_eq hdom fun γ x => hf γ.1 γ.2 x

end GlobalTheory.ConjUIntegral
