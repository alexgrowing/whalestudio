import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

namespace GlobalTheory.LeviAt

theorem embAt_projAt_mem_parab {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : CMData F E) (V : HSpace E) (W : Submodule E V.V) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : GAd hc.sig V.gram) (ht : t ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab hc V (AF F) W) :
    embAt hc.sig V.gram S (projAt hc.sig V.gram S t) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab hc V (AF F) W := by
  have h := mem_atPts.1 (embAt_mem hc.sig V.gram S (projAt hc.sig V.gram S t))
  refine mem_parab_of_adelic (fun w => ?_) fun v => ?_
  · rw [mem_finPts_iff_forall.1 h.1 w]; exact one_mem _
  · by_cases hv : v ∈ S
    · rw [proj_embAt hc.sig V.gram S _ ⟨v, hv⟩]
      exact mapH_mem_parab (evFin F v) ht
    · rw [h.2 v hv]; exact one_mem _

theorem embAt_projAt_mem_levi : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (P : Finset (SV (wittIndex V))) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : GAd D.sp.cm.sig V.gram), t ∈ Φ.levi D.sp.cm (AF D.host.F) P → embAt D.sp.cm.sig V.gram S (projAt D.sp.cm.sig V.gram S t) ∈ Φ.levi D.sp.cm (AF D.host.F) P := by
  intro D V Φ P S t ht
  simp only [WittFrame.levi, Subgroup.mem_iInf, Subgroup.mem_inf] at ht ⊢
  exact fun u hu => ⟨embAt_projAt_mem_parab _ _ _ S t (ht u hu).1, embAt_projAt_mem_parab _ _ _ S t (ht u hu).2⟩

end GlobalTheory.LeviAt
