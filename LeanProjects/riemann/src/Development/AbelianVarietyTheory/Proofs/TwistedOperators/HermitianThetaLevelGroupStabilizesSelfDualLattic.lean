import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmHostFractionalIdealPartitionOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmulMemHermitianLatticeAdelicCompletionOfSmulLeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeTransportOfPolarisationIdealTimesLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicMemFrameStabilizerOfLatticeTransportStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecSubMemLatticeCompletionOfLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeTransportCongruenceOfFrameVectorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceModPrimeOfPolarisationIdealTimesLatticStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeReductionEqOneOfCompletionCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionTrivialOfConjugatePlaceSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugatePlaceCmFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevKFrame

theorem levK_frame : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ βT : GL (Fin T.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame βT ΛT → ∀ Pg : Finset (Formalism.L2.DIV.Pl D.host.E), (∀ PP ∈ Pg, Lv.𝔪 ≤ conjI PP.asIdeal) → (∀ κ ∈ Lv.J, ∀ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E), κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) → ∀ PP ∈ Pg, ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ conjI PP.asIdeal) → ∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → Lev.finE T k ∈ Formalism.L2.DIV.St βT ∧ ∀ PP ∈ Pg, Formalism.L2.DIV.redFn βT PP (Lev.finE T k) = 1 := by
  intro D S T C Lv ΛT hsd hAA βT hfr Pg hPg hJ k κ hk
  obtain ⟨-, hmov, κ', hκ', hc⟩ := hk
  have hmovT := GlobalTheory.T.latticeTransport_of_polarisationIdealTimesLattice D C.X.Λ ΛT (fmt T k) hAA hmov
  have hSt := GlobalTheory.T.finiteAdelic_mem_frameStabilizer_of_latticeTransport D T ΛT βT hfr k hmovT
  refine ⟨hSt, fun PP hPP => ?_⟩
  obtain ⟨PP', hPP', hcj⟩ := GlobalTheory.T.exists_conjugatePlace_cmField D PP
  have hI : ∀ i j, κ' i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E)) i j ∈ PP'.asIdeal := by
    rw [hPP']; exact hJ κ κ.2 κ' hκ' PP hPP
  have h1 := GlobalTheory.T.latticeTransport_congruence_of_frameVectors D C.X.Λ Lv.β Lv.𝔪 PP'.asIdeal Lv.β_mem Lv.β_span (hPP' ▸ hPg PP hPP) (fmt T k) κ' hI hmov hc
  have h2 := GlobalTheory.T.mulVec_sub_mem_latticeCompletion_of_lattice D C.X.Λ (PP'.asIdeal • C.X.Λ) (fmt T k) h1
  obtain ⟨b, hb, h3⟩ := GlobalTheory.T.congruenceModPrime_of_polarisationIdealTimesLattice D C.X.Λ ΛT PP'.asIdeal PP'.isPrime hAA (fmt T k) h2
  have h4 := GlobalTheory.T.lattice_reduction_eq_one_of_completion_congruence D T ΛT βT hfr k hSt PP' b hb h3
  exact GlobalTheory.T.reductionTrivial_of_conjugatePlace_selfDual D T ΛT hsd βT hfr k hSt PP PP' hcj h4

end GlobalTheory.LevKFrame

end
