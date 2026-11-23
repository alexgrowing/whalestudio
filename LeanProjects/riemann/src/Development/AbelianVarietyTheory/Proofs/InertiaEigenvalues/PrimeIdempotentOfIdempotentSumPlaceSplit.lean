import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical

namespace GlobalTheory.IdemSumBranch

open GlobalTheory.StdFrames GlobalTheory.IdemSupport

variable {D : D7}

theorem cpt_idemSum {ea : AE D} {S : Finset (Pl D.host.E)} (h : IsIdemSum ea S) {Q : Pl D.host.E} (hQ : Q ∈ S) :
    cpt Q (toEAf D ea) = 1 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  have hs := map_sum ((cpt Q).comp (toEAf D)).toAddMonoidHom es S
  refine hs.trans ?_
  rw [Finset.sum_eq_single_of_mem Q hQ]
  · exact (cpt_of_isIdemAt (hes Q hQ)).1
  · intro R hR hne
    exact (cpt_of_isIdemAt (hes R hR)).2 Q hne.symm

theorem conjPrime_ne {ea : AE D} {S : Finset (Pl D.host.E)} (h : IsIdemSum ea S) {P Q : Pl D.host.E} (hP : P ∈ S)
    (hQ : Q ∈ S) : cP Q ≠ P := by
  intro hc
  have h1 := congrArg (fun t => cpt P (toEAf D t)) h.2
  simp only [RingHom.map_mul, RingHom.map_zero, cpt_idemSum h hP, one_mul] at h1
  rw [toEAf_cA, ← hc] at h1
  have h2 := cpt_sg_eq_zero h1
  rw [sg_sg, cpt_idemSum h hQ] at h2
  exact one_ne_zero h2

theorem branch : ∀ (D : D7) (P : Pl D.host.E) (e f ea : AE D) (S : Finset (Pl D.host.E)),
    IsPrimeIdem P e f → IsIdemSum ea S → P ∈ S → Formalism.L2.NTheta.IsIdemAt e P ∧ f = e + cA D e ∧ cA D f = f ∧
      infPart D f = 0 ∧ ∀ PP ∈ S, GlobalTheory.IdemSupport.cP PP ≠ P := by
  intro D P e f ea S h1 hS hP
  obtain ⟨hd, ε, hε, hf⟩ := of_isPrimeIdem (comp_toAd D) h1
  have hinf : infPart D f = 0 := hf ▸ (place_comp (comp_toAd D) hε).1
  rcases h1 with ⟨h1, h2⟩ | ⟨rfl, -⟩
  · refine ⟨h1, h2, ?_, hinf, fun Q hQ => conjPrime_ne hS hP hQ⟩
    rw [h2, RingHom.map_add, Formalism.L2.Theta.cA_cA, add_comm]
  · exfalso
    have h2 := (place_comp (comp_toAd D) hε).2.1 (cP P) (under_cP P)
    rw [← hf, hd.2.2 _ (conjPrime_ne hS hP hP)] at h2
    exact zero_ne_one h2

end GlobalTheory.IdemSumBranch
