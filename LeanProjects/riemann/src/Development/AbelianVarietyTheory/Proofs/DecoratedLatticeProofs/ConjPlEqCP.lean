import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelPlaces

open IsDedekindDomain NumberField GlobalTheory.IdemSupport

variable {D : D7} {Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}

theorem ev_sum {ι : Type} (s : Finset ι) (f : ι → Formalism.L2.Theta.AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (∑ i ∈ s, f i) Q = ∑ i ∈ s, Φ (f i) Q := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, ev_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ev_add, ih]

theorem conjPl_eq_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.DivisionValues.conjPl P = cP P :=
  (GlobalTheory.IdemSupport.isConjPl_iff P _).1 (GlobalTheory.GoodPrimes.isConjPl_iff.2 rfl)

theorem under_injOn {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} (h : Formalism.IndefR.Datum.IsIdemSum e P) :
    Set.InjOn (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.under (𝓞 D.host.F)) (P : Set (Formalism.L2.DIV.Pl D.host.E)) := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, h0⟩ := h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  intro PP hPP PP' hPP' hu
  by_contra hne
  have hd : ∀ Q ∈ P, IsDelta Φ Q (es Q) := fun Q hQ => delta_of_isIdemAt hΦ (hes Q hQ)
  have hc' : PP' = cP PP := by
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (D := D) hu.symm with h1 | h1
    · exact absurd h1.symm hne
    · rw [h1, conjPl_eq_cP]
  have hc : PP = cP PP' := by
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (D := D) hu with h1 | h1
    · exact absurd h1 hne
    · rw [h1, conjPl_eq_cP]
  have e1 : Φ (∑ Q ∈ P, es Q) PP = 1 := by
    rw [ev_sum, Finset.sum_eq_single PP (fun Q hQ hQP => (hd Q hQ).2.2 PP (Ne.symm hQP))
      (fun h => absurd (Finset.mem_coe.1 hPP) h), (hd PP (Finset.mem_coe.1 hPP)).2.1]
  have e2 : Φ (cA D (∑ Q ∈ P, es Q)) PP = 1 := by
    rw [map_sum, ev_sum, Finset.sum_eq_single PP' ?_ (fun h => absurd (Finset.mem_coe.1 hPP') h)]
    · have := (delta_conj hΦ (hd PP' (Finset.mem_coe.1 hPP'))).2.1
      rwa [← hc] at this
    · intro Q hQ hQP
      refine (delta_conj hΦ (hd Q hQ)).2.2 PP fun hQc => ?_
      have hv : Q.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) := by rw [← under_cP Q, ← hQc]
      rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (D := D) hv with h1 | h1
      · rw [h1] at hQc
        exact hne (hc'.trans hQc.symm).symm
      · rw [conjPl_eq_cP, ← hc'] at h1
        exact hQP h1
  have e3 := ev_mul (Φ := Φ) (∑ Q ∈ P, es Q) (cA D (∑ Q ∈ P, es Q)) PP
  rw [h0, ev_zero, e1, e2, one_mul] at e3
  exact zero_ne_one e3

theorem injOn_under : ∀ (D : D7) (c : GlobalTheory.ChainOnto.Com D), c.Is → Set.InjOn (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.under (NumberField.RingOfIntegers D.host.F)) (c.Pg : Set (Formalism.L2.DIV.Pl D.host.E)) := by
  intro D c hc
  obtain ⟨e, he⟩ := hc.split
  exact under_injOn he

end GlobalTheory.LevelPlaces
