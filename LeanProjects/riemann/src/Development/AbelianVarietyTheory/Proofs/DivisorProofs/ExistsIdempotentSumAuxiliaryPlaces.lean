import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalVAlgebraMapMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridIdem

open GlobalTheory.IdemModTwo

variable {D : D7}

theorem splitAt_under {e : Formalism.L2.Theta.AE D} {Q : HeightOneSpectrum (𝓞 D.host.E)}
    (h : Formalism.L2.NTheta.IsIdemAt e Q) : SplitAt D (Q.under (𝓞 D.host.F)) e := by
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 h.1
  obtain ⟨Q', hQ, hQv⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D v e he
  obtain rfl : Q = Q' := HeightOneSpectrum.ext (Ideal.ext fun x => by
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [h.2 x hx, hQ.2 x hx])
  have : Q.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hQv
  rwa [this]

theorem exists_isIdemSum (S : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (h : ∀ Q ∈ S, ∃ e : Formalism.L2.Theta.AE D, Formalism.L2.NTheta.IsIdemAt e Q)
    (hinj : ∀ Q ∈ S, ∀ Q' ∈ S, Q.under (𝓞 D.host.F) = Q'.under (𝓞 D.host.F) → Q = Q') :
    ∃ e : Formalism.L2.Theta.AE D, IsIdemSum e S := by
  choose! es hes using h
  refine ⟨∑ Q ∈ S, es Q, ⟨es, hes, rfl⟩, ?_⟩
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun Q hQ => Finset.sum_eq_zero fun Q' hQ' => ?_
  by_cases hq : Q = Q'
  · subst hq
    exact (hes Q hQ).1.2.1
  · exact (splitAt_under (hes Q hQ)).orth (splitAt_under (hes Q' hQ')).conj fun h => hq (hinj Q hQ Q' hQ' h)

theorem exists_idempotentSum_auxiliaryPlaces : ∀ (D : D7) (T : Type) (L : LevCh D T) (P : Places L), ∃ e : Formalism.L2.Theta.AE D, IsIdemSum e P.W0 := by
  classical
  intro D T L P
  have hm : ∀ Q ∈ P.W0, ∃ v ∈ P.S0, P.w v = Q := fun Q hQ => by
    unfold Places.W0 at hQ
    exact Finset.mem_image.1 (by convert hQ)
  refine exists_isIdemSum _ (fun Q hQ => ?_) fun Q hQ Q' hQ' h => ?_
  · obtain ⟨v, hv, rfl⟩ := hm Q hQ
    exact P.w_split v hv
  · obtain ⟨v, hv, rfl⟩ := hm Q hQ
    obtain ⟨v', hv', rfl⟩ := hm Q' hQ'
    rw [P.under_w hv, P.under_w hv'] at h
    rw [h]

end GlobalTheory.GridIdem
