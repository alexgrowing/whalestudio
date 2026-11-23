import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentSumAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SingleDatum

theorem exists_isHalfIdem : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l : Geo.Tor.Level H), ∃ e : AE D, IsHalfIdem l e := by
  intro D H l
  classical
  have hbar : ∀ x : 𝓞 D.host.E, H.bar x = GlobalTheory.IdemSupport.cO D x := fun x =>
    RingOfIntegers.ext (by rw [H.bar_eq, GlobalTheory.IdemSupport.cO_coe]; rfl)
  have key : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), l.Mb ≤ Q.asIdeal → ¬ l.Mb ≤ (GlobalTheory.IdemSupport.cP Q).asIdeal := by
    intro Q h1 h2
    apply Q.isPrime.ne_top
    rw [eq_top_iff, ← l.coprime]
    refine sup_le h1 (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)
    have h3 := h2 hx
    rw [GlobalTheory.IdemSupport.mem_cP] at h3
    rw [Ideal.mem_comap, RingHom.coe_coe, hbar]
    exact h3
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have h1 := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h1
    have h2 : (l.M : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
    exact h2 h1
  have hfin : {Q : HeightOneSpectrum (𝓞 D.host.E) | l.Mb ≤ Q.asIdeal}.Finite :=
    (Ideal.finite_factors (I := l.Mb) (by rwa [Ideal.zero_eq_bot])).subset fun Q hQ => Ideal.dvd_iff_le.2 hQ
  refine (GlobalTheory.GridIdem.exists_isIdemSum hfin.toFinset ?_ ?_).imp fun e he => ⟨hfin.toFinset, he, fun PP => hfin.mem_toFinset⟩
  · intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    refine GlobalTheory.Hk3.SplitMatch.exists_isIdemAt fun h => key Q hQ fun x hx => ?_
    rw [GlobalTheory.IdemSupport.mem_cP]
    have h4 : Formalism.DivisionValues.cO D.host.E x ∈ (Formalism.DivisionValues.conjPl Q).asIdeal := Ideal.mem_map_of_mem _ (hQ hx)
    rw [h] at h4
    exact h4
  · intro Q hQ Q' hQ' hu
    rw [Set.Finite.mem_toFinset] at hQ hQ'
    rcases GlobalTheory.IdemSupport.eq_or_eq_cP hu with h | h
    · exact h
    · exact absurd (by rw [← h]; exact hQ) (key Q' hQ')

end GlobalTheory.SingleDatum
