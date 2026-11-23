import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HostIdealUnitAtPlacesPrimeToLevel

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff

namespace GlobalTheory.AAUnit

theorem natCast_notMem_of_coprime {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {n p : ℕ}
    (h : Nat.Coprime n p) (hp : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) : ((n : ℕ) : 𝓞 K) ∉ w.asIdeal := by
  intro hn
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr h).map (Int.castRingHom (𝓞 K))
  have h1 : (1 : 𝓞 K) ∈ w.asIdeal := by
    rw [← huv]
    simp only [eq_intCast, Int.cast_natCast]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left u hn) (w.asIdeal.mul_mem_left v hp)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem absNorm_cmIdeal_not_mem_gridPlaces {D : D7} {T : Type} {L : LevCh D T} (P : Places L) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ P.S0) : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
  rcases P.mem_S0_of_sum_eq.mp hv with h | h
  ·
    subst h
    have hq := GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (D := D)
    exact natCast_notMem_of_coprime P.v0 ((Nat.Prime.coprime_iff_not_dvd hq.1).mpr hq.2.2).symm P.basePlace_over_qZero
  ·
    have hcop : ∀ p ∈ D.host.levelPrimes, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
        ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal :=
      fun p hp hpv => natCast_notMem_of_coprime v (D.host.ccK_coprime p (by simp [hp])) hpv
    rcases (GlobalTheory.ChiGrid.S1_mem_OmF (D := D)).mp h with h' | h' | h' | h'
    · exact hcop _ (D.host.g_level 0) h'
    · exact hcop _ (D.host.g_level 1) h'
    · exact hcop _ D.host.pde_level.1 h'
    · exact hcop _ D.host.pde_level.2 h'

theorem exists_valuation_one_element_at_grid_places : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, GlobalTheory.SepRows.OffQ D → L.Is μ₀ → ∀ (G : GridData L sc), ∀ w ∈ G.pl.W0, ∃ a ∈ D.host.AA, Valued.v ((algebraMap D.host.E (Kw w)) a) = 1 := by
  intro D T L sc μ₀ _ _ G w hw
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw

  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ (G.pl.w v).asIdeal := by
    intro hin
    apply absNorm_cmIdeal_not_mem_gridPlaces G.pl hv
    have hc : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∈ ((G.pl.w v).under (𝓞 D.host.F)).asIdeal := by
      show ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) ∈
        Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (G.pl.w v).asIdeal
      rw [Ideal.mem_comap, map_natCast]
      exact hin
    rw [G.pl.under_w hv] at hc
    exact hc
  refine ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩
  have key := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) (v := G.pl.w v)).mpr hN
  rw [map_natCast] at key
  first
  | exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := G.pl.w v) _).trans key
  | (erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']; exact key)

end GlobalTheory.AAUnit
