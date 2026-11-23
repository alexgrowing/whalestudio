import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlaces
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGeneratorPlaceValuationBound
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaLow
open GlobalTheory.ThetaBound GlobalTheory.PlaceInt

theorem finite_vLa_ne_zero {K : Type} [Field K] [NumberField K] (x : K) :
    {w : HeightOneSpectrum (𝓞 K) | vLa w x ≠ 0}.Finite := by
  by_cases hx : x = 0
  · subst hx
    convert Set.finite_empty
    ext w
    simp [vLa]
  · refine (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 x hx)).subset fun w hw h1 => hw ?_
    simp only [Units.val_mk0] at h1
    simp [vLa, h1]

theorem vLa_natCast_eq_zero {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {g p : ℕ}
    (hg : ((g : ℕ) : 𝓞 K) ∈ w.asIdeal) (hc : Nat.Coprime g p) : vLa w ((p : ℕ) : K) = 0 := by
  have hp : ((p : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    intro hp
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 K))
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← huv]
    simp only [eq_intCast, Int.cast_natCast]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hg) (Ideal.mul_mem_left _ _ hp)
  have h1 : w.valuation K ((p : ℕ) : K) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) p, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hp
  simp [vLa, h1]

theorem thetaRule_bounded_below : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (g g' : ℕ) (π π' : 𝓞 D.host.E), HalfSplit l g g' π π' → Nat.Coprime (g * g') (D.host.QS * D.host.q * D.host.d) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∃ m : HeightOneSpectrum (𝓞 c.F) → ℝ, (Function.support m).Finite ∧ (∀ f ∈ thGen Xo c nab a n, ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((m w : ℝ) : EReal) ≤ v f) ∧ ∀ w : HeightOneSpectrum (𝓞 c.F), (((g : ℕ) : 𝓞 c.F) ∈ w.asIdeal ∨ ((g' : ℕ) : 𝓞 c.F) ∈ w.asIdeal) → m w = -((vLa w (nrm Dw c a (star π * star π')) : ℤ) : ℝ) := by
  intro D H Dw l Xo c
  letI := H.starRing
  intro nab hnab g g' π π' hs hcop a n
  have hstar : ∀ x : 𝓞 D.host.E, star x = H.bar x := hnab.1
  obtain ⟨hg, hg', hne, hM, hπ, hπ', hMb, -, -⟩ := hs
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hπ
    exact hg.ne_zero (by exact_mod_cast hπ.symm)
  have hπ0' : π' ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hπ'
    exact hg'.ne_zero (by exact_mod_cast hπ'.symm)
  have hb0 : star π * star π' ≠ 0 := by
    rw [hstar, hstar]
    refine mul_ne_zero (fun h => hπ0 ?_) (fun h => hπ0' ?_)
    · rw [← TorsFac.bar_bar (H := H) π, h, map_zero]
    · rw [← TorsFac.bar_bar (H := H) π', h, map_zero]
  let ρ : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ p ∈ D.host.condN.primeFactors, ((vLa w ((p : ℕ) : c.F) : ℤ) : ℝ) *
      D.host.vdH p * (Formalism.L2.Pj.DF Dw a : ℝ) / 2
  refine ⟨fun w => -(ρ w + ((vLa w (nrm Dw c a (star π * star π')) : ℤ) : ℝ)), ?_, ?_, ?_⟩
  ·
    have hfin : ((⋃ p ∈ D.host.condN.primeFactors,
        {w : HeightOneSpectrum (𝓞 c.F) | vLa w ((p : ℕ) : c.F) ≠ 0}) ∪
        {w | vLa w (nrm Dw c a (star π * star π')) ≠ 0}).Finite :=
      (Set.Finite.biUnion (Finset.finite_toSet _) fun p _ => finite_vLa_ne_zero _).union (finite_vLa_ne_zero _)
    refine hfin.subset fun w hw => ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists, not_not] at hn
    apply hw
    have h0 : ρ w = 0 := Finset.sum_eq_zero fun p hp => by rw [hn.1 p hp]; simp
    simp [h0, hn.2]
  · intro f hf w v hv
    obtain ⟨y, rfl⟩ := hv
    obtain ⟨T, io, e, ho, yI, hy, eta, heta, hq⟩ := y.2
    have hv : vAtV y f = nval T.V e (evI yI f) := by
      show y.1.1 f = _
      rw [hq]
      rfl
    rw [hv]
    refine bound_of_chBound Xo c (star π * star π') hb0 ?_ nab hnab w a n (ρ w) ?_ T io e ho yI hy f hf
    · intro ℓ hp hd
      rw [hM] at hd ⊢
      rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hg').1 h1
        refine ⟨fun h2 => hne ?_, star π', star π, _root_.mul_comm _ _, ?_, ?_⟩
        · rw [pow_two] at h2
          exact ((Nat.prime_dvd_prime_iff_eq hg' hg).1 (Nat.dvd_of_mul_dvd_mul_left hg'.pos h2)).symm
        · rw [hstar, TorsFac.bar_bar, _root_.mul_comm]; exact hπ'
        · rw [hMb, hstar, TorsFac.bar_bar, Ideal.span_singleton_le_span_singleton]
          exact Dvd.intro_left _ rfl
      · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hg).1 h1
        refine ⟨fun h2 => hne ?_, star π, star π', rfl, ?_, ?_⟩
        · rw [pow_two] at h2
          exact (Nat.prime_dvd_prime_iff_eq hg hg').1 (Nat.dvd_of_mul_dvd_mul_right hg.pos h2)
        · rw [hstar, TorsFac.bar_bar, _root_.mul_comm]; exact hπ
        · rw [hMb, hstar, TorsFac.bar_bar, Ideal.span_singleton_le_span_singleton]
          exact Dvd.intro _ rfl
    · intro T' io' y' C' e' ho'
      have hc := HostChart.chBound_host D H Dw l Xo c hstar T' io' y' C' e' ho'.1 a n
        (Formalism.L2.Pj.DF Dw a) le_rfl
      convert hc using 1
      refine Finset.sum_congr rfl fun p _ => ?_
      have h1 := ho'.2 ((p : ℕ) : c.F)
      rw [map_natCast] at h1
      have he : (e' : ℝ) ≠ 0 := by exact_mod_cast ho'.1.ne'
      rw [h1]
      push_cast
      rw [mul_div_cancel_left₀ _ he]
  · intro w hw
    have h0 : ρ w = 0 := Finset.sum_eq_zero fun p hp => by
      have hcp : Nat.Coprime (g * g') p := Nat.Coprime.coprime_dvd_right (Nat.dvd_of_mem_primeFactors hp) hcop
      rcases hw with hw | hw
      · rw [vLa_natCast_eq_zero w hw (Nat.Coprime.coprime_dvd_left (dvd_mul_right g g') hcp)]; simp
      · rw [vLa_natCast_eq_zero w hw (Nat.Coprime.coprime_dvd_left (dvd_mul_left g' g) hcp)]; simp
    show -(ρ w + _) = _
    rw [h0, zero_add]
end GlobalTheory.ThetaLow
