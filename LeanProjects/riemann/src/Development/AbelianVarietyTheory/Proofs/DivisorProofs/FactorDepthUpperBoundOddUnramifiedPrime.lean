import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStepCharactersOfColengthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitOfUnramifiedPrimeStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersBoundedMinorEigenspace
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UnramifiedCompanionChartCharacters
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FacUpOdd

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem inPsi_conj_iff (H : Host E) (τ : E →+* ℂ) :
    InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have him := congrArg Complex.im H.sqrt_neg_disc_sq
  simp [pow_two] at hre him
  have hre0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  have hc : starRingEnd ℂ H.rt0 = -H.rt0 := Complex.ext (by simp [hre0]) (by simp)
  have h0 : H.rt0 ≠ 0 := by
    intro h0
    rw [h0] at hre
    simp at hre
    exact H.d_prime.ne_zero (by exact_mod_cast hre)
  have h3 : ¬ (-H.rt0 = H.rt0) := fun h => h0 (by linear_combination (-1/2 : ℂ) * h)
  have hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow]
    have : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [this]; simp
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · rw [h, hc]; simp [h3]
  · rw [h, map_neg, hc, neg_neg]; simp [h3]

theorem mult_of_inPsi {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : InPsi H τ) : Dw.mult τ = Dw.p := by
  unfold Datum.mult; rw [if_pos (show τ (H.rt : E) = H.rt0 from h)]

theorem mult_of_not_inPsi {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : ¬ InPsi H τ) : Dw.mult τ = Dw.q := by
  unfold Datum.mult; rw [if_neg (show ¬ τ (H.rt : E) = H.rt0 from h)]

theorem rpow_neg_succ (p : ℕ) (hp : 0 < p) (i : ℕ) :
    (p : ℝ) ^ (-((i : ℝ) + 1)) = ((p : ℝ)⁻¹) ^ (i + 1) := by
  have hp0 : (0 : ℝ) ≤ p := by positivity
  rw [Real.rpow_neg hp0, show ((i : ℝ) + 1) = ((i + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, inv_pow]

theorem tsum_const (p : ℕ) (hp : 1 < p) (q : ℝ) :
    ∑' i : ℕ, (p : ℝ) ^ (-((i : ℝ) + 1)) * q = q / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have r0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have r1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have e : (fun i : ℕ => (p : ℝ) ^ (-((i : ℝ) + 1)) * q) = fun i => ((p : ℝ)⁻¹) ^ i * ((p : ℝ)⁻¹ * q) := by
    funext i; rw [rpow_neg_succ p (by omega), pow_succ]; ring
  rw [e, tsum_mul_right, tsum_geometric_of_lt_one r0 r1]
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  have : (p : ℝ) ≠ 0 := by linarith
  field_simp

theorem tsum_alt (p : ℕ) (hp : 1 < p) (a b : ℝ) :
    ∑' i : ℕ, (p : ℝ) ^ (-((i : ℝ) + 1)) * (if Even i then a else b) = (a * p + b) / ((p : ℝ) ^ 2 - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  set r : ℝ := (p : ℝ)⁻¹ with hr
  have r0 : (0 : ℝ) ≤ r ^ 2 := by positivity
  have r1 : r ^ 2 < 1 := by
    have : r < 1 := inv_lt_one_of_one_lt₀ hp1
    have : 0 ≤ r := by positivity
    nlinarith
  set g : ℕ → ℝ := fun i => (p : ℝ) ^ (-((i : ℝ) + 1)) * (if Even i then a else b) with hg
  have ge : (fun k => g (2 * k)) = fun k => (r ^ 2) ^ k * (r * a) := by
    funext k
    simp only [hg]
    rw [rpow_neg_succ p (by omega), if_pos (even_two_mul k), ← hr, pow_succ, pow_mul]; ring
  have go : (fun k => g (2 * k + 1)) = fun k => (r ^ 2) ^ k * (r ^ 2 * b) := by
    funext k
    simp only [hg]
    rw [rpow_neg_succ p (by omega), if_neg (Nat.not_even_iff_odd.2 (odd_two_mul_add_one k)), ← hr,
      show 2 * k + 1 + 1 = 2 * k + 2 by ring, pow_add, pow_mul]; ring
  have hs := summable_geometric_of_lt_one r0 r1
  rw [← tsum_even_add_odd (by rw [ge]; exact hs.mul_right _) (by rw [go]; exact hs.mul_right _), ge, go,
    tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one r0 r1]
  have h2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have h3 : (1 : ℝ) - r ^ 2 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  rw [hr]
  field_simp

end GlobalTheory.FacUpOdd

namespace GlobalTheory.FacUpOdd

theorem nuFac_le_odd_unram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ¬ IsUnit (p : T.V) → y.IsAlg → p ≠ 2 → ¬ (p : ℤ) ∣ discr E → ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → (SplitInK H p → nuFac p y f k ≤ ((k * (Dw.q / ((p : ℝ) - 1)) : ℝ) : EReal)) ∧ (InertInK H p → nuFac p y f k ≤ ((k * (Dw.q / ((p : ℝ) - 1) + ((Dw.p : ℝ) - Dw.q) * p / ((p : ℝ) ^ 2 - 1)) : ℝ) : EReal)) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y hnu hy hp2 hdisc f k hpsi
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨X⟩ := GlobalTheory.CharDepth.nonempty_valExt T p hnu
  obtain ⟨Ch⟩ := (GlobalTheory.IntChartExists.intChart_exists E H Dw l Xo c).1 (fun _ => rfl) T io y
  obtain ⟨hfot, horb⟩ := GlobalTheory.T.frobenius_orbit_of_unramified_prime E H l c p T io X hdisc
  obtain ⟨τ, i⟩ := f
  obtain ⟨h, hh, -, lab, hl0, hfr, hinj, -⟩ := horb τ
  haveI : NeZero h := ⟨hh.ne'⟩
  subst hl0
  obtain ⟨xs, hxs, hle⟩ := GlobalTheory.CharMinor.colength_bound p (GlobalTheory.ChF.unramified_companion_chart_characters p) hp2 E H Dw l Xo c
    T io y Ch X hy hdisc h lab hinj (fun s x => hfr s x) 0
  have hnu := (GlobalTheory.T.flagStep_characters_of_colength E H Dw l Xo c p T io y Ch X ⟨lab 0, i⟩ xs _ hxs hle).2 k
  have hstep : ∀ n : ℕ, lab ((n + 1 : ℕ) : ZMod h) = lab ((n : ZMod h) + 1) := fun n => by push_cast; rfl
  refine ⟨fun hs => ?_, fun hi => ?_⟩
  · have hall : ∀ n : ℕ, InPsi H (lab (n : ZMod h)) := by
      intro n
      induction n with
      | zero => simpa using hpsi
      | succ n ih => rw [hstep]; exact ((hfot _ _ (hfr _)).1 hs).2 ih
    refine hnu.trans (le_of_eq ?_)
    congr 2
    rw [← tsum_const p hp1]
    refine tsum_congr fun n => ?_
    rw [zero_add, mult_of_not_inPsi Dw ((inPsi_conj_iff H _).1.mt (not_not.2 (hall (n + 1))))]
  · have halt : ∀ n : ℕ, InPsi H (lab (n : ZMod h)) ↔ Even n := by
      intro n
      induction n with
      | zero => simpa using hpsi
      | succ n ih =>
        rw [hstep, ((hfot _ _ (hfr _)).2 hi), inPsi_conj_iff, ih, Nat.even_add_one]
    refine hnu.trans (le_of_eq ?_)
    congr 2
    have e : ∀ n : ℕ, (Dw.mult (ComplexEmbedding.conjugate (lab (0 + ((n + 1 : ℕ) : ZMod h)))) : ℝ) =
        if Even n then (Dw.p : ℝ) else Dw.q := by
      intro n
      rw [zero_add]
      by_cases hn : Even n
      · rw [if_pos hn, mult_of_inPsi Dw ((inPsi_conj_iff H _).2 (fun h' => ?_))]
        have := (halt (n + 1)).1 h'
        rw [Nat.even_add_one] at this
        exact this hn
      · rw [if_neg hn, mult_of_not_inPsi Dw (fun h' => ?_)]
        have := (inPsi_conj_iff H _).1 h'
        rw [halt, Nat.even_add_one, not_not] at this
        exact hn this
    rw [tsum_congr fun n => by rw [e n], tsum_alt p hp1]
    have hp1' : (1 : ℝ) < p := by exact_mod_cast hp1
    have h2 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    have h3 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring

end GlobalTheory.FacUpOdd
