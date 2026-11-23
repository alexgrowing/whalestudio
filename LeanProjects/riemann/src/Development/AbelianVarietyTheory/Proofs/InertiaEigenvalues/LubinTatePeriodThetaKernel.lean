import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK
open GlobalTheory.Prism IsLocalRing
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LTPeriodKerSq

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem intToOC_mem_max {π : ↥(OL K)} (hπ : Irreducible π) : intToOC K π ∈ maximalIdeal (OC l) := by
  obtain ⟨n, hn⟩ := GlobalTheory.AinfK.exists_l_dvd_pow hπ
  have h1 := map_dvd (intToOC K) hn
  rw [map_natCast, map_pow] at h1
  by_contra h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h
  exact (inferInstance : Fact ¬IsUnit ((l : ℕ) : OC l)).out (isUnit_of_dvd_unit h1 (h.pow _))

theorem not_sq_dvd {π : ↥(OL K)} (hπ : Irreducible π) {p : PreTilt (OC l) l} (hp : p.untilt = intToOC K π)
    (r : ℕ) {u v : AK K} (hu : u = inO K π * v + v ^ (r + 2))
    (hs : eta π p ^ 2 ∣ inO K π + u ^ (r + 1)) : False := by
  have hϖm := intToOC_mem_max hπ
  obtain ⟨c, hc⟩ := hs
  have hθ : intToOC K π + thetaK K u ^ (r + 1) = 0 := by
    have := congrArg (thetaK K) hc
    rwa [map_add, map_pow, thetaK_inO, map_mul, map_pow, thetaK_eta hp, zero_pow two_ne_zero, zero_mul] at this
  have hre : red K (eta π p) = p := by
    rw [eta, map_sub, red_teich, red_inO_eq_zero hπ.not_isUnit, sub_zero]
  have hr : red K v ^ ((r + 2) * (r + 1)) = p ^ 2 * red K c := by
    have := congrArg (red K) hc
    rw [map_add, red_inO_eq_zero hπ.not_isUnit, zero_add, map_pow, hu, map_add, map_mul,
      red_inO_eq_zero hπ.not_isUnit, zero_mul, zero_add, map_pow, map_mul, map_pow, hre, ← pow_mul] at this
    exact this
  have ha : (red K v).untilt ^ ((r + 2) * (r + 1)) = intToOC K π ^ 2 * (red K c).untilt := by
    have := congrArg PreTilt.untilt hr
    rwa [map_pow, map_mul, map_pow, hp] at this
  obtain ⟨d, hd⟩ := dvd_thetaK_sub hπ v
  have hz1 : thetaK K u = intToOC K π * thetaK K v + thetaK K v ^ (r + 2) := by
    rw [hu, map_add, map_mul, thetaK_inO, map_pow]
  have hmp : (maximalIdeal (OC l)).IsPrime := inferInstance
  have ham : (red K v).untilt ∈ maximalIdeal (OC l) :=
    hmp.mem_of_pow_mem ((r + 2) * (r + 1)) (by
      rw [ha]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖm 2 two_pos))
  have hz2m : thetaK K v ∈ maximalIdeal (OC l) := by
    rw [show thetaK K v = (red K v).untilt + intToOC K π * d by linear_combination hd]
    exact Ideal.add_mem _ ham (Ideal.mul_mem_right _ _ hϖm)
  have hS : (∑ i ∈ Finset.range (r + 2), thetaK K v ^ i * (red K v).untilt ^ (r + 2 - 1 - i)) ∈
      maximalIdeal (OC l) := Ideal.sum_mem _ fun i _ => by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ham _ (by omega))
    · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hz2m _ hi0)
  have e1 := geom_sum₂_mul (thetaK K v) (red K v).untilt (r + 2)
  have e2 := geom_sum₂_mul (thetaK K u) ((red K v).untilt ^ (r + 2)) (r + 1)
  have ha' : ((red K v).untilt ^ (r + 2)) ^ (r + 1) = intToOC K π ^ 2 * (red K c).untilt := by
    rw [← pow_mul, ha]
  set S := ∑ i ∈ Finset.range (r + 2), thetaK K v ^ i * (red K v).untilt ^ (r + 2 - 1 - i)
  set S' := ∑ i ∈ Finset.range (r + 1), thetaK K u ^ i * ((red K v).untilt ^ (r + 2)) ^ (r + 1 - 1 - i)
  have key : intToOC K π * (1 + intToOC K π * (red K c).untilt + S' * (thetaK K v + S * d)) = 0 := by
    linear_combination hθ + e2 - ha' - S' * hz1 + S' * e1 - S' * S * hd
  have hϖ0 : intToOC K π ≠ 0 := (map_ne_zero_iff _ (GlobalTheory.BKReal.intToOC_injective K)).2 hπ.ne_zero
  have h1 := (mul_eq_zero.1 key).resolve_left hϖ0
  have hmem : (1 : OC l) ∈ maximalIdeal (OC l) := by
    rw [show (1 : OC l) = -(intToOC K π * (red K c).untilt + S' * (thetaK K v + S * d)) by
      linear_combination h1]
    exact neg_mem (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hϖm)
      (Ideal.mul_mem_left _ _ (Ideal.add_mem _ hz2m (Ideal.mul_mem_right _ _ hS))))
  exact (maximalIdeal.isMaximal (OC l)).ne_top ((Ideal.eq_top_iff_one _).2 hmem)

theorem eq_zero_of_red {π : ↥(OL K)} (hπ : Irreducible π) (r : ℕ) {ω : AK K}
    (hF : frobq K ω = inO K π * ω + ω ^ (r + 2)) (h0 : red K ω = 0) : ω = 0 := by
  have := complete_pi hπ
  have hπ0 : inO K π ≠ 0 := fun h => one_ne_zero (eq_zero_of_mul_pi hπ 1 (by rw [h, mul_zero]))
  have key : ∀ n : ℕ, inO K π ^ (n + 1) ∣ ω := fun n => by
    induction n with
    | zero =>
      rw [zero_add, pow_one, ← Ideal.mem_span_singleton, ← ker_red hπ]
      exact h0
    | succ n ih =>
      obtain ⟨y, rfl⟩ := ih
      obtain ⟨x, hx⟩ := (frobq_bijective K).2 (y + inO K π ^ (n * r + n + r) * y ^ (r + 2))
      rw [map_mul, map_pow, frobq_inO] at hF
      have h1 : frobq K y = frobq K (inO K π * x) := by
        refine mul_left_cancel₀ (pow_ne_zero (n + 1) hπ0) ?_
        rw [hF, map_mul, frobq_inO, hx]
        ring
      exact ⟨x, by rw [(frobq_bijective K).1 h1]; ring⟩
  exact GlobalTheory.Per.AinfComplete.eq_zero_of_haus (inO K π) ω fun n =>
    Ideal.mem_span_singleton.2 ((pow_dvd_pow _ n.le_succ).trans (key n))

open GlobalTheory.Per.AinfComplete in

theorem not_mem_sq {π : ↥(OL K)} (hπ : Irreducible π) {ω : AK K} (hω0 : ω ≠ 0) (hθ : thetaK K ω = 0)
    (hF : frobq K ω = inO K π * ω + ω ^ resCard K) : ω ∉ RingHom.ker (thetaK K) ^ 2 := by
  intro hω2
  obtain ⟨p, hp⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (intToOC K π)
  have hker := ker_thetaK hπ hp
  have hq : 2 ≤ resCard K :=
    hl.out.two_le.trans (Nat.le_self_pow (card_res' K).1 l)
  obtain ⟨r, hr⟩ : ∃ r, resCard K = r + 2 := ⟨resCard K - 2, by omega⟩
  have hr' : l ^ fK K = r + 2 := hr
  rw [hr] at hF
  have hdiv : ∀ x, thetaK K x = 0 ↔ eta π p ∣ x := fun x => by
    rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton]
  have hη0 : eta π p ≠ 0 := fun h => hω0 (zero_dvd_iff.1 (h ▸ (hdiv ω).1 hθ))
  have hηp : Prime (eta π p) := by
    rw [← Ideal.span_singleton_prime hη0, ← hker]
    exact RingHom.ker_isPrime _
  have hϖ0 : intToOC K π ≠ 0 := (map_ne_zero_iff _ (GlobalTheory.BKReal.intToOC_injective K)).2 hπ.ne_zero
  rw [hker, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hω2
  obtain ⟨G, hG⟩ := (frobq_bijective K).2.hasRightInverse
  let w : ℕ → AK K := fun n => G^[n] ω
  have hw : ∀ n, frobq K (w (n + 1)) = w n := fun n => by
    simp only [w, Function.iterate_succ_apply']
    exact hG _
  have hFw : ∀ n, frobq K (w n) = inO K π * w n + w n ^ (r + 2) := fun n => by
    induction n with
    | zero => exact hF
    | succ n ih =>
      refine (frobq_bijective K).1 ?_
      rw [map_add, map_mul, map_pow, frobq_inO, hw, ih]
  have hrec : ∀ n, w n = inO K π * w (n + 1) + w (n + 1) ^ (r + 2) := fun n => by rw [← hFw, hw]
  have hall : ∀ n, eta π p ^ 2 ∣ w n := fun n => by
    induction n with
    | zero => exact hω2
    | succ n ih =>
      rw [hrec n] at ih
      by_cases hu : eta π p ∣ w (n + 1)
      · obtain ⟨a, ha⟩ := hu
        rw [ha, show inO K π * (eta π p * a) + (eta π p * a) ^ (r + 2) =
          eta π p * (inO K π * a + eta π p * (eta π p ^ r * a ^ (r + 2))) by ring, sq,
          mul_dvd_mul_iff_left hη0, dvd_add_left (dvd_mul_right _ _)] at ih
        rcases hηp.dvd_or_dvd ih with h | h
        · exact absurd (thetaK_inO π ▸ (hdiv _).2 h) hϖ0
        · rw [ha, sq]
          exact mul_dvd_mul_left _ h
      · rw [show inO K π * w (n + 1) + w (n + 1) ^ (r + 2) =
          w (n + 1) * (inO K π + w (n + 1) ^ (r + 1)) by ring] at ih
        exact (not_sq_dvd hπ hp r (hrec (n + 1)) (hηp.pow_dvd_of_dvd_mul_left 2 hu ih)).elim
  have hre : red K (eta π p) = p := by
    rw [eta, map_sub, red_teich, red_inO_eq_zero hπ.not_isUnit, sub_zero]
  have hred : ∀ n, red K ω = red K (w n) ^ (r + 2) ^ n := fun n => by
    induction n with
    | zero => simp [w]
    | succ n ih => rw [ih, ← hw n, red_frobq, hr', ← pow_mul, ← pow_succ']
  have hpu : ¬ IsUnit p := fun h => intToOC_mem_max hπ (hp ▸ h.map PreTilt.untilt)
  have h1 : IsNilpotent (Perfection.coeff (ModP (OC l) l) l 0 p) :=
    nilpotent_of_not_isUnit l _ fun h => hpu (perfection_isUnit _ h)
  refine hω0 (eq_zero_of_red hπ r hF (perfection_haus (p := l) (R := ModP (OC l) l) h1 (red K ω) fun n => ?_))
  have h2 : p ∣ red K (w n) := by
    rw [← hre]
    exact map_dvd _ ((dvd_pow_self _ two_ne_zero).trans (hall n))
  have h3 : p ^ n ∣ red K ω := by
    rw [hred n]
    exact (pow_dvd_pow p (Nat.lt_pow_self (by omega)).le).trans (pow_dvd_pow_of_dvd h2 _)
  exact h3

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∀ ω : AK K, ω ≠ 0 → thetaK K ω = 0 → frobq K ω = inO K π * ω + ω ^ resCard K →
      (∀ (g : ↥(GK K)) (a : ↥(OL K)) (φ : PowerSeries ↥(OL K)), (a : ↥K.1) = (χ g : ↥K.1) → IsLTEndo K π a φ →
        ∀ n : ℕ, gal K g ω - ∑ j ∈ Finset.range n, inO K (PowerSeries.coeff j φ) * ω ^ j ∈ RingHom.ker (thetaK K) ^ n) →
      ω ∉ RingHom.ker (thetaK K) ^ 2 := by
  intro l _ K χ π z hLT ω hω0 hθ hF _
  exact not_mem_sq hLT.1 hω0 hθ hF

end GlobalTheory.LTPeriodKerSq
