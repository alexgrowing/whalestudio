import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelope
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.BKGal
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.EpsCoeff

variable {l : ℕ} [hl : Fact l.Prime]

abbrev rt (ε : OCb l) (n : ℕ) : OCb l := ((frobeniusEquiv (OCb l) l).symm)^[n] ε

theorem rt_pow (ε : OCb l) (n k : ℕ) : rt ε (n + k) ^ (l ^ k) = rt ε n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← ih, ← Nat.add_assoc, pow_succ', pow_mul]
    congr 1
    rw [rt, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]

theorem frob_iter_teich (x : OCb l) (m : ℕ) :
    (⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[m] (WittVector.teichmuller l x) =
      WittVector.teichmuller l (x ^ (l ^ m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, WittVector.frobenius_eq_map_frobenius,
      WittVector.map_teichmuller, frobenius_def, ← pow_mul, ← pow_succ]

def xin (ε : OCb l) (n : ℕ) : Ainf l :=
  ∑ i ∈ Finset.range l, (WittVector.teichmuller l (rt ε (n + 1))) ^ i

theorem frob_iter_xin (ε : OCb l) (n k : ℕ) :
    (⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n + k] (xin ε n) =
      ∑ i ∈ Finset.range l, (WittVector.teichmuller l (rt ε 1 ^ (l ^ k))) ^ i := by
  rw [xin, ← RingHom.coe_pow, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, RingHom.coe_pow, frob_iter_teich, pow_add, pow_mul, add_comm n 1, rt_pow]

theorem xi_eq (ε : OCb l) (n : ℕ) :
    GlobalTheory.MemLoc.xi ε = (⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n] (xin ε n) := by
  have h := frob_iter_xin ε n 0
  rw [Nat.add_zero] at h
  rw [h]
  simp [GlobalTheory.MemLoc.xi, rt]

theorem natCast_ne_zero : ((l : ℕ) : Per.OC l) ≠ 0 := by
  intro h
  apply GlobalTheory.RingBasics.p_ne_zero (p := l)
  have := congrArg Subtype.val h
  simpa using this

theorem theta_frob_xin (ε : OCb l) (hε : ε.untilt = 1) (n j : ℕ) :
    Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n + (j + 1)] (xin ε n)) = l := by
  rw [frob_iter_xin, map_sum]
  have h1 : (rt ε 1 ^ (l ^ (j + 1))).untilt = 1 := by
    rw [pow_succ', pow_mul]
    have : rt ε 1 ^ l = ε := by
      have h := rt_pow ε 0 1
      rw [zero_add, pow_one] at h
      exact h
    rw [this, map_pow, hε, one_pow]
  rw [Finset.sum_congr rfl (fun i _ => by rw [map_pow, WittVector.fontaineTheta_teichmuller, h1, one_pow])]
  simp

theorem xin_dvd (ε : OCb l) (hε : GlobalTheory.MemLoc.IsEps ε) (n : ℕ) (b : Ainf l)
    (hb : Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n] b) = 0) : xin ε n ∣ b := by
  obtain ⟨y, hy⟩ := (GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd l ε hε _).1 hb
  have hbij := (WittVector.frobenius_bijective l (OCb l)).iterate n
  obtain ⟨y', rfl⟩ := hbij.2 y
  refine ⟨y', hbij.1 ?_⟩
  rw [hy, ← RingHom.coe_pow, map_mul, RingHom.coe_pow, xi_eq ε n]

theorem coeff_xin (ε : OCb l) (n : ℕ) :
    (xin ε n).coeff 0 * (rt ε (n + 1) - 1) = rt ε n - 1 := by
  rw [← WittVector.constantCoeff_apply, xin, map_sum]
  simp only [map_pow, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  rw [geom_sum_mul]
  have := rt_pow ε n 1
  rw [pow_one] at this
  rw [this]

theorem step (ε : OCb l) (hε : GlobalTheory.MemLoc.IsEps ε) (a : Ainf l)
    (ha : ∀ n : ℕ, Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n] a) = 0) (n : ℕ) :
    ∃ b c : Ainf l, a = c * b ∧
      (∀ m, n ≤ m → Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[m] c) ≠ 0) ∧
      c.coeff 0 * (rt ε n - 1) = ε - 1 := by
  induction n with
  | zero =>
    refine ⟨a, 1, (one_mul a).symm, fun m _ => ?_, ?_⟩
    · rw [← RingHom.coe_pow, map_one, map_one]; exact one_ne_zero
    · simp [rt]
  | succ n ih =>
    obtain ⟨b, c, rfl, hc, h0⟩ := ih
    have hb : ∀ m, n ≤ m → Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[m] b) = 0 :=
      fun m hm => by
        have := ha m
        rw [← RingHom.coe_pow, map_mul, map_mul, RingHom.coe_pow] at this
        exact (mul_eq_zero.1 this).resolve_left (hc m hm)
    obtain ⟨b', rfl⟩ := xin_dvd ε hε n b (hb n le_rfl)
    refine ⟨b', c * xin ε n, by ring, fun m hm => ?_, ?_⟩
    · rw [← RingHom.coe_pow, map_mul, map_mul, RingHom.coe_pow]
      refine mul_ne_zero (hc m (by omega)) ?_
      obtain ⟨j, rfl⟩ : ∃ j, m = n + (j + 1) := ⟨m - n - 1, by omega⟩
      rw [theta_frob_xin ε hε.1]
      exact natCast_ne_zero
    · rw [WittVector.mul_coeff_zero, mul_assoc, coeff_xin, h0]

theorem memLoc_isEps {ε : OCb l} (h : IsEps ε) : GlobalTheory.MemLoc.IsEps ε := by
  obtain ⟨h1, δ, hδ, hne⟩ := h
  have : (frobeniusEquiv (OCb l) l).symm ε = δ :=
    (RingEquiv.symm_apply_eq _).2 (by rw [frobeniusEquiv_def, hδ])
  exact ⟨h1, by rw [this]; exact hne⟩

theorem norm_untilt_mul (x y : OCb l) :
    ‖(((x * y).untilt : OC l) : ℂ_[l])‖ =
      ‖((x.untilt : OC l) : ℂ_[l])‖ * ‖((y.untilt : OC l) : ℂ_[l])‖ := by
  rw [map_mul, MulMemClass.coe_mul, norm_mul]

theorem norm_untilt_le_one (x : OCb l) : ‖((x.untilt : OC l) : ℂ_[l])‖ ≤ 1 :=
  (GlobalTheory.RingBasics.mem_OC _).1 x.untilt.2

theorem norm_rt_pow (x : OCb l) (n : ℕ) :
    ‖(((rt x n).untilt : OC l) : ℂ_[l])‖ ^ (l ^ n) = ‖((x.untilt : OC l) : ℂ_[l])‖ := by
  have h := rt_pow x 0 n
  rw [zero_add] at h
  rw [← norm_pow, ← SubmonoidClass.coe_pow, ← map_pow, h]
  rfl

theorem norm_le_of_dvd (a b : OCb l) (hb : b ≠ 0) (h : ∀ n, b ∣ a * rt b n) :
    ‖((a.untilt : OC l) : ℂ_[l])‖ ≤ ‖((b.untilt : OC l) : ℂ_[l])‖ := by
  set A := ‖((a.untilt : OC l) : ℂ_[l])‖ with hAdef
  set B := ‖((b.untilt : OC l) : ℂ_[l])‖ with hBdef
  have hB : 0 < B := by
    refine norm_pos_iff.2 fun h0 => GlobalTheory.FrobInt.sharpRoot_ne_zero b hb 0 ?_
    exact_mod_cast h0
  by_contra hlt
  push_neg at hlt
  have hA : 0 < A := hB.trans hlt
  have key : ∀ n : ℕ, A ^ (l ^ n) * B ≤ B ^ (l ^ n) := by
    intro n
    obtain ⟨c, hc⟩ := h n
    have h1 := congrArg (fun x : OCb l => ‖((x.untilt : OC l) : ℂ_[l])‖ ^ (l ^ n)) hc
    simp only [norm_untilt_mul, mul_pow, norm_rt_pow] at h1
    have hc1 : ‖((c.untilt : OC l) : ℂ_[l])‖ ^ (l ^ n) ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_untilt_le_one c)
    calc A ^ (l ^ n) * B = B ^ (l ^ n) * ‖((c.untilt : OC l) : ℂ_[l])‖ ^ (l ^ n) := h1
      _ ≤ B ^ (l ^ n) := mul_le_of_le_one_right (by positivity) hc1
  have hr : B / A < 1 := (div_lt_one hA).2 hlt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hB hr
  have h2 : (B / A) ^ (l ^ n) ≤ (B / A) ^ n :=
    pow_le_pow_of_le_one (by positivity) hr.le (Nat.lt_pow_self hl.out.one_lt).le
  have h3 : B ≤ (B / A) ^ (l ^ n) := by
    rw [div_pow, le_div_iff₀ (by positivity), mul_comm]
    exact key n
  linarith

theorem dvd_of_norm_le (x y : OC l) (hx : x ≠ 0) (h : ‖(y : ℂ_[l])‖ ≤ ‖(x : ℂ_[l])‖) : x ∣ y := by
  have hx' : (x : ℂ_[l]) ≠ 0 := fun h0 => hx (by exact_mod_cast h0)
  refine ⟨⟨(y : ℂ_[l]) / x, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div, div_le_one (norm_pos_iff.2 hx')]
    exact h
  · show (y : ℂ_[l]) = (x : ℂ_[l]) * ((y : ℂ_[l]) / x)
    field_simp

theorem dvd_of_forall_dvd_mul_rt (a b : OCb l) (hb : b ≠ 0) (h : ∀ n, b ∣ a * rt b n) : b ∣ a := by
  refine GlobalTheory.FrobInt.dvd_of_sharpRoot_dvd b a (GlobalTheory.FrobInt.sharpRoot_ne_zero b hb) fun k => ?_
  refine dvd_of_norm_le _ _ (GlobalTheory.FrobInt.sharpRoot_ne_zero b hb k) ?_
  have hbk : rt b k ≠ 0 := by
    intro h0
    apply hb
    apply (frobeniusEquiv (OCb l) l).symm.injective.iterate k
    rw [iterate_map_zero]
    exact h0
  refine norm_le_of_dvd (rt a k) (rt b k) hbk fun n => ?_
  obtain ⟨c, hc⟩ := h n
  refine ⟨rt c k, ?_⟩
  have := congrArg (((frobeniusEquiv (OCb l) l).symm)^[k]) hc
  rw [iterate_map_mul, iterate_map_mul] at this
  have hcomm : rt (rt b k) n = rt (rt b n) k := by
    simp only [rt, ← Function.iterate_add_apply, add_comm]
  rw [hcomm]
  exact this

end GlobalTheory.EpsCoeff

namespace GlobalTheory

open GlobalTheory.EpsCoeff in

theorem eps_sub_one_dvd_coeff_zero : ∀ (l : ℕ) [Fact l.Prime] (ε : OCb l), IsEps ε → ∀ a : Ainf l,
    (∀ n : ℕ, Per.θ l (WittVector.frobenius^[n] a) = 0) → (ε - 1) ∣ a.coeff 0 := by
  intro l _ ε hε a ha
  have hε' := memLoc_isEps hε
  have hne : ε - 1 ≠ 0 := by
    intro h0
    rw [sub_eq_zero] at h0
    apply hε'.2
    rw [h0, map_one, map_one]
  refine dvd_of_forall_dvd_mul_rt _ _ hne fun n => ?_
  obtain ⟨b, c, rfl, -, h0⟩ := step ε hε' a ha n
  refine ⟨b.coeff 0, ?_⟩
  have hr : rt (ε - 1) n = rt ε n - 1 := by simp only [rt, iterate_map_sub, iterate_map_one]
  rw [hr, WittVector.mul_coeff_zero, ← h0]
  ring

end GlobalTheory
