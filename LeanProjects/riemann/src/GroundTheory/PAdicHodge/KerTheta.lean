import Mathlib
import GroundTheory.PAdicHodge.PerfectoidField
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LeSpanSingletonOfForallMemEq
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open WittVector

section Adic

variable {R : Type*} [CommRing R]

theorem smodEq_span_singleton_pow_iff (a x y : R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule R R)] ↔ a ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem le_span_singleton_of_forall_mem_eq {π ξ : R} [IsAdicComplete (Ideal.span {π}) R]
    {J : Ideal R} (h : ∀ x ∈ J, ∃ a z, z ∈ J ∧ x = a * ξ + z * π) :
    J ≤ Ideal.span {ξ} :=
  _root_.UpperTheory.Reformulated.B.Yhc2.le_span_singleton_of_forall_mem_eq h

end Adic

section WittPerfect

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [CommRing A] [CharP A p] [PerfectRing A p]

theorem exists_eq_teichmuller_add_mul_p (x : WittVector p A) :
    ∃ v : WittVector p A, x = teichmuller p (x.coeff 0) + v * p := by
  have : x - teichmuller p (x.coeff 0) ∈ Ideal.span {(p : WittVector p A)} := by
    rw [mem_span_p_iff_coeff_zero_eq_zero]
    have h := add_coeff_zero (x - teichmuller p (x.coeff 0)) (teichmuller p (x.coeff 0))
    rw [sub_add_cancel, teichmuller_coeff_zero] at h
    exact (eq_sub_of_add_eq h.symm).trans (sub_self _)
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨v, by rw [hv]; ring⟩

omit [PerfectRing A p] in

theorem coeff_zero_teichmuller_add_mul_p (c : A) (v : WittVector p A) :
    (teichmuller p c + v * p).coeff 0 = c := by
  rw [add_coeff_zero, teichmuller_coeff_zero, mul_charP_coeff_zero, add_zero]

omit [PerfectRing A p] in

theorem coeff_one_teichmuller_add_mul_p (c : A) (v : WittVector p A) :
    (teichmuller p c + v * p).coeff 1 = v.coeff 0 ^ p := by
  rw [coeff_add_of_disjoint 1 _ _ fun n => ?_, teichmuller_coeff_pos p c 1 one_pos, zero_add,
    mul_charP_coeff_succ]
  rcases n with _ | n
  · exact Or.inr (mul_charP_coeff_zero v)
  · exact Or.inl (teichmuller_coeff_pos p c (n + 1) n.succ_pos)

theorem isUnit_of_isUnit_coeff_zero {v : WittVector p A} (h : IsUnit (v.coeff 0)) : IsUnit v := by
  obtain ⟨u, hu⟩ := h.exists_left_inv
  set t := teichmuller p u * v with ht
  have h0 : t - 1 ∈ Ideal.span {(p : WittVector p A)} := by
    rw [mem_span_p_iff_coeff_zero_eq_zero]
    have h := add_coeff_zero (t - 1) 1
    rw [sub_add_cancel, one_coeff_zero, ht, mul_coeff_zero, teichmuller_coeff_zero, hu] at h
    exact (eq_sub_of_add_eq h.symm).trans (sub_self _)
  have hj := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ h0) 1
  rw [mul_one, sub_add_cancel] at hj
  exact isUnit_of_mul_isUnit_right hj

end WittPerfect

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p

section Integers

variable {p}

theorem isUnit_iff_norm_eq_one {u : 𝒪} : IsUnit u ↔ ‖(u : K)‖ = 1 := by
  constructor
  · rintro ⟨w, rfl⟩
    have h1 : ‖((w : 𝒪) : K)‖ * ‖(((w⁻¹ : 𝒪ˣ) : 𝒪) : K)‖ = 1 := by
      rw [← norm_mul, ← Subring.coe_mul, Units.mul_inv]; simp
    have ha := mem_normInteger.1 (w : 𝒪).2
    have hb := mem_normInteger.1 ((w⁻¹ : 𝒪ˣ) : 𝒪).2
    nlinarith [norm_nonneg ((w : 𝒪) : K), norm_nonneg (((w⁻¹ : 𝒪ˣ) : 𝒪) : K)]
  · intro h
    have h0 : (u : K) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
    refine isUnit_iff_exists_inv.2 ⟨⟨(u : K)⁻¹, mem_normInteger.2 (by rw [norm_inv, h, inv_one])⟩, ?_⟩
    ext
    simp [h0]

omit [Fact p.Prime] [IsPerfectoidField K p] in

theorem norm_le_of_mem_span_p {b : 𝒪} (hb : b ∈ Ideal.span {(p : 𝒪)}) :
    ‖(b : K)‖ ≤ ‖(p : K)‖ := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
  rw [Subring.coe_mul, norm_mul]
  have hc := mem_normInteger.1 c.2
  have : ((p : 𝒪) : K) = (p : K) := by simp
  rw [this]
  calc ‖(c : K)‖ * ‖(p : K)‖ ≤ 1 * ‖(p : K)‖ := by gcongr
    _ = _ := one_mul _

variable (p) in

theorem norm_eq_one_of_mk_eq {b c : 𝒪}
    (h : Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) b = Ideal.Quotient.mk _ c)
    (hc : ‖(c : K)‖ = 1) : ‖(b : K)‖ = 1 := by
  have hbc : ‖(b : K) - c‖ < 1 := by
    have := norm_le_of_mem_span_p (Ideal.Quotient.eq.1 h)
    rw [AddSubgroupClass.coe_sub] at this
    exact this.trans_lt (norm_natCast_lt_one (K := K) (p := p))
  refine le_antisymm (mem_normInteger.1 b.2) ?_
  have h2 : ‖(c : K)‖ ≤ max ‖(c : K) - b‖ ‖(b : K)‖ := by
    simpa using IsUltrametricDist.norm_add_le_max ((c : K) - b) (b : K)
  rw [norm_sub_rev] at h2
  rcases le_max_iff.1 h2 with h3 | h3
  · linarith
  · linarith

omit [Fact p.Prime] [IsPerfectoidField K p] in
variable (p) in

theorem norm_eq_of_mk_eq {b c : 𝒪}
    (h : Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) b = Ideal.Quotient.mk _ c)
    (hc : ‖(p : K)‖ < ‖(c : K)‖) : ‖(b : K)‖ = ‖(c : K)‖ := by
  have hbc : ‖(b : K) - c‖ ≤ ‖(p : K)‖ := by
    have := norm_le_of_mem_span_p (Ideal.Quotient.eq.1 h)
    rwa [AddSubgroupClass.coe_sub] at this
  have h1 : ‖(b : K)‖ ≤ max ‖(b : K) - c‖ ‖(c : K)‖ := by
    simpa using IsUltrametricDist.norm_add_le_max ((b : K) - c) (c : K)
  have h2 : ‖(c : K)‖ ≤ max ‖(c : K) - b‖ ‖(b : K)‖ := by
    simpa using IsUltrametricDist.norm_add_le_max ((c : K) - b) (b : K)
  rw [norm_sub_rev] at h2
  rcases le_max_iff.1 h1 with h3 | h3 <;> rcases le_max_iff.1 h2 with h4 | h4 <;> linarith

end Integers

section Tilt

theorem preTilt_ext {x y : 𝒪♭} (h : ∀ n, PreTilt.coeff n x = PreTilt.coeff n y) : x = y :=
  Perfection.ext h

theorem mk_untilt (x : 𝒪♭) :
    Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) (PreTilt.untilt x) = PreTilt.coeff 0 x :=
  PreTilt.mk_untilt_eq_coeff_zero x

theorem mk_untilt_iterate (x : 𝒪♭) (n : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(p : 𝒪)})
      (PreTilt.untilt ((frobeniusEquiv 𝒪♭ p).symm^[n] x)) = PreTilt.coeff n x := by
  rw [mk_untilt, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add]

theorem untilt_iterate_succ_pow (x : 𝒪♭) (n : ℕ) :
    PreTilt.untilt ((frobeniusEquiv 𝒪♭ p).symm^[n + 1] x) ^ p =
      PreTilt.untilt ((frobeniusEquiv 𝒪♭ p).symm^[n] x) := by
  rw [Function.iterate_succ_apply', ← map_pow, frobeniusEquiv_symm_pow_p]

theorem norm_untilt_iterate_pow (x : 𝒪♭) (n : ℕ) :
    ‖((PreTilt.untilt ((frobeniusEquiv 𝒪♭ p).symm^[n] x) : 𝒪) : K)‖ ^ p ^ n =
      ‖((PreTilt.untilt x : 𝒪) : K)‖ := by
  rw [← norm_pow, ← SubmonoidClass.coe_pow, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow]

theorem untilt_zero : PreTilt.untilt (0 : 𝒪♭) = 0 :=
  Perfection.teichmuller_zero

theorem untilt_eq_zero_iff {x : 𝒪♭} : PreTilt.untilt x = 0 ↔ x = 0 := by
  refine ⟨fun h => preTilt_ext p fun n => ?_, fun h => h ▸ untilt_zero p⟩
  have h1 := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n
  rw [h, pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)] at h1
  rw [← mk_untilt_iterate, h1, map_zero, map_zero]

def ofCompatible (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n) : 𝒪♭ :=
  (⟨fun n => Ideal.Quotient.mk _ (y n), fun n => by rw [← map_pow, hy]⟩ :
    Perfection (ModP 𝒪 p) p)

theorem coeff_ofCompatible (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n) (n : ℕ) :
    PreTilt.coeff n (ofCompatible p y hy) = Ideal.Quotient.mk _ (y n) :=
  rfl

theorem untilt_ofCompatible (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n) :
    PreTilt.untilt (ofCompatible p y hy) = y 0 := by
  have hpow : ∀ n, y n ^ p ^ n = y 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_mul, hy, ih]
  exact Perfection.teichmuller_spec fun n => ⟨y n, rfl, by rw [hpow n]; exact SModEq.refl _⟩

local notation "φ" => RingEquiv.symm (frobeniusEquiv (PreTilt (normInteger K) p) p)

theorem dvd_of_norm_untilt_le {a b : 𝒪♭} (hb : b ≠ 0)
    (h : ‖((PreTilt.untilt a : 𝒪) : K)‖ ≤ ‖((PreTilt.untilt b : 𝒪) : K)‖) : b ∣ a := by
  have hbn : ∀ n, ((PreTilt.untilt (φ^[n] b) : 𝒪) : K) ≠ 0 := by
    intro n h0
    apply hb
    have h0' : PreTilt.untilt (φ^[n] b) = 0 := Subtype.ext h0
    rw [← untilt_eq_zero_iff p, ← PreTilt.untilt_iterate_frobeniusEquiv_symm_pow b n, h0',
      zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
  have hle : ∀ n,
      ‖((PreTilt.untilt (φ^[n] a) : 𝒪) : K)‖ ≤ ‖((PreTilt.untilt (φ^[n] b) : 𝒪) : K)‖ := by
    intro n
    have hpn : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hpn, norm_untilt_iterate_pow,
      norm_untilt_iterate_pow]
    exact h
  let y : ℕ → 𝒪 := fun n =>
    ⟨((PreTilt.untilt (φ^[n] a) : 𝒪) : K) / PreTilt.untilt (φ^[n] b), mem_normInteger.2 (by
      rw [norm_div]; exact div_le_one_of_le₀ (hle n) (norm_nonneg _))⟩
  have hy : ∀ n, y (n + 1) ^ p = y n := by
    intro n
    ext
    simp only [y, SubmonoidClass.coe_pow, div_pow]
    rw [← SubmonoidClass.coe_pow, ← SubmonoidClass.coe_pow, untilt_iterate_succ_pow,
      untilt_iterate_succ_pow]
  refine ⟨ofCompatible p y hy, preTilt_ext p fun n => ?_⟩
  rw [map_mul, coeff_ofCompatible, ← mk_untilt_iterate, ← mk_untilt_iterate, ← map_mul]
  congr 1
  ext
  simp only [y, Subring.coe_mul]
  rw [mul_div_cancel₀ _ (hbn n)]

theorem isUnit_iff_norm_untilt {x : 𝒪♭} : IsUnit x ↔ ‖((PreTilt.untilt x : 𝒪) : K)‖ = 1 := by
  constructor
  · intro h
    exact isUnit_iff_norm_eq_one.1 (h.map PreTilt.untilt)
  · intro h
    have hx : x ≠ 0 := by
      rintro rfl
      rw [untilt_zero, ZeroMemClass.coe_zero, norm_zero] at h
      exact zero_ne_one h
    refine isUnit_of_dvd_one (dvd_of_norm_untilt_le p hx ?_)
    rw [map_one, OneMemClass.coe_one, norm_one, h]

theorem exists_mk_untilt_eq (b : 𝒪) :
    ∃ a : 𝒪♭, Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) (PreTilt.untilt a) =
      Ideal.Quotient.mk _ b := by
  obtain ⟨a, ha⟩ : ∃ a : 𝒪♭, PreTilt.coeff 0 a = Ideal.Quotient.mk _ b :=
    Perfection.coeff_surjective (surjective_frobenius (K := K) p) 0
    (Ideal.Quotient.mk _ b)
  exact ⟨a, by rw [mk_untilt]; exact ha⟩

end Tilt

end IsPerfectoidField

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "𝕎𝒪♭" => WittVector p (PreTilt (normInteger K) p)
local notation "θ" => fontaineTheta (normInteger K) p

section Kernel

theorem fontaineTheta_teichmuller_add_mul_p (c : 𝒪♭) (v : 𝕎𝒪♭) :
    θ (teichmuller p c + v * p) = PreTilt.untilt c + θ v * p := by
  rw [map_add, map_mul, fontaineTheta_teichmuller, map_natCast]

theorem coeff_zero_pow (x : 𝕎𝒪♭) (n : ℕ) : (x ^ n).coeff 0 = x.coeff 0 ^ n := by
  rw [← constantCoeff_apply, map_pow, constantCoeff_apply]

theorem norm_fontaineTheta_eq_one_of_isUnit_coeff_one {ξ v : 𝕎𝒪♭}
    (hv : ξ = teichmuller p (ξ.coeff 0) + v * p) (h1 : IsUnit (ξ.coeff 1)) :
    ‖((θ v : 𝒪) : K)‖ = 1 := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have h := congrArg (fun w : 𝕎𝒪♭ => w.coeff 1) hv
  rw [coeff_one_teichmuller_add_mul_p] at h
  rw [h] at h1
  have hv0 : IsUnit (v.coeff 0) := (isUnit_pow_iff hp0).1 h1
  refine norm_eq_one_of_mk_eq p (c := PreTilt.untilt (v.coeff 0)) ?_
    (isUnit_iff_norm_untilt p |>.1 hv0)
  rw [mk_fontaineTheta, mk_untilt]

theorem untilt_coeff_zero_add_eq_zero {ξ v : 𝕎𝒪♭} (hξ : ξ ∈ RingHom.ker θ)
    (hv : ξ = teichmuller p (ξ.coeff 0) + v * p) :
    PreTilt.untilt (ξ.coeff 0) + θ v * p = 0 := by
  rw [← fontaineTheta_teichmuller_add_mul_p, ← hv]
  exact hξ

theorem norm_untilt_coeff_zero {ξ v : 𝕎𝒪♭} (hξ : ξ ∈ RingHom.ker θ)
    (hv : ξ = teichmuller p (ξ.coeff 0) + v * p) :
    ‖((PreTilt.untilt (ξ.coeff 0) : 𝒪) : K)‖ = ‖((θ v : 𝒪) : K)‖ * ‖(p : K)‖ := by
  have h := congrArg (fun z : 𝒪 => (z : K)) (untilt_coeff_zero_add_eq_zero hξ hv)
  simp only [AddMemClass.coe_add, Subring.coe_mul, ZeroMemClass.coe_zero] at h
  have : ((PreTilt.untilt (ξ.coeff 0) : 𝒪) : K) = -(((θ v : 𝒪) : K) * (((p : 𝒪)) : K)) := by
    linear_combination h
  rw [this, norm_neg, norm_mul]
  simp

theorem ker_fontaineTheta_eq_span {ξ : 𝕎𝒪♭} (hξ : ξ ∈ RingHom.ker θ)
    (h1 : IsUnit (ξ.coeff 1)) : RingHom.ker θ = Ideal.span {ξ} := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨v, hv⟩ := exists_eq_teichmuller_add_mul_p ξ
  have hθv := norm_fontaineTheta_eq_one_of_isUnit_coeff_one hv h1
  have hθξ := untilt_coeff_zero_add_eq_zero hξ hv
  refine le_antisymm ?_ (Ideal.span_le.2 (Set.singleton_subset_iff.2 hξ))
  by_cases hpO : (p : 𝒪) = 0
  ·
    have hξ0 : ξ.coeff 0 = 0 := by
      rw [hpO, mul_zero, add_zero] at hθξ
      exact (untilt_eq_zero_iff p).1 hθξ
    have hv0 : IsUnit (v.coeff 0) := by
      have h := congrArg (fun w : 𝕎𝒪♭ => w.coeff 1) hv
      rw [coeff_one_teichmuller_add_mul_p] at h
      rw [h] at h1
      exact (isUnit_pow_iff hp0).1 h1
    have hvu : IsUnit v := isUnit_of_isUnit_coeff_zero hv0
    rw [hξ0, teichmuller_zero, zero_add] at hv
    intro x hx
    obtain ⟨y, hy⟩ := exists_eq_teichmuller_add_mul_p x
    have hx0 : x.coeff 0 = 0 := by
      have h := untilt_coeff_zero_add_eq_zero hx hy
      rw [hpO, mul_zero, add_zero] at h
      exact (untilt_eq_zero_iff p).1 h
    rw [hx0, teichmuller_zero, zero_add] at hy
    rw [Ideal.mem_span_singleton, hy, hv]
    exact mul_dvd_mul_right hvu.dvd _
  · have hpK : (p : K) ≠ 0 := fun h => hpO (Subtype.ext (by simpa using h))
    have hnξ0 := norm_untilt_coeff_zero hξ hv
    rw [hθv, one_mul] at hnξ0
    have hξ0 : ξ.coeff 0 ≠ 0 := by
      intro h
      rw [h, untilt_zero, ZeroMemClass.coe_zero, norm_zero] at hnξ0
      exact hpK (norm_eq_zero.1 hnξ0.symm)
    refine le_span_singleton_of_forall_mem_eq (π := (p : 𝕎𝒪♭)) fun x hx => ?_
    obtain ⟨y, hy⟩ := exists_eq_teichmuller_add_mul_p x
    have hθx := untilt_coeff_zero_add_eq_zero hx hy
    have hnx0 : ‖((PreTilt.untilt (x.coeff 0) : 𝒪) : K)‖ ≤ ‖(p : K)‖ := by
      rw [norm_untilt_coeff_zero hx hy]
      calc ‖((θ y : 𝒪) : K)‖ * ‖(p : K)‖ ≤ 1 * ‖(p : K)‖ := by
            gcongr; exact mem_normInteger.1 (θ y).2
        _ = _ := one_mul _
    obtain ⟨c, hc⟩ := dvd_of_norm_untilt_le p hξ0 (hnx0.trans hnξ0.ge)
    refine ⟨teichmuller p c, y - teichmuller p c * v, ?_, ?_⟩
    · rw [RingHom.mem_ker]
      have hc' : PreTilt.untilt (x.coeff 0) = PreTilt.untilt (ξ.coeff 0) * PreTilt.untilt c := by
        rw [hc, map_mul]
      have h2 : θ (y - teichmuller p c * v) * p = 0 := by
        rw [map_sub, map_mul, fontaineTheta_teichmuller]
        linear_combination hθx - PreTilt.untilt c * hθξ - hc'
      exact (mul_eq_zero.1 h2).resolve_right hpO
    · have hteich : teichmuller p (x.coeff 0) = teichmuller p c * teichmuller p (ξ.coeff 0) := by
        rw [hc, map_mul, mul_comm]
      linear_combination hy - teichmuller p c * hv + hteich

theorem fontaineTheta_mul_p_sub_teichmuller {ϖ : 𝒪♭} {w : 𝕎𝒪♭}
    (h : PreTilt.untilt ϖ = p * θ w) : w * p - teichmuller p ϖ ∈ RingHom.ker θ := by
  rw [RingHom.mem_ker, map_sub, map_mul, map_natCast, fontaineTheta_teichmuller, h, mul_comm,
    sub_self]

theorem isUnit_coeff_one_mul_p_sub_teichmuller {ϖ : 𝒪♭} {w : 𝕎𝒪♭} (hw : IsUnit (θ w))
    (h : PreTilt.untilt ϖ = p * θ w) : IsUnit ((w * p - teichmuller p ϖ).coeff 1) := by
  obtain ⟨s, hs⟩ := exists_eq_teichmuller_add_mul_p (-1 : 𝕎𝒪♭)
  have hneg : (-1 : 𝕎𝒪♭).coeff 0 = -1 := by
    have h0 := add_coeff_zero (-1 : 𝕎𝒪♭) 1
    rw [neg_add_cancel, one_coeff_zero, zero_coeff] at h0
    linear_combination -h0
  have e : teichmuller p (-ϖ) = teichmuller p ϖ * teichmuller p ((-1 : 𝕎𝒪♭).coeff 0) := by
    rw [hneg, ← map_mul, mul_neg_one]
  have key : w * p - teichmuller p ϖ = teichmuller p (-ϖ) + (w + teichmuller p ϖ * s) * p := by
    linear_combination teichmuller p ϖ * hs - e
  rw [key, coeff_one_teichmuller_add_mul_p]
  refine IsUnit.pow _ ((isUnit_iff_norm_untilt p).2 ?_)
  refine norm_eq_one_of_mk_eq p (c := θ w) ?_ (isUnit_iff_norm_eq_one.1 hw)
  have hmk : Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) (PreTilt.untilt ϖ) = 0 := by
    rw [h, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  rw [mk_untilt, add_coeff_zero, mul_coeff_zero, teichmuller_coeff_zero, map_add, map_mul,
    ← mk_untilt p ϖ, hmk, zero_mul, add_zero, mk_fontaineTheta]

theorem exists_mem_ker_isUnit_coeff_one_of_untilt_eq {ϖ : 𝒪♭} {u : 𝒪} (hu : IsUnit u)
    (h : PreTilt.untilt ϖ = p * u) :
    ∃ ξ ∈ RingHom.ker θ, IsUnit (ξ.coeff 1) := by
  obtain ⟨w, rfl⟩ := surjective_fontaineTheta (K := K) p u
  exact ⟨_, fontaineTheta_mul_p_sub_teichmuller h, isUnit_coeff_one_mul_p_sub_teichmuller hu h⟩

theorem ker_fontaineTheta_eq_span_p_sub_teichmuller {pflat : 𝒪♭}
    (h : PreTilt.untilt pflat = p) :
    RingHom.ker θ = Ideal.span {(p : 𝕎𝒪♭) - teichmuller p pflat} := by
  have h' : PreTilt.untilt pflat = p * θ 1 := by rw [map_one, mul_one, h]
  have := ker_fontaineTheta_eq_span (fontaineTheta_mul_p_sub_teichmuller h')
    (isUnit_coeff_one_mul_p_sub_teichmuller (by rw [map_one]; exact isUnit_one) h')
  rwa [one_mul] at this

theorem ker_fontaineTheta_eq_span_p_sub_teichmuller_ofCompatible (y : ℕ → 𝒪)
    (hy : ∀ n, y (n + 1) ^ p = y n) (h0 : y 0 = p) :
    RingHom.ker θ = Ideal.span {(p : 𝕎𝒪♭) - teichmuller p (ofCompatible p y hy)} :=
  ker_fontaineTheta_eq_span_p_sub_teichmuller (by rw [untilt_ofCompatible, h0])

variable (p) in

theorem exists_norm_untilt_eq {b : 𝒪} (hb : ‖(p : K)‖ < ‖(b : K)‖) :
    ∃ a : 𝒪♭, ‖((PreTilt.untilt a : 𝒪) : K)‖ = ‖(b : K)‖ := by
  obtain ⟨a, ha⟩ := exists_mk_untilt_eq p b
  exact ⟨a, norm_eq_of_mk_eq p ha hb⟩

variable (K p) in

theorem exists_untilt_eq_p_mul_unit :
    ∃ ϖ : 𝒪♭, ∃ u : 𝒪, IsUnit u ∧ PreTilt.untilt ϖ = p * u := by
  by_cases hpO : (p : 𝒪) = 0
  · exact ⟨0, 1, isUnit_one, by rw [untilt_zero, hpO, zero_mul]⟩
  have hpK : (p : K) ≠ 0 := fun h => hpO (Subtype.ext (by simpa using h))
  have hp1 : ‖(p : K)‖ < 1 := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
  have hpos : 0 < ‖(p : K)‖ := norm_pos_iff.2 hpK
  obtain ⟨x, hx1, hx2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) _ hp1
  have hxpos : 0 < ‖x‖ := hpos.trans hx1
  have hx0 : x ≠ 0 := norm_pos_iff.1 hxpos
  have hy : ‖(p : K) / x‖ ≤ 1 := by
    rw [norm_div]; exact div_le_one_of_le₀ hx1.le hxpos.le
  obtain ⟨a₁, ha₁⟩ := exists_norm_untilt_eq (K := K) p (b := ⟨x, mem_normInteger.2 hx2.le⟩) hx1
  obtain ⟨a₂, ha₂⟩ := exists_norm_untilt_eq (K := K) p (b := ⟨(p : K) / x, mem_normInteger.2 hy⟩)
    (by
      show ‖(p : K)‖ < ‖(p : K) / x‖
      rw [norm_div, lt_div_iff₀ hxpos]
      exact mul_lt_of_lt_one_right hpos hx2)
  have hϖ : ‖((PreTilt.untilt (a₁ * a₂) : 𝒪) : K)‖ = ‖(p : K)‖ := by
    rw [map_mul, Subring.coe_mul, norm_mul, ha₁, ha₂]
    show ‖x‖ * ‖(p : K) / x‖ = ‖(p : K)‖
    rw [norm_div, mul_div_cancel₀ _ hxpos.ne']
  have hu : ‖((PreTilt.untilt (a₁ * a₂) : 𝒪) : K) / p‖ = 1 := by
    rw [norm_div, hϖ, div_self hpos.ne']
  refine ⟨a₁ * a₂, ⟨_, mem_normInteger.2 hu.le⟩, isUnit_iff_norm_eq_one.2 hu, ?_⟩
  ext
  simp only [Subring.coe_mul]
  rw [show ((p : 𝒪) : K) = (p : K) by simp, mul_div_cancel₀ _ hpK]

variable (K p) in

theorem exists_mem_ker_fontaineTheta_isUnit_coeff_one :
    ∃ ξ ∈ RingHom.ker θ, IsUnit (ξ.coeff 1) := by
  obtain ⟨ϖ, u, hu, h⟩ := exists_untilt_eq_p_mul_unit K p
  exact exists_mem_ker_isUnit_coeff_one_of_untilt_eq hu h

variable (K p) in

theorem isPrincipal_ker_fontaineTheta : (RingHom.ker θ).IsPrincipal := by
  obtain ⟨ξ, hξ, h1⟩ := exists_mem_ker_fontaineTheta_isUnit_coeff_one K p
  exact ⟨⟨ξ, ker_fontaineTheta_eq_span hξ h1⟩⟩

variable (K p) in

theorem exists_untilt_eq_p [IsAlgClosed K] : ∃ pflat : 𝒪♭, PreTilt.untilt pflat = p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let root : 𝒪 → 𝒪 := fun z =>
    ⟨Classical.choose (IsAlgClosed.exists_pow_nat_eq (z : K) hp), mem_normInteger.2 (by
      have h := Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (z : K) hp)
      have h2 : ‖Classical.choose (IsAlgClosed.exists_pow_nat_eq (z : K) hp)‖ ^ p ≤ 1 := by
        rw [← norm_pow, h]; exact mem_normInteger.1 z.2
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp.ne').1 h2)⟩
  have hroot : ∀ z, root z ^ p = z := fun z => Subtype.ext (by
    simp only [root, SubmonoidClass.coe_pow]
    exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (z : K) hp))
  let y : ℕ → 𝒪 := fun n => root^[n] p
  have hy : ∀ n, y (n + 1) ^ p = y n := fun n => by
    simp only [y, Function.iterate_succ_apply', hroot]
  exact ⟨ofCompatible p y hy, by rw [untilt_ofCompatible]; rfl⟩

variable (K p) in

theorem exists_ker_fontaineTheta_eq_span_p_sub_teichmuller [IsAlgClosed K] :
    ∃ pflat : 𝒪♭, PreTilt.untilt pflat = p ∧
      RingHom.ker θ = Ideal.span {(p : 𝕎𝒪♭) - teichmuller p pflat} := by
  obtain ⟨pflat, h⟩ := exists_untilt_eq_p K p
  exact ⟨pflat, h, ker_fontaineTheta_eq_span_p_sub_teichmuller h⟩

end Kernel

section WittTilt

variable (K p) in

theorem isDomain_wittVector_preTilt : IsDomain 𝕎𝒪♭ :=
  have := isDomain_preTilt (K := K) p
  inferInstance

theorem eq_zero_of_p_mul_eq_zero {x : 𝕎𝒪♭} (h : (p : 𝕎𝒪♭) * x = 0) : x = 0 :=
  WittVector.eq_zero_of_p_mul_eq_zero x (by rwa [mul_comm])

theorem eq_zero_of_teichmuller_mul_eq_zero {ϖ : 𝒪♭} (hϖ : ϖ ≠ 0) {x : 𝕎𝒪♭}
    (h : teichmuller p ϖ * x = 0) : x = 0 := by
  have := isDomain_wittVector_preTilt K p
  refine (mul_eq_zero.1 h).resolve_left fun h0 => hϖ ?_
  rw [← teichmuller_coeff_zero p ϖ, h0, zero_coeff]

theorem mem_nonZeroDivisors_of_isUnit_coeff_one {ξ : 𝕎𝒪♭} (h1 : IsUnit (ξ.coeff 1)) :
    ξ ∈ nonZeroDivisors 𝕎𝒪♭ := by
  have := isDomain_preTilt (K := K) p
  have := isDomain_wittVector_preTilt K p
  refine mem_nonZeroDivisors_of_ne_zero fun h => ?_
  rw [h, zero_coeff] at h1
  exact not_isUnit_zero h1

theorem isHausdorff_span_of_isUnit_coeff_one {ξ : 𝕎𝒪♭} (hξ : ξ ∈ RingHom.ker θ)
    (h1 : IsUnit (ξ.coeff 1)) : IsHausdorff (Ideal.span {ξ}) 𝕎𝒪♭ := by
  have := isDomain_preTilt (K := K) p
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨v, hv⟩ := exists_eq_teichmuller_add_mul_p ξ
  have hθv := norm_fontaineTheta_eq_one_of_isUnit_coeff_one hv h1
  have hθξ := untilt_coeff_zero_add_eq_zero hξ hv
  suffices H : ∀ m (x : 𝕎𝒪♭), (∀ n, ξ ^ n ∣ x) → (p : 𝕎𝒪♭) ^ m ∣ x by
    refine ⟨fun x hx => IsHausdorff.haus (I := Ideal.span {(p : 𝕎𝒪♭)}) inferInstance x
      fun m => ?_⟩
    rw [smodEq_span_singleton_pow_iff, sub_zero]
    exact H m x fun n => by
      have := hx n
      rwa [smodEq_span_singleton_pow_iff, sub_zero] at this
  by_cases hpO : (p : 𝒪) = 0
  · have hξ0 : ξ.coeff 0 = 0 := by
      rw [hpO, mul_zero, add_zero] at hθξ
      exact (untilt_eq_zero_iff p).1 hθξ
    rw [hξ0, teichmuller_zero, zero_add] at hv
    intro m x hx
    obtain ⟨w, hw⟩ := hx m
    exact ⟨v ^ m * w, by rw [hw, hv, mul_pow]; ring⟩
  have hpK : (p : K) ≠ 0 := fun h => hpO (Subtype.ext (by simpa using h))
  have hp1 : ‖(p : K)‖ < 1 := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
  have hnξ0 := norm_untilt_coeff_zero hξ hv
  rw [hθv, one_mul] at hnξ0
  have hξ0 : ξ.coeff 0 ≠ 0 := by
    intro h
    rw [h, untilt_zero, ZeroMemClass.coe_zero, norm_zero] at hnξ0
    exact hpK (norm_eq_zero.1 hnξ0.symm)
  intro m
  induction m with
  | zero => intro x _; simp
  | succ m ih =>
    intro x hx
    have hx0 : x.coeff 0 = 0 := by
      rw [← untilt_eq_zero_iff p]
      have hle : ∀ n, ‖((PreTilt.untilt (x.coeff 0) : 𝒪) : K)‖ ≤ ‖(p : K)‖ ^ n := by
        intro n
        obtain ⟨w, hw⟩ := hx n
        have hw0 : x.coeff 0 = ξ.coeff 0 ^ n * w.coeff 0 := by
          rw [hw, mul_coeff_zero, coeff_zero_pow]
        rw [hw0, map_mul, map_pow, Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow,
          hnξ0]
        calc ‖(p : K)‖ ^ n * ‖((PreTilt.untilt (w.coeff 0) : 𝒪) : K)‖
            ≤ ‖(p : K)‖ ^ n * 1 := by
              gcongr; exact mem_normInteger.1 (PreTilt.untilt (w.coeff 0)).2
          _ = _ := mul_one _
      have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : K)) hp1
      have h0 := ge_of_tendsto' ht hle
      exact Subtype.ext (norm_le_zero_iff.1 h0)
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1
      ((mem_span_p_iff_coeff_zero_eq_zero x).2 hx0)
    have hy' : ∀ n, ξ ^ n ∣ y := by
      intro n
      obtain ⟨w, hw⟩ := hx n
      have hw0 : w.coeff 0 = 0 := by
        have h := congrArg (fun z : 𝕎𝒪♭ => z.coeff 0) (hy.trans hw)
        rw [mul_charP_coeff_zero, mul_coeff_zero, coeff_zero_pow] at h
        exact (mul_eq_zero.1 h.symm).resolve_left (pow_ne_zero _ hξ0)
      obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.1
        ((mem_span_p_iff_coeff_zero_eq_zero w).2 hw0)
      refine ⟨w', sub_eq_zero.1 (eq_zero_of_p_mul_eq_zero ?_)⟩
      rw [mul_sub, mul_comm (p : 𝕎𝒪♭) y, hy, hw, ← hw']
      ring
    obtain ⟨t, ht⟩ := ih y hy'
    exact ⟨t, by rw [← hy, ht]; ring⟩

end WittTilt

end IsPerfectoidField

end GroundTheory.PAdicHodge
