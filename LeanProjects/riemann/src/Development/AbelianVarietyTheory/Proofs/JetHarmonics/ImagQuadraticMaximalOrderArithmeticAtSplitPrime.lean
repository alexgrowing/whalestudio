import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.OKArith

lemma sq_two_w (d : ℕ) : (2 * wK d - 1) ^ 2 = -(d : ℂ) := by
  have h : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]; simp
  have : 2 * wK d - 1 = Complex.I * ((Real.sqrt d : ℝ) : ℂ) := by unfold wK; ring
  rw [this, mul_pow, h, Complex.I_sq]; ring

lemma w_sq {d k : ℕ} (hk : 4 * k = d + 1) : wK d ^ 2 = wK d - k := by
  have h := sq_two_w d
  have hk' : (4 : ℂ) * k = d + 1 := by exact_mod_cast hk
  linear_combination (1/4 : ℂ) * h + (1/4 : ℂ) * hk'

lemma conj_w (d : ℕ) : conj (wK d) = 1 - wK d := by
  unfold wK
  simp only [map_div₀, map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

lemma conj_el (d : ℕ) (u v : ℤ) : conj ((u : ℂ) + (v : ℂ) * wK d) = u + v * (1 - wK d) := by
  simp [conj_w]

lemma im_w (d : ℕ) : (wK d).im = Real.sqrt d / 2 := by
  unfold wK; simp

lemma coord_unique {d : ℕ} (hd : 0 < d) {u v u' v' : ℤ}
    (h : (u : ℂ) + (v : ℂ) * wK d = u' + v' * wK d) : u = u' ∧ v = v' := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have h1 := congrArg Complex.im h
  simp [im_w, hs.ne'] at h1
  have hv : v = v' := h1
  subst hv
  have : (u : ℂ) = u' := by linear_combination h
  exact ⟨by exact_mod_cast this, rfl⟩

lemma in_mul {d k : ℕ} (hk : 4 * k = d + 1) {α β : ℂ} (ha : InOK d α) (hb : InOK d β) :
    InOK d (α * β) := by
  obtain ⟨u, v, rfl⟩ := ha
  obtain ⟨u', v', rfl⟩ := hb
  refine ⟨u * u' - v * v' * k, u * v' + v * u' + v * v', ?_⟩
  push_cast
  linear_combination (v * v' : ℂ) * w_sq hk

lemma in_conj {d : ℕ} {α : ℂ} (ha : InOK d α) : InOK d (conj α) := by
  obtain ⟨u, v, rfl⟩ := ha
  refine ⟨u + v, -v, ?_⟩
  rw [conj_el]; push_cast; ring

variable {q : ℕ} [hq : Fact q.Prime]

noncomputable def zcHom (q : ℕ) [Fact q.Prime] : ℤ_[q] →+* ℂ_[q] :=
  (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

lemma zc_eq (a : ℤ_[q]) : zc a = zcHom q a := rfl

lemma norm_zc (a : ℤ_[q]) : ‖zcHom q a‖ = ‖a‖ := by
  change ‖algebraMap ℚ_[q] ℂ_[q] (a : ℚ_[q])‖ = _
  rw [norm_algebraMap']; rfl

lemma not_dvd {d : ℕ} (hs : Split d q) : ¬ q ∣ d := by
  rcases hs with ⟨rfl, h⟩ | ⟨_, h⟩
  · omega
  · intro hd
    have : jacobiSym (-(d : ℤ)) q = 0 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_zero_iff]
      simp [(ZMod.natCast_eq_zero_iff d q).2 hd]
    omega

lemma exists_root_mod {d k : ℕ} (hk : 4 * k = d + 1) (hs : Split d q) :
    ∃ a : ℤ, (q : ℤ) ∣ a ^ 2 - a + k := by
  rcases hs with ⟨rfl, h⟩ | ⟨h2, h⟩
  · exact ⟨0, by simp; omega⟩
  · rw [← jacobiSym.legendreSym.to_jacobiSym] at h
    have h0 : (((-(d : ℤ) : ℤ)) : ZMod q) ≠ 0 := by
      intro h0
      rw [(legendreSym.eq_zero_iff q _).2 h0] at h; omega
    obtain ⟨b, hb⟩ := (legendreSym.eq_one_iff q h0).1 h
    have h2' : (2 : ZMod q) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact h2 ((Nat.prime_dvd_prime_iff_eq hq.out Nat.prime_two).1 this)
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective ((b + 1) / 2)
    refine ⟨a, ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hb ⊢
    have hk' : (4 : ZMod q) * k = d + 1 := by exact_mod_cast congrArg (Nat.cast : ℕ → ZMod q) hk
    have ha' : 2 * (a : ZMod q) = b + 1 := by rw [ha]; field_simp
    have : (2 : ZMod q) ^ 2 * ((a : ZMod q) ^ 2 - a + k) = 0 := by
      linear_combination (2 * a + b - 1) * ha' + hk' - hb
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ h2')

lemma norm_d {d : ℕ} (hs : Split d q) : ‖(d : ℤ_[q])‖ = 1 := by
  have h := not_dvd hs
  have h1 : ¬ ‖((d : ℤ) : ℤ_[q])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd]; exact_mod_cast h
  push_cast at h1
  exact le_antisymm (PadicInt.norm_le_one _) (not_lt.1 h1)

lemma exists_root {d k : ℕ} (hk : 4 * k = d + 1) (hs : Split d q) :
    ∃ z : ℤ_[q], z ^ 2 - z + k = 0 := by
  obtain ⟨a, ha⟩ := exists_root_mod hk hs
  have hnd := not_dvd hs
  have h1 : ‖((a ^ 2 - a + k : ℤ) : ℤ_[q])‖ < 1 := (PadicInt.norm_int_lt_one_iff_dvd _).2 ha
  have h2 : ¬ ‖((2 * a - 1 : ℤ) : ℤ_[q])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    intro h
    apply hnd
    have hk' : (4 : ℤ) * k = d + 1 := by exact_mod_cast hk
    have : (d : ℤ) = 4 * (a ^ 2 - a + k) - (2 * a - 1) * (2 * a - 1) := by linear_combination -hk'
    have h3 : (q : ℤ) ∣ d := by
      rw [this]; exact dvd_sub (Dvd.dvd.mul_left ha _) (Dvd.dvd.mul_left h _)
    exact_mod_cast h3
  have h3 : ‖((2 * a - 1 : ℤ) : ℤ_[q])‖ = 1 := le_antisymm (PadicInt.norm_le_one _) (not_lt.1 h2)
  let F : Polynomial ℤ_[q] := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k : ℤ_[q])
  have hF : ‖F.aeval (a : ℤ_[q])‖ < ‖F.derivative.aeval (a : ℤ_[q])‖ ^ 2 := by
    have e1 : F.aeval (a : ℤ_[q]) = ((a ^ 2 - a + k : ℤ) : ℤ_[q]) := by simp [F]
    have e2 : F.derivative.aeval (a : ℤ_[q]) = ((2 * a - 1 : ℤ) : ℤ_[q]) := by
      simp [F]; left; norm_num
    rw [e1, e2, h3]; simpa using h1
  obtain ⟨z, hz, -⟩ := hensels_lemma hF
  exact ⟨z, by simpa [F] using hz⟩

lemma exists_r {d k : ℕ} (hk : 4 * k = d + 1) (hs : Split d q) (ι : ℂ ≃+* ℂ_[q]) :
    ∃ r : ℤ_[q], ι (wK d) = zcHom q r ∧ IsUnit (2 * r - 1) := by
  obtain ⟨z, hz⟩ := exists_root hk hs
  have hk' : (4 : ℤ_[q]) * k = d + 1 := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[q]) hk
  have hu : IsUnit (2 * z - 1) := by
    have : (2 * z - 1) ^ 2 = -(d : ℤ_[q]) := by linear_combination 4 * hz - hk'
    have h2 : IsUnit ((2 * z - 1) ^ 2) := by
      rw [this, PadicInt.isUnit_iff, norm_neg, norm_d hs]
    exact (isUnit_pow_iff two_ne_zero).1 h2
  have h1 := congrArg ι (w_sq hk)
  have h2 := congrArg (zcHom q) hz
  simp only [map_pow, map_sub, map_add, map_natCast, map_zero] at h1 h2
  have : (ι (wK d) - zcHom q z) * (ι (wK d) - (1 - zcHom q z)) = 0 := by
    linear_combination h1 - h2
  rcases mul_eq_zero.1 this with h | h
  · exact ⟨z, sub_eq_zero.1 h, hu⟩
  · refine ⟨1 - z, by rw [sub_eq_zero.1 h]; simp, ?_⟩
    have : 2 * (1 - z) - 1 = -(2 * z - 1) := by ring
    rw [this]; exact hu.neg

lemma exists_approx {r : ℤ_[q]} (hr : IsUnit (2 * r - 1)) (A B : ℤ_[q]) (m : ℕ) :
    ∃ u v : ℤ, (q : ℤ_[q]) ^ m ∣ (u + v * r - A) ∧ (q : ℤ_[q]) ^ m ∣ (u + v * (1 - r) - B) := by
  obtain ⟨t, ht⟩ := hr.exists_right_inv
  have hV := PadicInt.appr_spec m ((A - B) * t)
  have hU := PadicInt.appr_spec m (A - (A - B) * t * r)
  rw [Ideal.mem_span_singleton] at hU hV
  obtain ⟨x, hx⟩ := hU
  obtain ⟨y, hy⟩ := hV
  refine ⟨((A - (A - B) * t * r).appr m : ℕ), (((A - B) * t).appr m : ℕ), ⟨-x - y * r, ?_⟩,
    ⟨-x - y * (1 - r), ?_⟩⟩
  · push_cast
    linear_combination -hx - r * hy
  · push_cast
    linear_combination -hx - (1 - r) * hy - (A - B) * ht

lemma norm_le_iff (a : ℤ_[q]) (n : ℕ) :
    ‖zcHom q a‖ ≤ (q : ℝ) ^ (-(n : ℤ)) ↔ (q : ℤ_[q]) ^ n ∣ a := by
  rw [norm_zc, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

lemma int_dvd {n : ℕ} {a : ℤ} (h : (q : ℤ_[q]) ^ n ∣ (a : ℤ_[q])) : (q : ℤ) ^ n ∣ a := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow,
    PadicInt.norm_int_le_pow_iff_dvd] at h
  exact_mod_cast h

end GlobalTheory.MomOne.OKArith

open GlobalTheory.MomOne.OKArith in

theorem GlobalTheory.MomOne.okArith : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → (InOK d 1 ∧ InOK d (wK d) ∧ ∀ α β, InOK d α → InOK d β → InOK d (α + β) ∧ InOK d (α * β) ∧ InOK d (-α) ∧ InOK d (conj α)) ∧ (∀ α, InOK d α → (∃ a : ℤ_[q], ι α = zc a) ∧ (∃ N : ℕ, (N : ℂ) = α * conj α) ∧ α ∈ algebraicClosure ℚ ℂ) ∧ (∀ (α : ℂ) (n : ℕ), InOK d α → ‖ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → ‖ι (conj α)‖ ≤ (q : ℝ) ^ (-(n : ℤ)) → InOK d (α / (q : ℂ) ^ n)) ∧ (∀ m s : ℕ, Nat.Coprime s q → ∃ e, InOK d e ∧ ‖ι ((s : ℂ) * e) - 1‖ ≤ (q : ℝ) ^ (-(m : ℤ)) ∧ ‖ι (conj e)‖ ≤ (q : ℝ) ^ (-(m : ℤ))) ∧ (∀ n : ℕ, ∃ α, InOK d α ∧ ‖ι α‖ ≤ (q : ℝ) ^ (-(n : ℤ)) ∧ ¬ InOK d (α / 2)) ∧ (∀ x y, InOK d x → InOK d y → ∃ k : ℤ, (h1 d x y).im = k) ∧ ¬ q ∣ d := by
  intro d q hq ι hd h16 hs
  obtain ⟨k, hk⟩ : ∃ k, 4 * k = d + 1 := ⟨(d + 1) / 4, by omega⟩
  obtain ⟨r, hr, hu⟩ := exists_r hk hs ι
  have e1 : ∀ u v : ℤ, ι ((u : ℂ) + v * wK d) = zcHom q (u + v * r) := by
    intro u v; simp [hr]
  have e2 : ∀ u v : ℤ, ι (conj ((u : ℂ) + v * wK d)) = zcHom q (u + v * (1 - r)) := by
    intro u v; rw [conj_el]; simp [hr]
  refine ⟨⟨⟨1, 0, by simp⟩, ⟨0, 1, by simp⟩, fun α β ha hb => ⟨?_, in_mul hk ha hb, ?_, in_conj ha⟩⟩,
    ?_, ?_, ?_, ?_, ?_, not_dvd hs⟩
  · obtain ⟨u, v, rfl⟩ := ha
    obtain ⟨u', v', rfl⟩ := hb
    exact ⟨u + u', v + v', by push_cast; ring⟩
  · obtain ⟨u, v, rfl⟩ := ha
    exact ⟨-u, -v, by push_cast; ring⟩
  · rintro α ⟨u, v, rfl⟩
    refine ⟨⟨_, e1 u v⟩, ?_, ?_⟩
    · have hk1 : (1 : ℤ) ≤ k := by omega
      have hpos : 0 ≤ u ^ 2 + u * v + k * v ^ 2 := by nlinarith [sq_nonneg (2 * u + v), sq_nonneg v]
      obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le hpos
      refine ⟨N, ?_⟩
      have hN' : (u : ℂ) ^ 2 + u * v + k * v ^ 2 = N := by exact_mod_cast hN
      rw [conj_el]
      linear_combination -hN' + (v : ℂ) ^ 2 * w_sq hk
    · have h1 : (2 * wK d - 1) ∈ algebraicClosure ℚ ℂ := by
        rw [mem_algebraicClosure_iff]
        refine IsAlgebraic.of_pow two_pos ?_
        rw [sq_two_w, ← mem_algebraicClosure_iff]
        exact neg_mem (natCast_mem _ _)
      have h2 : wK d = ((2 * wK d - 1) + 1) / ((2 : ℕ) : ℂ) := by push_cast; ring
      have h3 : wK d ∈ algebraicClosure ℚ ℂ := by
        rw [h2]; exact div_mem (add_mem h1 (one_mem _)) (natCast_mem _ _)
      exact add_mem (intCast_mem _ _) (mul_mem (intCast_mem _ _) h3)
  · rintro α n ⟨u, v, rfl⟩ h1 h2
    rw [e1, norm_le_iff] at h1
    rw [e2, norm_le_iff] at h2
    have hv : (q : ℤ_[q]) ^ n ∣ (v : ℤ_[q]) := by
      have := dvd_sub h1 h2
      rw [show (u + v * r - (u + v * (1 - r)) : ℤ_[q]) = v * (2 * r - 1) by ring] at this
      exact hu.dvd_mul_right.1 this
    have hu' : (q : ℤ_[q]) ^ n ∣ (u : ℤ_[q]) := by
      have := dvd_sub h1 (hv.mul_right r)
      simpa using this
    obtain ⟨a, rfl⟩ := int_dvd hu'
    obtain ⟨b, rfl⟩ := int_dvd hv
    refine ⟨a, b, ?_⟩
    have : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
    push_cast
    field_simp
  · intro m s hsq
    have hsu : IsUnit (s : ℤ_[q]) := by
      rw [PadicInt.isUnit_iff]
      have h1 : ¬ ‖((s : ℤ) : ℤ_[q])‖ < 1 := by
        rw [PadicInt.norm_int_lt_one_iff_dvd]
        have := (Nat.Prime.coprime_iff_not_dvd hq.out).1 hsq.symm
        exact_mod_cast this
      push_cast at h1
      exact le_antisymm (PadicInt.norm_le_one _) (not_lt.1 h1)
    obtain ⟨t, ht⟩ := hsu.exists_right_inv
    obtain ⟨u, v, h1, h2⟩ := exists_approx hu t 0 m
    refine ⟨u + v * wK d, ⟨u, v, rfl⟩, ?_, ?_⟩
    · have : ι ((s : ℂ) * (u + v * wK d)) - 1 = zcHom q (s * (u + v * r - t)) := by
        rw [map_mul, e1, mul_sub, ht]; simp
      rw [this, norm_le_iff]
      exact h1.mul_left _
    · rw [e2, norm_le_iff]; simpa using h2
  · intro n
    by_cases h2 : q = 2
    · obtain ⟨u, v, h1, h3⟩ := exists_approx hu 0 1 (n + 1)
      refine ⟨u + v * wK d, ⟨u, v, rfl⟩, ?_, ?_⟩
      · rw [e1, norm_le_iff]
        exact (pow_dvd_pow _ (Nat.le_succ n)).trans (by simpa using h1)
      · rintro ⟨a, b, hab⟩
        have h4 : (u : ℂ) + v * wK d = ((2 * a : ℤ) : ℂ) + ((2 * b : ℤ) : ℂ) * wK d := by
          push_cast; linear_combination 2 * hab
        obtain ⟨rfl, rfl⟩ := coord_unique hd.pos h4
        have h5 : (q : ℤ_[q]) ∣ _ := (dvd_pow_self _ (Nat.succ_ne_zero n)).trans h3
        have h6 : (q : ℤ_[q]) ∣ ((2 * a : ℤ) + (2 * b : ℤ) * (1 - r)) := by
          refine ⟨a + b * (1 - r), ?_⟩
          have : (q : ℤ_[q]) = 2 := by
            have := congrArg (Nat.cast : ℕ → ℤ_[q]) h2
            simpa using this
          rw [this]; push_cast; ring
        have h7 := dvd_sub h6 h5
        rw [sub_sub_cancel] at h7
        exact PadicInt.prime_p.not_dvd_one h7
    · refine ⟨(q : ℂ) ^ n, ⟨q ^ n, 0, by simp⟩, ?_, ?_⟩
      · have : ι ((q : ℂ) ^ n) = zcHom q (q ^ n) := by simp
        rw [this, norm_le_iff]
      · rintro ⟨a, b, hab⟩
        have h4 : ((q ^ n : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * wK d
            = ((2 * a : ℤ) : ℂ) + ((2 * b : ℤ) : ℂ) * wK d := by
          push_cast; linear_combination 2 * hab
        have h5 := (coord_unique hd.pos h4).1
        have h6 : (2 : ℕ) ∣ q ^ n := by
          have : (2 : ℤ) ∣ q ^ n := ⟨a, h5⟩
          exact_mod_cast this
        exact h2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq.out).1
          (Nat.prime_two.dvd_of_dvd_pow h6)).symm
  · intro x y hx hy
    obtain ⟨u, v, h⟩ := in_mul hk hx (in_conj hy)
    refine ⟨v, ?_⟩
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd.pos)
    unfold h1
    rw [h, Complex.im_ofReal_mul]
    simp [im_w]
    field_simp
