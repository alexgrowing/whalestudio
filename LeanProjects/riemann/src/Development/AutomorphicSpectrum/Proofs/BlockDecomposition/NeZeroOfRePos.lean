import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

noncomputable section

open UpperHalfPlane hiding I
open Complex CongruenceSubgroup
open scoped MatrixGroups ModularForm ComplexConjugate Real
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HalfWeightUnfold

lemma arg_ne_pi {p : ℂ} (hp : 0 < p.re) : p.arg ≠ π := by
  intro h
  have := (Complex.arg_eq_pi_iff.1 h).1
  linarith

lemma ne_zero_of_re_pos {p : ℂ} (hp : 0 < p.re) : p ≠ 0 := by
  rintro rfl
  simp at hp

lemma log_mul_conj {p : ℂ} (hp : 0 < p.re) : log (p * conj p) = log p + log (conj p) := by
  have h0 := ne_zero_of_re_pos hp
  have hc : conj p ≠ 0 := (map_ne_zero _).2 h0
  rw [Complex.log_mul_eq_add_log_iff h0 hc, Complex.arg_conj, if_neg (arg_ne_pi hp)]
  simp [Real.pi_pos.le, Real.pi_pos]

lemma pair {p : ℂ} (hp : 0 < p.re) (k ν : ℕ) (ω α β : ℂ) (h1 : (k : ℂ) - ω = -α)
    (h2 : (ν : ℂ) + 1 / 2 - ω = -β) :
    p ^ k * ((conj p) ^ ν * (conj p) ^ (1 / 2 : ℂ)) * (p * conj p) ^ (-ω) =
      p ^ (-α) * (conj p) ^ (-β) := by
  have h0 := ne_zero_of_re_pos hp
  have hc : conj p ≠ 0 := (map_ne_zero _).2 h0
  have h3 : p * conj p ≠ 0 := mul_ne_zero h0 hc
  rw [← cpow_natCast p k, ← cpow_natCast (conj p) ν]
  simp only [cpow_def_of_ne_zero h0, cpow_def_of_ne_zero hc, cpow_def_of_ne_zero h3,
    log_mul_conj hp, ← exp_add]
  congr 1
  linear_combination (log p) * h1 + (log (conj p)) * h2

lemma real_mul_cpow {r : ℝ} (hr : 0 < r) {x : ℂ} (hx : x ≠ 0) (c : ℂ) :
    ((r : ℂ) * x) ^ c = (r : ℂ) ^ c * x ^ c := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero hr0 hx), cpow_def_of_ne_zero hr0, cpow_def_of_ne_zero hx,
    Complex.log_ofReal_mul hr hx, ← exp_add, Complex.ofReal_log hr.le]
  congr 1
  ring

lemma real_div_cpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℂ) :
    (((a / b : ℝ)) : ℂ) ^ x = (a : ℂ) ^ x * (b : ℂ) ^ (-x) := by
  have hb' : ((b : ℂ)).arg ≠ π := arg_ne_pi (by simpa using hb)
  rw [div_eq_mul_inv, Complex.ofReal_mul, mul_cpow_ofReal_nonneg ha.le (inv_nonneg.2 hb.le),
    Complex.ofReal_inv, inv_cpow _ _ hb', cpow_neg]

def kap (k ν : ℕ) (ω u : ℂ) : ℂ :=
  u ^ k * conj (u ^ ν * (-I * u) ^ (1 / 2 : ℂ)) * ((normSq u : ℝ) : ℂ) ^ (-ω)

lemma kap_eq (k ν : ℕ) (s u : ℂ) (hu : 0 < u.im) :
    kap k ν (om k ν s) u = I ^ k * (-I) ^ ν * KK (al k ν s) (be k ν s) u.im u.re := by
  obtain ⟨p, hp⟩ : ∃ p, p = -I * u := ⟨_, rfl⟩
  have hre : 0 < p.re := by simpa [hp] using hu
  have hu' : u = I * p := by rw [hp]; linear_combination (u) * I_sq
  have h0 := ne_zero_of_re_pos hre
  have hn : ((normSq u : ℝ) : ℂ) = p * conj p := by
    rw [Complex.mul_conj, hu']; simp [map_mul]
  have hK : KK (al k ν s) (be k ν s) u.im u.re =
      p ^ (-(al k ν s)) * (conj p) ^ (-(be k ν s)) := by
    have e1 : (u.im : ℂ) - I * u.re = p := by
      rw [hp]; apply Complex.ext <;> simp
    have e2 : (u.im : ℂ) + I * u.re = conj p := by
      rw [hp]; apply Complex.ext <;> simp
    rw [KK, e1, e2]
  have h12 : conj (p ^ (1 / 2 : ℂ)) = (conj p) ^ (1 / 2 : ℂ) := by
    have hh : conj (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
    rw [conj_cpow p _ (arg_ne_pi hre), hh]
  have key := pair hre k ν (om k ν s) (al k ν s) (be k ν s)
    (by simp only [om, al]; ring) (by simp only [om, be]; ring)
  rw [kap, ← hp, hn, hK, hu', mul_pow, mul_pow, map_mul, map_mul, map_pow, map_pow,
    conj_I, h12]
  linear_combination (I ^ k * (-I) ^ ν) * key

lemma KK_hom (α β : ℂ) {r : ℝ} (hr : 0 < r) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    KK α β (r * y) (r * t) = (r : ℂ) ^ (-(α + β)) * KK α β y t := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have h1 : (y : ℂ) - I * t ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hy.ne' this
  have h2 : (y : ℂ) + I * t ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hy.ne' this
  have e1 : ((r * y : ℝ) : ℂ) - I * ((r * t : ℝ) : ℂ) = (r : ℂ) * ((y : ℂ) - I * t) := by
    push_cast; ring
  have e2 : ((r * y : ℝ) : ℂ) + I * ((r * t : ℝ) : ℂ) = (r : ℂ) * ((y : ℂ) + I * t) := by
    push_cast; ring
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [KK, KK, e1, e2, real_mul_cpow hr h1, real_mul_cpow hr h2, neg_add, cpow_add _ _ hr0]
  ring

lemma char_id {N M : ℕ} [NeZero N] [NeZero M] (hM : N ∣ M) (χ : DirichletCharacter ℂ N)
    (c : DirichletCharacter ℂ M) (d : ℕ) (hu : IsUnit (d : ZMod M)) :
    χ (d : ZMod N) * conj ((c * DirichletCharacter.changeLevel hM χ⁻¹)⁻¹ (d : ZMod M)) =
      c (d : ZMod M) := by
  obtain ⟨u, hu⟩ := hu
  have hcast : ZMod.cast (u : ZMod M) = (d : ZMod N) := by
    rw [hu]; exact ZMod.cast_natCast hM d
  have hun : IsUnit (d : ZMod N) := by
    rw [← hcast]
    have := (u.isUnit).map (ZMod.castHom hM (ZMod N))
    simpa using this
  have hχ : χ (d : ZMod N) ≠ 0 := (hun.map χ).ne_zero
  have hn : ‖(c * DirichletCharacter.changeLevel hM χ⁻¹) (u : ZMod M)‖ = 1 :=
    DirichletCharacter.unit_norm_eq_one _ u
  rw [← hu, MulChar.inv_apply_eq_inv', map_inv₀, Complex.inv_eq_conj (by simpa using congrArg id hn),
    Complex.conj_conj, MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd _ hM u, hcast,
    MulChar.inv_apply_eq_inv']
  field_simp

lemma assemble (Xd Pd Cd A T Y g Dh Rc Q n KU Kwi Lm Lp dm dp Kv : ℂ) (h1 : Xd * Pd = Cd)
    (h2 : Q * Rc * n = KU * Kwi) (h3 : Lm * Lp = 1) (h4 : dm * dp = Dh) (h5 : Kv = Lp * dp * KU) :
    (Xd * Q * A) * (Pd * g * Dh * Rc * T) * (Y * n) =
      A * T * (Y * Lm * Kwi) * (Cd * dm * g * Kv) := by
  subst h1 h5 h4
  linear_combination (Xd * Pd * A * g * (dm * dp) * T * Y) * h2 -
    (A * T * Y * Kwi * Xd * Pd * dm * g * dp * KU) * h3

lemma cpow_ne {Q : ℂ} (hQ : Q ≠ 0) (x : ℂ) : Q ^ x ≠ 0 := by
  rw [cpow_def_of_ne_zero hQ]; exact exp_ne_zero _

lemma kap_ratio (k ν : ℕ) (s U w : ℂ) (hU : 0 < U.im) (hw : 0 < w.im) :
    (U / w) ^ k * conj ((-I * U) ^ (1 / 2 : ℂ) * (-I * w) ^ (-(1 / 2 : ℂ)) * (U / w) ^ ν) *
        ((normSq (U / w) : ℝ) : ℂ) ^ (-(om k ν s)) =
      KK (al k ν s) (be k ν s) U.im U.re * (KK (al k ν s) (be k ν s) w.im w.re)⁻¹ := by
  have hc : (I ^ k * (-I) ^ ν : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ I_ne_zero) (pow_ne_zero _ (neg_ne_zero.2 I_ne_zero))
  have hU0 : U ≠ 0 := by rintro rfl; simp at hU
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hQ : -I * w ≠ 0 := mul_ne_zero (neg_ne_zero.2 I_ne_zero) hw0
  have e : KK (al k ν s) (be k ν s) U.im U.re * (KK (al k ν s) (be k ν s) w.im w.re)⁻¹ =
      kap k ν (om k ν s) U * (kap k ν (om k ν s) w)⁻¹ := by
    rw [kap_eq k ν s U hU, kap_eq k ν s w hw, mul_inv]
    calc _ = (I ^ k * (-I) ^ ν * (I ^ k * (-I) ^ ν)⁻¹) * (KK (al k ν s) (be k ν s) U.im U.re *
          (KK (al k ν s) (be k ν s) w.im w.re)⁻¹) := by rw [mul_inv_cancel₀ hc, one_mul]
      _ = _ := by ring
  have hnU : 0 < normSq U := normSq_pos.2 hU0
  have hnw : 0 < normSq w := normSq_pos.2 hw0
  have hnw0 : ((normSq w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnw.ne'
  have h1 : ((normSq w : ℝ) : ℂ) ^ (om k ν s) = (((normSq w : ℝ) : ℂ) ^ (-(om k ν s)))⁻¹ := by
    rw [cpow_neg, inv_inv]
  rw [e, map_div₀, real_div_cpow hnU hnw, neg_neg, h1, kap, kap, cpow_neg (-I * w)]
  have a1 := cpow_ne hnw0 (-(om k ν s))
  have a2 : conj ((-I * w) ^ (1 / 2 : ℂ)) ≠ 0 := (map_ne_zero _).2 (cpow_ne hQ _)
  have a3 : conj w ≠ 0 := (map_ne_zero _).2 hw0
  simp only [map_mul, map_inv₀, map_pow, map_div₀, div_pow, mul_inv]
  field_simp

theorem term_of_theta : T3 → T4 → T5 := by
  intro h3 h4 k N M ν d _ _ hM χ f a hf c c' γ z s hd hν hc hdd
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = 4 * M ^ 2 := ⟨_, rfl⟩
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hL0 : 0 < L := by rw [hL]; positivity
  have hcL : γ 1 0 = (L : ℤ) * c' := by rw [hc, hL]; push_cast; ring
  have hdet : γ 0 0 * d - γ 0 1 * (4 * (M : ℤ) ^ 2 * c') = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    rw [← hc, ← hdd]
    exact this
  have hunit : IsUnit (d : ZMod M) := by
    apply IsUnit.of_mul_eq_one ((γ 0 0 : ℤ) : ZMod M)
    have := congrArg (Int.cast : ℤ → ZMod M) hdet
    push_cast at this
    simpa [mul_comm] using this
  have hmem : γ ∈ Gamma0 N := by
    rw [Gamma0_mem, hc]
    have hdv : (N : ℤ) ∣ 4 * (M : ℤ) ^ 2 * c' :=
      Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow (Int.natCast_dvd_natCast.2 hM) two_ne_zero) 4) c'
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hdv
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  obtain ⟨w, hwd⟩ : ∃ w, w = -1 / (z : ℂ) := ⟨_, rfl⟩
  have hw : 0 < w.im := by
    have := UpperHalfPlane.im_inv_neg_coe_pos z
    rwa [show (-(z : ℂ))⁻¹ = w by rw [hwd, inv_neg, neg_div, one_div]] at this
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  obtain ⟨U, hUd⟩ : ∃ U : ℂ, U = d * w - (γ 1 0 : ℤ) := ⟨_, rfl⟩
  obtain ⟨v, hvd⟩ : ∃ v : ℂ, v = w / (L : ℂ) := ⟨_, rfl⟩
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  obtain ⟨r, hrd⟩ : ∃ r : ℝ, r = (L : ℝ) * d := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrd]; positivity
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hwv : w = ((L : ℝ) : ℂ) * v := by rw [hvd]; push_cast; field_simp
  have hvim : 0 < v.im := by
    have h := hw
    rw [hwv, Complex.im_ofReal_mul] at h
    exact (mul_pos_iff_of_pos_left (by exact_mod_cast hL0)).1 h
  have hUe : U = (r : ℂ) * (v - (((c' : ℝ) / (d : ℝ) : ℝ) : ℂ)) := by
    rw [hUd, hcL, hrd, hvd]
    push_cast
    field_simp
  have hUim : U.im = r * v.im := by
    rw [hUe, Complex.im_ofReal_mul]; simp
  have hUre : U.re = r * (v.re - (c' : ℝ) / (d : ℝ)) := by
    rw [hUe, Complex.re_ofReal_mul]; simp
  have hU : 0 < U.im := by rw [hUim]; positivity
  have hU0 : U ≠ 0 := by rintro rfl; simp at hU
  have hden : denom γ z = U / w := by
    rw [ModularGroup.denom_apply, hUd, hwd, hdd]
    push_cast
    field_simp
    ring
  have hq0 : U / w ≠ 0 := div_ne_zero hU0 hw0
  have hfz : f (γ • z) = χ (d : ZMod N) * (U / w) ^ k * f z := by
    have e := congrFun (hf.char γ hmem) z
    rw [ModularForm.SL_slash_apply] at e
    simp only [Pi.smul_apply, smul_eq_mul] at e
    rw [hdd, Int.cast_natCast, hden, zpow_neg, zpow_natCast,
      mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ hq0)] at e
    rw [e]; ring
  have hnq : 0 < normSq (U / w) := normSq_pos.2 hq0
  have him : (((γ • z : ℍ).im : ℝ) : ℂ) ^ om k ν s =
      ((z.im : ℝ) : ℂ) ^ om k ν s * ((normSq (U / w) : ℝ) : ℂ) ^ (-(om k ν s)) := by
    rw [ModularGroup.im_smul_eq_div_normSq, hden, real_div_cpow z.im_pos hnq]
  have hdarg : ((d : ℂ)).arg ≠ π := arg_ne_pi (by simpa using hd)
  have hdconj : conj ((d : ℂ) ^ (-(1 / 2 : ℂ))) = (d : ℂ) ^ (-(1 / 2 : ℂ)) := by
    have hh : conj (-(1 / 2 : ℂ)) = -(1 / 2) := by rw [map_neg, map_div₀, map_one, map_ofNat]
    have := conj_cpow (d : ℂ) (-(1 / 2)) hdarg
    rw [Complex.conj_natCast, hh] at this
    exact this.symm
  have hg := h4 M d (γ 0 0) (γ 0 1) c' hd hdet
  have ht := h3 M d ν (c * DirichletCharacter.changeLevel hM χ⁻¹)⁻¹ c' γ z hd hν hc hdd
  rw [← hwd, ← hUd] at ht
  have hth : conj (th (fun n => (c * DirichletCharacter.changeLevel hM χ⁻¹)⁻¹ (n : ZMod M)) ν (γ • z : ℍ)) =
      conj ((c * DirichletCharacter.changeLevel hM χ⁻¹)⁻¹ (d : ZMod M)) * GS c' d * (d : ℂ) ^ (-(1 / 2 : ℂ)) *
        conj ((-I * U) ^ (1 / 2 : ℂ) * (-I * w) ^ (-(1 / 2 : ℂ)) * (U / w) ^ ν) *
        conj (th (fun n => (c * DirichletCharacter.changeLevel hM χ⁻¹)⁻¹ (n : ZMod M)) ν z) := by
    rw [ht]
    simp only [map_mul]
    rw [hg, hdconj]
    ring
  have hsum : al k ν s + be k ν s = s + 1 / 2 := by simp only [al, be]; ring
  have hKv : KK (al k ν s) (be k ν s) v.im (v.re - (c' : ℝ) / (d : ℝ)) =
      (r : ℂ) ^ (s + 1 / 2) * KK (al k ν s) (be k ν s) U.im U.re := by
    rw [hUim, hUre, KK_hom _ _ hr hvim, hsum, ← mul_assoc, ← cpow_add _ _ hr0]
    simp
  have hrsplit : (r : ℂ) ^ (s + 1 / 2) = (L : ℂ) ^ (s + 1 / 2) * (d : ℂ) ^ (s + 1 / 2) := by
    have := mul_cpow_ofReal_nonneg (Nat.cast_nonneg (α := ℝ) L) (Nat.cast_nonneg (α := ℝ) d) (s + 1 / 2)
    rw [hrd]
    simpa using this
  have e3 : (L : ℂ) ^ (-(s + 1 / 2)) * (L : ℂ) ^ (s + 1 / 2) = 1 := by
    rw [← cpow_add _ _ hLc]; simp
  have e4 : (d : ℂ) ^ (-(s + 1)) * (d : ℂ) ^ (s + 1 / 2) = (d : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [← cpow_add _ _ hdc]; congr 1; ring
  have key := kap_ratio k ν s U w hU hw
  have h1 := char_id hM χ c d hunit
  simp only [FF, pref, tm]
  rw [← hL, ← hwd, ← hvd, hfz, hth, him, div_eq_mul_inv]
  exact assemble _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 key e3 e4 (by rw [hKv, hrsplit])

end GlobalTheory.CompanionTheory.HalfWeightUnfold

end
