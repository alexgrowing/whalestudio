import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTerms

open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex.Arch
variable {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O}

namespace Dict
variable (d : Dict N B)

theorem tx_ex_zero : d.ex 0 = 1 := (d.ab.2.2.1 0).2 B.abelian₂.zero_mem

theorem tx_ex_smul (n : ℕ) (x : Fin B.gB → ℂ) : d.ex ((n : ℂ) • x) = d.ex x ^ n := by
  induction n with
  | zero => simp [d.tx_ex_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, d.ab.1, ih, pow_succ]

theorem tx_ex_neg (x : Fin B.gB → ℂ) : d.ex (-x) = (d.ex x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← d.ab.1, neg_add_cancel, d.tx_ex_zero])

theorem tx_dbl (x : Fin B.gB → ℂ) : dbl N.θ N.σ (d.ex x) * d.fr (x + x) = d.fr x ^ 4 := by
  have a := d.ab.2.2.2.2.2.1 x (-x) x
  have b := d.ab.2.2.2.2.2.2.1 x
  rw [add_neg_cancel, neg_add_cancel, zero_add, d.ab.2.2.2.1, d.tx_ex_neg] at a
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  apply Additive.ofMul.injective
  simp only [dbl, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a b ⊢
  linear_combination (norm := abel) a - b

theorem tx_cubN (x : Fin B.gB → ℂ) (i : ℕ) :
    cubN N.θ i 1 (d.ex x) (d.ex x) * d.fr ((i : ℂ) • x) * d.fr x * d.fr (x + x) ^ i =
      d.fr ((i : ℂ) • x + x) * d.fr x ^ (2 * i) := by
  induction i with
  | zero => simp [cubN, d.ab.2.2.2.1]
  | succ i ih =>
    have a := d.ab.2.2.2.2.2.1 ((i : ℂ) • x) x x
    rw [d.tx_ex_smul] at a
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, Nat.cast_succ, add_smul, one_smul, one_mul, Nat.mul_succ, pow_add (d.fr x), pow_succ (d.fr (x + x))]
    replace a := congrArg Additive.ofMul a
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [ofMul_mul, sq] at a ih ⊢
    linear_combination (norm := abel) a + ih

theorem tx_cubN_div (x : Fin B.gB → ℂ) (i : ℕ) :
    cubN N.θ i 1 (d.ex x) (d.ex x) / dbl N.θ N.σ (d.ex x) ^ i * d.fr ((i : ℂ) • x) * d.fr x * d.fr x ^ (2 * i) =
      d.fr ((i : ℂ) • x + x) := by
  have a := congrArg Additive.ofMul (d.tx_cubN x i)
  have b := congrArg (fun t => Additive.ofMul (t ^ i)) (d.tx_dbl x)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b ⊢
  linear_combination (norm := module) a - b

theorem tx_mulq (x : Fin B.gB → ℂ) (n : ℕ) :
    mulq N.θ N.σ n (d.ex x) * d.fr x ^ (n ^ 2) = d.fr ((n : ℂ) • x) := by
  induction n with
  | zero => simp [mulq, d.ab.2.2.2.1]
  | succ n ih =>
    rw [mulq] at ih
    rw [mulq, Finset.prod_range_succ, Nat.cast_succ, add_smul, one_smul, ← d.tx_cubN_div, ← ih,
      show (n + 1) ^ 2 = n ^ 2 + 1 + 2 * n by ring, pow_add, pow_succ]
    simp only [mul_assoc, mul_left_comm]

theorem tx_isPt_pow (h : PtSt) {v : B.V} {g : N.Gt} (hg : d.IsPt v g) (n : ℕ) : d.IsPt ((n : ℂ) • v) (g ^ n) := by
  obtain ⟨-, -, h3, h4, -⟩ := h O N B d
  induction n with
  | zero =>
    rw [pow_zero, h4]
    exact ⟨0, rfl, by simp⟩
  | succ n ih =>
    rw [Nat.cast_succ, add_smul, one_smul, pow_succ]
    exact h3 _ _ _ _ ih hg

theorem tx_vt {v : B.V} {g : N.Gt} (hg : d.IsPt v g) (x : B.X) :
    N.vt g (d.eX x) = B.term 1 0 d.th x v * d.fr v.2 := by
  have a := hg.2 x
  have b := congrArg Units.val (d.ψ_eq x)
  rw [NumD.vt, hg.1, d.c_eq, ← d.ab.1, d.ab.2.2.2.2.2.2.2.2, AnArc.term, add_comm v.2, ← b]
  simp only [Units.val_mul, pow_one, map_zero, AnArc.e_zero, zero_add, one_smul]
  linear_combination (N.ψ (d.eX x) : ℂ) * d.th (B.ct x + v.2) * a
end Dict

theorem Dict.tx_wQ (d : Dict N B) {k t : ℕ} (hk : k = 2 * t + 1) {la : B.La} {p : N.QT k} (hp : d.Rep k la p) :
    (N.wQ p : ℂ) * d.fr ((k : ℂ)⁻¹ • B.P0 la).2 ^ k * B.ah la.l (B.ct la.y) =
      B.psi la.y * Complex.exp (lin B la (B.P0 la) / k) ^ t := by
  obtain ⟨hy, hb, hs⟩ := hp
  have k0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  replace hs := hs la.y
  have hx : (k : ℂ) • ((k : ℂ)⁻¹ • B.P0 la).2 = B.ct la.y + la.l := by
    rw [Prod.smul_snd, smul_inv_smul₀ k0, AnArc.degeneratingTori_basePeriodMap_snd]
  have hE : Complex.exp (lin B la (B.P0 la) / k) * eTwoPi (((k : ℂ)⁻¹ • B.P0 la).1 la.y) =
      Complex.exp (Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la.l) := by
    rw [eTwoPi, ← Complex.exp_add, lin, Prod.smul_snd, B.H_smul_left, Prod.smul_fst, AddMonoidHom.smul_apply,
      smul_eq_mul]
    congr 1
    ring
  generalize ((k : ℂ)⁻¹ • B.P0 la).2 = x at *
  generalize Complex.exp (lin B la (B.P0 la) / k) = E at *
  generalize eTwoPi (((k : ℂ)⁻¹ • B.P0 la).1 la.y) = e at *
  have f1 := d.ab.2.2.2.2.1 la.l (B.ct la.y)
  have f2 := d.ab.2.2.2.2.1 la.l (B.ct la.y + x)
  rw [B.ah_add, ← hE, add_right_comm] at f2
  have a := congrArg Units.val (d.tx_mulq x k)
  have b := congrArg Units.val (d.tx_cubN_div x k)
  have c := congrArg Units.val (d.ψ_eq la.y)
  rw [hx] at a b
  have ht : (k - 1) / 2 = t := by omega
  rw [NumD.wQ, NumB.wS, hy, hb, ht, mul_div_assoc (p.1.2.s _)]
  generalize cubN N.θ k 1 (d.ex x) (d.ex x) / dbl N.θ N.σ (d.ex x) ^ k = D at *
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_div_eq_div_val] at a b c ⊢
  have hD : (p.1.2.s (d.eX la.y) : ℂ) * D * (d.fr x ^ (2 * k) * E) = 1 := by
    refine mul_right_cancel₀ (b := (d.fr (B.ct la.y) : ℂ) * d.fr x * e) ?_ ?_
    · refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) ?_
      rintro rfl
      exact Complex.exp_ne_zero _ (hE.symm.trans (mul_zero _))
    · linear_combination hs - (p.1.2.s (d.eX la.y) : ℂ) * f2 +
        (p.1.2.s (d.eX la.y) : ℂ) * B.ah la.l (B.ct la.y) * E * e * b +
        (p.1.2.s (d.eX la.y) : ℂ) * D * (d.fr x ^ (2 * k) * E) * d.fr x * e * f1
  have hD' := (mul_eq_one_iff_inv_eq₀ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))).1 hD
  rw [div_eq_mul_inv, ← inv_pow, hD', mul_pow, ← pow_mul, ← c, f1, ← a,
    show k ^ 2 = 2 * k * t + k by rw [sq]; nth_rw 2 [hk]; ring, pow_add]
  ring

theorem IsPrim.tx_sign {w₀ : O} (h : IsPrim B w₀) (la : B.La) :
    (B.psi la.y : ℂ) =
      (-1) ^ B.EF la (w₀ • la) * Complex.exp (-(lin B la (B.P0 la) / 2)) * B.ah la.l (B.ct la.y) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hy : la.y = w₀ • la.y + star w₀ • la.y := by rw [← add_smul, h1, one_smul]
  have hT : B.T la.y la.y = 2 * B.T la.y (w₀ • la.y) := by
    have : B.T la.y la.y = B.T la.y (w₀ • la.y + star w₀ • la.y) := by rw [← hy]
    rw [this, map_add, ← B.T_adj, B.T_symm (w₀ • la.y), two_mul]
  have hn : la.n la.y = la.n (w₀ • la.y) + la.n (star w₀ • la.y) := by rw [← map_add, ← hy]
  have hm : ∀ z : ℤ, (-1 : ℂ) ^ z = Complex.exp (z * (Real.pi * Complex.I)) := fun z => by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [h3, AnArc.ah, h2, hm, hm, eTwoPi, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
    Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(la.n (star w₀ • la.y) + B.Ef la.l (B.FLam w₀ la.l)), ?_⟩
  simp only [lin, AnArc.EF_apply, AnArc.La.smul_y, AnArc.La.smul_n_apply, AnArc.La.smul_l, AnArc.degeneratingTori_basePeriodMap_fst_apply,
    AnArc.degeneratingTori_basePeriodMap_snd, AnArc.H_add_left, hT, hn]
  have := Complex.I_ne_zero
  push_cast
  field_simp
  ring

theorem txSt_of_ptSt (h : PtSt) : TxSt := by
  intro O _ _ N B d w₀ hw k β hβ m hm ho w u hu la p hp x
  obtain ⟨t, ht⟩ := ho.pow (n := 2)
  have m0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ho.pos.ne'
  have hQ := d.tx_wQ ht hp
  have hv := d.tx_vt (d.tx_isPt_pow h hp.2 m) x
  have hq := congrArg Units.val (d.tx_mulq (((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la).2 m)
  have hmm : (m : ℂ) • ((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la = (m : ℂ)⁻¹ • B.P0 la := by
    rw [smul_smul]
    congr 1
    push_cast
    field_simp
  rw [← Prod.smul_snd (m : ℂ), hmm] at hq
  rw [hmm] at hv
  rw [hw.tx_sign, mul_right_comm _ (B.ah _ _), mul_left_inj' (B.ah_ne_zero _ _), mul_assoc, ← Complex.exp_nat_mul,
    ← Complex.exp_add] at hQ
  have hterm : B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.Pw w la) =
      B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la) * eTwoPi ((m : ℂ)⁻¹ * (w * B.be la.y x)) := by
    have e1 : ((m : ℂ)⁻¹ • B.Pw w la).1 (0 + 1 • x) =
        ((m : ℂ)⁻¹ • B.P0 la).1 (0 + 1 • x) + (m : ℂ)⁻¹ * (w * B.be la.y x) := by
      simp only [zero_add, one_smul, Prod.smul_fst, AddMonoidHom.smul_apply, smul_eq_mul, AnArc.Pw_fst_apply,
        AnArc.degeneratingTori_basePeriodMap_fst_apply]
      ring
    have e2 : ((m : ℂ)⁻¹ • B.Pw w la).2 = ((m : ℂ)⁻¹ • B.P0 la).2 := by
      rw [Prod.smul_snd, Prod.smul_snd, AnArc.Pw_snd, AnArc.degeneratingTori_basePeriodMap_snd]
    rw [AnArc.term, AnArc.term, e1, e2, AnArc.e_add]
    ring
  have hlin : lin B la (B.Pw w la) = lin B la (B.P0 la) - 2 * Real.pi * Complex.I * (w * B.be la.y la.y) := by
    simp only [lin, AnArc.Pw_fst_apply, AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.Pw_snd, AnArc.degeneratingTori_basePeriodMap_snd]
    ring
  obtain ⟨c, hc⟩ : (2 * (m : ℤ) ^ 2) ∣ β.be (d.eX la.y + m • d.eX x) (d.eX la.y + m • d.eX x) :=
    (mul_dvd_mul_left 2 (by exact_mod_cast hm)).trans (β.dvd _ _)
  have hc' : 2 * (m : ℤ) ^ 2 * c = B.be la.y la.y + 2 * m * B.be la.y x + m ^ 2 * (2 * B.q x) := by
    rw [← hc, ← map_nsmul, ← map_add, ← hβ, B.two_mul_q]
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, B.be_symm x la.y]
    ring
  replace hc' : (c : ℂ) = (B.be la.y la.y + 2 * m * B.be la.y x + m ^ 2 * (2 * B.q x)) / (2 * m ^ 2) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero (pow_ne_zero _ m0)), mul_comm]
    exact_mod_cast hc'
  have ht' : (t : ℂ) = (m ^ 2 - 1) / 2 := by
    have : (m : ℂ) ^ 2 = 2 * t + 1 := by exact_mod_cast ht
    rw [this]; ring
  have key : eTwoPi (w * c) * Complex.exp (-(lin B la (B.P0 la) / 2) + t * (lin B la (B.P0 la) / (m ^ 2 : ℕ))) =
      Complex.exp (-(lin B la (B.Pw w la) / (2 * (m : ℂ) ^ 2))) * eTwoPi ((m : ℂ)⁻¹ * (w * B.be la.y x)) *
        eTwoPi (w * B.exponent 1 0 x) := by
    simp only [eTwoPi, ← Complex.exp_add, hlin, hc', ht', AnArc.exponent, map_zero]
    congr 1
    push_cast
    field_simp
    ring
  have m0' : (2 * (m : ℤ) ^ 2) ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero _ (Int.natCast_ne_zero.2 ho.pos.ne'))
  rw [N.twist_txT β u m hm ho, hp.1, hc, Int.mul_ediv_cancel_left _ m0', Units.val_zpow_eq_zpow_val, hu,
    ← AnArc.e_mul_intCast, NumD.txT, hv, hterm, hp.2.1, ← hq, Units.val_div_eq_div_val, Units.val_mul,
    Units.val_pow_eq_pow_val]
  have hmq := (mulq N.θ N.σ m (d.ex (((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la).2)).ne_zero
  linear_combination (eTwoPi (w * c) * B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la)) * hQ +
    (-1) ^ B.EF la (w₀ • la) * B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la) * key +
    eTwoPi (w * c) * B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la) * N.wQ p *
      (d.fr (((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la).2 : ℂ) ^ m ^ 2 * inv_mul_cancel₀ hmq

end GlobalTheory.Ex.Arch
end
