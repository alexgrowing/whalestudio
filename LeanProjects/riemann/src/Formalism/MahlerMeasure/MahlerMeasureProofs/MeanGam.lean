import Formalism.MahlerMeasure.StatementTM
import Formalism.MahlerMeasure.GamInt
import Formalism.MahlerMeasure.LegendreDigits

namespace Formalism.GM.MeanGammaLemmas
open Polynomial Finset

lemma binK_eval_nat (F : Type) [Field F] [CharZero F] (k n : ℕ) :
    (binK F k).eval (n : F) = (n.choose k : F) := by
  simp only [binK, Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_mul]

lemma binK_map (F L : Type) [Field F] [Field L] (φ : F →+* L) (k : ℕ) :
    (binK F k).map φ = binK L k := by
  simp only [binK, Polynomial.map_mul, Polynomial.map_C, map_inv₀, map_natCast, descPochhammer_map]

lemma binMatK_map (F L : Type) [Field F] [Field L] (φ : F →+* L) {n : ℕ} (del : ℕ)
    (c : Fin n → Fin n → ℕ → F) :
    binMatK L del (fun i j k => φ (c i j k)) = (binMatK F del c).map (Polynomial.map φ) := by
  funext i j
  simp only [binMatK, Matrix.map_apply, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, binK_map]

lemma binMatK_eval_nat (F : Type) [Field F] [CharZero F] {n : ℕ} (del : ℕ)
    (c : Fin n → Fin n → ℕ → F) (i j : Fin n) (t : ℕ) :
    (binMatK F del c i j).eval (t : F) = ∑ k ∈ range (del + 1), c i j k * (t.choose k : F) := by
  simp only [binMatK, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, binK_eval_nat]

lemma norm_nat (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : n ≠ 0) :
    ‖(n : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  have h1 : ((n : ℚ) : ℚ_[p]) = (n : ℚ_[p]) := by push_cast; rfl
  rw [← h1, Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn),
    padicValRat.of_nat]
  push_cast
  try rfl

lemma neglog_zpow (p : ℕ) [hp : Fact p.Prime] (z : ℤ) : -Real.logb p ((p : ℝ) ^ (-z)) = z := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  rw [← Real.rpow_intCast, Real.logb_rpow hp0 hp1.ne']
  simp

lemma neglog_nat (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : n ≠ 0) :
    -Real.logb p ‖(n : ℚ_[p])‖ = padicValNat p n := by
  rw [norm_nat p n hn, neglog_zpow]
  simp

end Formalism.GM.MeanGammaLemmas

namespace Formalism.GM.MeanGammaLemmas
open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}

lemma coeff_initPart (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) :
    (initPart v e f).coeff m = if m v = e then f.coeff m else 0 := by
  classical
  simp only [initPart, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single m]
  · by_cases h : m v = e <;> simp [h]
  · intro b _ hb
    by_cases h : b v = e <;> simp [h, MvPolynomial.coeff_monomial, hb]
  · intro hm
    have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
    by_cases h : m v = e <;> simp [h, h0]

noncomputable def initL (p : ℕ) [Fact p.Prime] (v : σ) (e : ℕ) :
    MvPolynomial σ ℚ_[p] →ₗ[ℤ_[p]] MvPolynomial σ ℚ_[p] where
  toFun := initPart v e
  map_add' x y := by
    ext m; simp only [coeff_initPart, coeff_add]; split_ifs <;> simp
  map_smul' a x := by
    ext m
    simp only [coeff_initPart, RingHom.id_apply]
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, coeff_initPart]
    split_ifs <;> simp

lemma initL_apply (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) : initL p v e f = initPart v e f := rfl

lemma initPart_eq_zero_of_lt (v : σ) (e o : ℕ) (f : MvPolynomial σ ℚ_[p]) (hf : HasOrder v o f) (h : e < o) :
    initPart v e f = 0 := by
  ext m
  rw [coeff_initPart, MvPolynomial.coeff_zero]
  split_ifs with hme
  · by_cases hm : m ∈ f.support
    · have := hf.1 m hm
      omega
    · simpa [MvPolynomial.mem_support_iff] using hm
  · rfl

lemma init_basis {ι : Type} (f : ι → MvPolynomial σ ℚ_[p]) (ord : ι → ℕ) (v : σ)
    (Fil : ℕ → Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (hli : LinearIndependent ℤ_[p] f) (hord : ∀ b, HasOrder v (ord b) (f b))
    (hfil : ∀ e, Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) = Fil e)
    (hstep : ∀ e x, x ∈ Fil e → initPart v e x = 0 → x ∈ Fil (e + 1)) (e : ℕ) :
    LinearIndepOn ℤ_[p] (fun b => initPart v e (f b)) {b | ord b = e} ∧
      Submodule.span ℤ_[p] ((fun b => initPart v e (f b)) '' {b | ord b = e}) =
        Submodule.span ℤ_[p] (initPart v e '' (Fil e : Set (MvPolynomial σ ℚ_[p]))) := by
  constructor
  · rw [linearIndepOn_iff]
    intro l hl h0
    have hlsub : l ∈ Finsupp.supported ℤ_[p] ℤ_[p] {b | e ≤ ord b} :=
      Finsupp.supported_mono (fun b hb => le_of_eq (Eq.symm hb)) hl
    have hx : Finsupp.linearCombination ℤ_[p] f l ∈ Fil e := by
      rw [← hfil, Finsupp.mem_span_image_iff_linearCombination]
      exact ⟨l, hlsub, rfl⟩
    have hinit : initPart v e (Finsupp.linearCombination ℤ_[p] f l) = 0 := by
      rw [← initL_apply, Finsupp.apply_linearCombination]
      exact h0
    have hx1 := hstep e _ hx hinit
    rw [← hfil, Finsupp.mem_span_image_iff_linearCombination] at hx1
    obtain ⟨l', hl', hll'⟩ := hx1
    have heq : l' = l := by
      have := linearIndependent_iff.mp hli (l' - l) (by rw [map_sub, hll', sub_self])
      exact sub_eq_zero.mp this
    ext b
    by_cases hb : ord b = e
    · rw [← heq, Finsupp.coe_zero, Pi.zero_apply]
      exact (Finsupp.mem_supported' _ _).mp hl' b (by simp [hb])
    · rw [Finsupp.coe_zero, Pi.zero_apply]
      exact (Finsupp.mem_supported' _ _).mp hl b hb
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨b, hb, rfl⟩
      apply Submodule.subset_span
      refine ⟨f b, ?_, rfl⟩
      show f b ∈ (Fil e : Set (MvPolynomial σ ℚ_[p]))
      rw [← hfil]
      exact Submodule.subset_span ⟨b, le_of_eq (Eq.symm hb), rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) := by
        rw [hfil]
        exact hx
      have hmap : initL p v e x ∈ Submodule.span ℤ_[p] (initL p v e '' (f '' {b | e ≤ ord b})) := by
        rw [Submodule.span_image]
        exact Submodule.mem_map_of_mem hx'
      rw [initL_apply] at hmap
      refine (Submodule.span_le.mpr ?_) hmap
      rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      by_cases hbe : ord b = e
      · exact Submodule.subset_span ⟨b, hbe, rfl⟩
      · rw [SetLike.mem_coe, initL_apply,
          initPart_eq_zero_of_lt v e (ord b) (f b) (hord b) (lt_of_le_of_ne hb (Ne.symm hbe))]
        exact Submodule.zero_mem _

end Formalism.GM.MeanGammaLemmas

namespace Formalism.GM.MeanGammaLemmas
open Finset

lemma det_block_norm {F : Type} [NormedField F] {n : ℕ} (B G : Matrix (Fin n) (Fin n) F) (e : Fin n → ℕ)
    (β : ℕ → F) (c : ℝ) (hc : 0 ≤ c)
    (hB : ∀ i j, B i j = if e i = e j then β (e i) * G i j else 0)
    (hG : ∀ a, c ^ (Fintype.card {b // e b = a}) ≤ ‖(G.toSquareBlock e a).det‖) :
    ∏ b, (‖β (e b)‖ * c) ≤ ‖B.det‖ := by
  classical
  have hBT : B.BlockTriangular e := by
    intro i j hij
    rw [hB, if_neg (ne_of_gt hij)]
  have hblock : ∀ a, B.toSquareBlock e a = β a • G.toSquareBlock e a := by
    intro a
    ext i j
    simp [Matrix.toSquareBlock_def, hB, i.2, j.2]
  rw [hBT.det, norm_prod]
  have hc := Finset.prod_comp (s := Finset.univ) (fun a => ‖β a‖ * c) e
  rw [hc]
  apply Finset.prod_le_prod (fun a _ => by positivity)
  intro a _
  rw [hblock, Matrix.det_smul, norm_mul, norm_pow, mul_pow]
  have hcard : Fintype.card {i // e i = a} = (Finset.univ.filter fun b => e b = a).card := by
    rw [Fintype.card_subtype]
  rw [← hcard]
  exact mul_le_mul_of_nonneg_left (hG a) (by positivity)

end Formalism.GM.MeanGammaLemmas

namespace Formalism.GM.MeanGammaLemmas
open Finset

lemma vfact_le (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (padicValNat p n.factorial : ℝ) ≤ n / ((p : ℝ) - 1) := by
  have hp1 := hp.out.one_lt
  have h := sub_one_mul_padicValNat_factorial (p := p) n
  have h2 : (p - 1) * padicValNat p n.factorial ≤ n := by rw [h]; exact Nat.sub_le _ _
  have hp1r : (1 : ℝ) < p := by exact_mod_cast hp1
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [le_div_iff₀ hpm]
  have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub hp1.le]; simp
  have h4 : (((p - 1) * padicValNat p n.factorial : ℕ) : ℝ) ≤ n := by exact_mod_cast h2
  rw [Nat.cast_mul, h3] at h4
  linarith

lemma nlog_le (p x B : ℕ) (hx : x ≤ B) : (Nat.log p x : ℝ) ≤ Real.logb p B := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · rw [Nat.log_of_left_le_one (by omega) x]
    interval_cases p <;> simp [Real.logb]
  · rcases Nat.eq_zero_or_pos x with rfl | hx0
    · rcases Nat.eq_zero_or_pos B with rfl | hB
      · simp
      · simp only [Nat.log_zero_right, Nat.cast_zero]
        exact Real.logb_nonneg (by exact_mod_cast hp) (by exact_mod_cast hB)
    · rw [Real.le_logb_iff_rpow_le (by exact_mod_cast hp)
        (by exact_mod_cast (lt_of_lt_of_le hx0 hx)), Real.rpow_natCast]
      exact_mod_cast (Nat.pow_log_le_self p hx0.ne').trans hx

lemma legendre' (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    (n : ℝ) / ((p : ℝ) - 1) - (padicValNat p n.factorial : ℝ) ≤ (Nat.log p n : ℝ) + 1 := by
  have hp1 := hp.out.one_lt
  have h := sub_one_mul_padicValNat_factorial (p := p) n
  have hds := Nat.digit_sum_le p n
  have hsum : (p.digits n).sum ≤ (p.digits n).length * (p - 1) := by
    have := List.sum_le_card_nsmul (p.digits n) (p - 1)
      (fun d hd => Nat.le_sub_one_of_lt (Nat.digits_lt_base hp1 hd))
    simpa using this
  have hp1r : (1 : ℝ) < p := by exact_mod_cast hp1
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hlen := Nat.digits_len p n hp1 hn.ne'
    have key : ((p : ℝ) - 1) * (padicValNat p n.factorial) = n - (p.digits n).sum := by
      have := congrArg (fun x : ℕ => (x : ℝ)) h
      rw [Nat.cast_mul, Nat.cast_sub hp1.le, Nat.cast_sub hds, Nat.cast_one] at this
      exact this
    have hsumR : ((p.digits n).sum : ℝ) ≤ ((Nat.log p n : ℝ) + 1) * ((p : ℝ) - 1) := by
      rw [hlen] at hsum
      have := (Nat.cast_le (α := ℝ)).mpr hsum
      rw [Nat.cast_mul, Nat.cast_sub hp1.le, Nat.cast_add, Nat.cast_one] at this
      exact this
    have hv : (padicValNat p n.factorial : ℝ) = (n - (p.digits n).sum) / ((p : ℝ) - 1) := by
      rw [eq_div_iff hpm.ne', ← key]
      ring
    rw [hv, ← sub_div, sub_sub_cancel, div_le_iff₀ hpm]
    exact hsumR

lemma vchoose_le (p : ℕ) [hp : Fact p.Prime] (n k : ℕ) :
    (padicValNat p (n.choose k) : ℝ) ≤ (Nat.log p n : ℝ) := by
  have := Nat.factorization_choose_le_log (p := p) (n := n) (k := k)
  rw [Nat.factorization_def _ hp.out] at this
  exact_mod_cast this

lemma neg_logb_zpow_self (p : ℕ) [hp : Fact p.Prime] (z : ℤ) : -Real.logb p ((p : ℝ) ^ z) = -z := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  rw [← Real.rpow_intCast, Real.logb_rpow hp0 hp1.ne']

lemma negLog_beta (p : ℕ) [hp : Fact p.Prime] (M e z o S : ℕ) :
    -Real.logb p ‖(p : ℚ_[p]) ^ M * ((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) /
        ((o.factorial * S.factorial : ℕ) : ℚ_[p])‖ =
      (M : ℝ) + padicValNat p e.factorial + padicValNat p ((z + e).choose e) -
        padicValNat p o.factorial - padicValNat p S.factorial := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hA : e.factorial * (z + e).choose e ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos (Nat.le_add_left e z)).ne'
  have hB : o.factorial * S.factorial ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  rw [norm_div, norm_mul, norm_pow, Padic.norm_p, norm_nat p _ hA, norm_nat p _ hB,
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.choose_pos (Nat.le_add_left e z)).ne',
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  rw [show ((p : ℝ)⁻¹) ^ M = (p : ℝ) ^ (-(M : ℤ)) by rw [zpow_neg, zpow_natCast, inv_pow],
    ← zpow_add₀ hp0.ne', ← zpow_sub₀ hp0.ne', neg_logb_zpow_self]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_neg, Int.cast_natCast, Nat.cast_add]
  ring

lemma per_row (p : ℕ) [hp : Fact p.Prime] (a r S o z e cI : ℕ) (κ C : ℝ)
    (heo : e ≤ o) (ho : o ≤ 2 * a) (hS : S ≤ 2 * a) (hz : z ≤ 2 * a) (hr : 1 ≤ r)
    (hκ : 12 * (Real.logb p (8 * a + r) + 1) ≤ κ) (hcI : (cI : ℝ) ≤ C * κ) :
    -Real.logb p ‖(p : ℚ_[p]) ^ (⌈κ⌉₊ + cI) * ((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) /
        ((o.factorial * S.factorial : ℕ) : ℚ_[p])‖ + ((S + o - e : ℕ) : ℝ) / ((p : ℝ) - 1) + κ ≤
      (C + 3) * κ := by
  rw [negLog_beta]
  have hp1r : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpm : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have L0 : 0 ≤ Real.logb p (8 * a + r) := Real.logb_nonneg hp1r (by linarith)
  have hκ0 : 0 ≤ κ := by linarith
  have hzl : (Nat.log p (z + e) : ℝ) ≤ Real.logb p (8 * a + r) := by
    have := nlog_le p (z + e) (8 * a + r) (by omega)
    push_cast at this
    exact this
  have hol : (Nat.log p o : ℝ) ≤ Real.logb p (8 * a + r) := by
    have := nlog_le p o (8 * a + r) (by omega)
    push_cast at this
    exact this
  have hSl : (Nat.log p S : ℝ) ≤ Real.logb p (8 * a + r) := by
    have := nlog_le p S (8 * a + r) (by omega)
    push_cast at this
    exact this
  have h1 := vfact_le p e
  have h2 := legendre' p o
  have h3 := legendre' p S
  have h4 := vchoose_le p (z + e) e
  have hceil := Nat.ceil_lt_add_one hκ0
  have hSoe : ((S + o - e : ℕ) : ℝ) = (S : ℝ) + o - e := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hsplit : (e : ℝ) / ((p : ℝ) - 1) + ((S : ℝ) + o - e) / ((p : ℝ) - 1) =
      (S : ℝ) / ((p : ℝ) - 1) + (o : ℝ) / ((p : ℝ) - 1) := by
    rw [← add_div, ← add_div]
    congr 1
    ring
  rw [hSoe]
  push_cast
  linarith

end Formalism.GM.MeanGammaLemmas

namespace Formalism.GM.MeanGammaLemmas
open Polynomial Finset Formalism.GM.M

lemma sum_trunc {F : Type} [Field F] (D0 del : ℕ) (h : D0 ≤ del) (g : ℕ → F) :
    ∑ k ∈ range (del + 1), (if k ≤ D0 then g k else 0) = ∑ k ∈ range (D0 + 1), g k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma poly_eq_of_eval (p : ℕ) [Fact p.Prime] (Q P : ℚ_[p][X]) (S : ℕ) (a : ℚ_[p])
    (h : ∀ n : ℕ, S ≤ n → Q.eval (n : ℚ_[p]) = a * P.eval (n : ℚ_[p])) : Q = C a * P := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n + S : ℕ) : ℚ_[p])) ?_ ?_
  · intro x y hxy
    have := Nat.cast_injective hxy
    omega
  · intro n
    simp only [Set.mem_setOf_eq, eval_mul, eval_C]
    exact h _ (by omega)

lemma entry_deg (hDeg : GamDeg) {p : ℕ} [Fact p.Prime] {K r : ℕ} (LLw : Letters (K + 1)) (ρ : Fin r)
    (z e e' : ℕ) (f f' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hr : 1 ≤ r)
    (hv : LLw.vec (Fin.last K) = true) (hf : f ∈ Pol p r LLw) (hf' : f' ∈ Pol p r LLw)
    (he : HasOrder (Fin.last K, ρ) e f) (he' : HasOrder (Fin.last K, ρ) e' f')
    (Q : ℚ_[p][X]) (a : ℚ_[p])
    (hQ : ∀ n : ℕ, LLw.total ≤ n → Q.eval (n : ℚ_[p]) = a * tieGam p LLw ρ z n f f') :
    Q.natDegree ≤ LLw.total + LLw.deg (Fin.last K) - max e e' := by
  obtain ⟨P, hP, hPe⟩ := hDeg p K r LLw ρ z e e' f f' hr hv hf hf' he he'
  have hQP : Q = C a * P := poly_eq_of_eval p Q P LLw.total a (fun n hn => by rw [hQ n hn, hPe n hn])
  rw [hQP]
  exact (natDegree_C_mul_le a P).trans hP

lemma entry_lead (hLead : GamLead) {p : ℕ} [Fact p.Prime] {K r : ℕ} (LLw : Letters (K + 1)) (ρ : Fin r)
    (z e : ℕ) (f f' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hr : 1 ≤ r)
    (hv : LLw.vec (Fin.last K) = true) (hf : f ∈ Pol p r LLw) (hf' : f' ∈ Pol p r LLw)
    (he : HasOrder (Fin.last K, ρ) e f) (he' : HasOrder (Fin.last K, ρ) e f')
    (Q : ℚ_[p][X]) (a : ℚ_[p]) (ha : a ≠ 0)
    (hQ : ∀ n : ℕ, LLw.total ≤ n → Q.eval (n : ℚ_[p]) = a * tieGam p LLw ρ z n f f') :
    Q.coeff (LLw.total + LLw.deg (Fin.last K) - e) =
      a * (((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) *
        fock p (initPart (Fin.last K, ρ) e f) (initPart (Fin.last K, ρ) e f') /
        ((((LLw.deg (Fin.last K)).factorial * LLw.total.factorial : ℕ) : ℚ_[p]) *
          ∏ i, ((LLw.deg i).factorial : ℚ_[p]))) := by
  have hP : ∀ n : ℕ, LLw.total ≤ n → tieGam p LLw ρ z n f f' = (C a⁻¹ * Q).eval (n : ℚ_[p]) := by
    intro n hn
    rw [eval_mul, eval_C, hQ n hn, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  have h := hLead p K r LLw ρ z e f f' (C a⁻¹ * Q) hr hv hf hf' he he' hP
  rw [coeff_C_mul] at h
  rw [← h, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]

lemma split_det (p : ℕ) [Fact p.Prime] {n : ℕ} (Aq : Matrix (Fin n) (Fin n) ℚ_[p][X]) :
    (Aq.map (Polynomial.map (algebraMap ℚ_[p] (PadicAlgCl p)))).det =
      (Aq.det).map (algebraMap ℚ_[p] (PadicAlgCl p)) := by
  have h := RingHom.map_det (Polynomial.mapRingHom (algebraMap ℚ_[p] (PadicAlgCl p))) Aq
  simpa using h.symm

lemma splits_form {L : Type} [Field L] [IsAlgClosed L] (Dk : L[X]) :
    Dk = C Dk.leadingCoeff * (Dk.roots.map (fun ζ => X - C ζ)).prod ∧ Dk.roots.card = Dk.natDegree := by
  have hc : Multiset.card Dk.roots = Dk.natDegree := splits_iff_card_roots.mp (IsAlgClosed.splits Dk)
  exact ⟨(C_leadingCoeff_mul_prod_multiset_X_sub_C hc).symm, hc⟩

end Formalism.GM.MeanGammaLemmas

namespace Formalism.GM.MeanGammaLemmas
open Polynomial Finset Formalism.GM.M

noncomputable def betaT (p : ℕ) [Fact p.Prime] (m z o S e : ℕ) : ℚ_[p] :=
  (p : ℚ_[p]) ^ m * ((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) / ((o.factorial * S.factorial : ℕ) : ℚ_[p])

noncomputable def gramT (p : ℕ) [Fact p.Prime] {K r n : ℕ} (LLw : Letters (K + 1)) (ρ : Fin r)
    (f : Fin n → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (ord : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℚ_[p] :=
  Matrix.of fun x y => fock p (initPart (Fin.last K, ρ) (ord x) (f x)) (initPart (Fin.last K, ρ) (ord x) (f y)) /
    ∏ i, ((LLw.deg i).factorial : ℚ_[p])

noncomputable def coefT (p : ℕ) [Fact p.Prime] {n : ℕ} (D0 m : ℕ) (cc : Fin n → Fin n → ℕ → ℤ_[p]) :
    Fin n → Fin n → ℕ → ℚ_[p] :=
  fun x y k => if k ≤ D0 then (p : ℚ_[p]) ^ m * (cc x y k : ℚ_[p]) else 0

lemma betaT_ne_zero (p : ℕ) [hp : Fact p.Prime] (m z o S e : ℕ) : betaT p m z o S e ≠ 0 := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hA : e.factorial * (z + e).choose e ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos (Nat.le_add_left e z)).ne'
  have hB : o.factorial * S.factorial ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  simp only [betaT]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hp0) (Nat.cast_ne_zero.mpr hA)) (Nat.cast_ne_zero.mpr hB)

lemma lead_part (hDeg : GamDeg) (hLead : GamLead) {p : ℕ} [hp : Fact p.Prime] {K r : ℕ} [NeZero r]
    (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (z : ℕ)
    (w : Fin r → ℤ) (n₀ : ℕ) (f : Fin n₀ → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (ord : Fin n₀ → ℕ)
    (κ : ℝ) (m cI : ℕ) (cc : Fin n₀ → Fin n₀ → ℕ → ℤ_[p]) (hr1 : 1 ≤ r) (hv : LLw.vec (Fin.last K) = true)
    (hli : LinearIndependent ℤ_[p] f) (hspan : Submodule.span ℤ_[p] (Set.range f) = MMwZ p LLw J M ρ w)
    (hord : ∀ b, HasOrder (Fin.last K, ρ) (ord b) (f b))
    (hfil : ∀ e, Submodule.span ℤ_[p] (f '' {b | e ≤ ord b}) = FilE p LLw J M ρ w (Fin.last K, ρ) e)
    (hL4 : GramDeterminantGradedHypothesis p LLw J M ρ κ)
    (hcc : ∀ x y (n : ℕ), LLw.total ≤ n →
      ((p : ℚ_[p]) ^ cI) * tieGam p LLw ρ z n (f x) (f y) =
        ∑ i ∈ range (LLw.total + LLw.deg (Fin.last K) + 1), (cc x y i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p])) :
    (∀ x y (n : ℕ), LLw.total ≤ n →
      ((binMatK ℚ_[p] (2 * LLw.total) (coefT p (LLw.total + LLw.deg (Fin.last K)) m cc)) x y).eval (n : ℚ_[p]) =
        (p : ℚ_[p]) ^ (m + cI) * tieGam p LLw ρ z n (f x) (f y)) ∧
    (binMatK ℚ_[p] (2 * LLw.total) (coefT p (LLw.total + LLw.deg (Fin.last K)) m cc)).det.natDegree =
      ∑ b, (LLw.total + LLw.deg (Fin.last K) - ord b) ∧
    ∏ b, (‖betaT p (m + cI) z (LLw.deg (Fin.last K)) LLw.total (ord b)‖ * (p : ℝ) ^ (-κ)) ≤
      ‖(binMatK ℚ_[p] (2 * LLw.total) (coefT p (LLw.total + LLw.deg (Fin.last K)) m cc)).det.leadingCoeff‖ ∧
    (∀ b, ord b ≤ LLw.deg (Fin.last K)) ∧ LLw.deg (Fin.last K) ≤ LLw.total := by
  classical
  have hmem : ∀ b, f b ∈ MMwZ p LLw J M ρ w := fun b => hspan ▸ Submodule.subset_span ⟨b, rfl⟩
  have hPol : ∀ b, f b ∈ Pol p r LLw := fun b =>
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp
      (Submodule.mem_inf.mp (hmem b)).1).1).1).1
  have hoS : LLw.deg (Fin.last K) ≤ LLw.total :=
    Finset.single_le_sum (f := LLw.deg) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  have hord_le : ∀ b, ord b ≤ LLw.deg (Fin.last K) := by
    intro b
    obtain ⟨mm, hm, hme⟩ := (hord b).2
    have hmd : MultiDeg LLw mm := ((MvPolynomial.mem_restrictSupport_iff _).mp (hPol b)) hm
    have := hmd (Fin.last K)
    rw [← this, ← hme]
    exact Finset.single_le_sum (f := fun c => mm (Fin.last K, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ρ)
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set S := LLw.total with hSdef
  set o := LLw.deg (Fin.last K) with hodef
  set Aq := binMatK ℚ_[p] (2 * S) (coefT p (S + o) m cc) with hAqdef

  have hAeval : ∀ x y (n : ℕ), S ≤ n → (Aq x y).eval (n : ℚ_[p]) =
      (p : ℚ_[p]) ^ (m + cI) * tieGam p LLw ρ z n (f x) (f y) := by
    intro x y n hn
    rw [hAqdef, binMatK_eval_nat]
    simp only [coefT, ite_mul, zero_mul]
    rw [sum_trunc (S + o) (2 * S) (by omega)]
    simp only [mul_assoc]
    rw [← Finset.mul_sum, ← hcc x y n hn, pow_add, mul_assoc]

  have hAdeg : ∀ x y, (Aq x y).natDegree + max (ord x) (ord y) ≤ S + o := by
    intro x y
    have := entry_deg hDeg LLw ρ z (ord x) (ord y) (f x) (f y) hr1 hv (hPol x) (hPol y) (hord x) (hord y)
      (Aq x y) _ (hAeval x y)
    have h1 := hord_le x; have h2 := hord_le y
    have : max (ord x) (ord y) ≤ o := max_le h1 h2
    omega

  have hAtop : ∀ x y, ord x = ord y → (Aq x y).coeff (S + o - ord x) =
      betaT p (m + cI) z o S (ord x) * gramT p LLw ρ f ord x y := by
    intro x y hxy
    have hy : HasOrder (Fin.last K, ρ) (ord x) (f y) := hxy ▸ hord y
    rw [entry_lead hLead LLw ρ z (ord x) (f x) (f y) hr1 hv (hPol x) (hPol y) (hord x) hy (Aq x y) _
      (pow_ne_zero _ hp0) (hAeval x y)]
    simp only [betaT, gramT, Matrix.of_apply]
    push_cast
    ring
  obtain ⟨hdeg1, hcoef, hlead⟩ := Formalism.GM.Top.detBlockLead ℚ_[p] n₀ Aq (S + o) ord
    (fun i => (hord_le i).trans (by omega)) hAdeg
  set B := Matrix.of fun i j => if ord i = ord j then (Aq i j).coeff (S + o - ord i) else 0 with hBdef
  have hB : ∀ i j, B i j = if ord i = ord j then betaT p (m + cI) z o S (ord i) * gramT p LLw ρ f ord i j
      else 0 := by
    intro i j
    simp only [hBdef, Matrix.of_apply]
    split_ifs with h
    · exact hAtop i j h
    · rfl

  have hstep : ∀ e x, x ∈ FilE p LLw J M ρ w (Fin.last K, ρ) e → initPart (Fin.last K, ρ) e x = 0 →
      x ∈ FilE p LLw J M ρ w (Fin.last K, ρ) (e + 1) := by
    intro e x hx h0
    have hx' := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨hx'.1, ?_⟩
    rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff]
    have h2 := hx'.2
    rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at h2
    intro mm hmm
    have h3 : e ≤ mm (Fin.last K, ρ) := h2 hmm
    show e + 1 ≤ mm (Fin.last K, ρ)
    rcases Nat.lt_or_eq_of_le h3 with h | h
    · exact h
    · exfalso
      have hc := congrArg (MvPolynomial.coeff mm) h0
      rw [coeff_initPart, if_pos h.symm, MvPolynomial.coeff_zero] at hc
      exact (MvPolynomial.mem_support_iff.mp hmm) hc

  have hGblk : ∀ a', ((p : ℝ) ^ (-κ)) ^ (Fintype.card {b // ord b = a'}) ≤
      ‖((gramT p LLw ρ f ord).toSquareBlock ord a').det‖ := by
    intro a'
    set k := Fintype.card {b // ord b = a'}
    let σe : {b // ord b = a'} ≃ Fin k := Fintype.equivFin _
    let g : Fin k → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
      fun i => initPart (Fin.last K, ρ) a' (f (σe.symm i))
    obtain ⟨hli', hsp'⟩ := init_basis f ord (Fin.last K, ρ) (FilE p LLw J M ρ w (Fin.last K, ρ)) hli hord hfil
      hstep a'
    have hg_li : LinearIndependent ℤ_[p] g := by
      have h0 : LinearIndependent ℤ_[p] (fun b : {b // ord b = a'} => initPart (Fin.last K, ρ) a' (f b)) := hli'
      exact h0.comp σe.symm σe.symm.injective
    have hg_sp : Submodule.span ℤ_[p] (Set.range g) = grLat p LLw J M ρ w (Fin.last K, ρ) a' := by
      unfold grLat
      rw [← hsp']
      congr 1
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨(σe.symm i : Fin n₀), (σe.symm i).2, rfl⟩
      · rintro ⟨b, hb, rfl⟩
        refine ⟨σe ⟨b, hb⟩, ?_⟩
        simp [g]
    have h4 := hL4 w a' k g hg_li hg_sp
    have hmat : (Matrix.of fun i j => fock p (g i) (g j) / ∏ i, ((LLw.deg i).factorial : ℚ_[p])) =
        Matrix.reindex σe σe ((gramT p LLw ρ f ord).toSquareBlock ord a') := by
      ext i j
      simp only [Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.toSquareBlock_def,
        gramT, g]
      rw [(σe.symm i).2]
    rw [hmat, Matrix.det_reindex_self] at h4
    have hp0' : (0 : ℝ) ≤ p := by positivity
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0']
    convert h4 using 2
    ring
  have hBnorm := det_block_norm B (gramT p LLw ρ f ord) ord (betaT p (m + cI) z o S) ((p : ℝ) ^ (-κ))
    (by positivity) hB hGblk
  have hprod_pos : 0 < ∏ b, (‖betaT p (m + cI) z o S (ord b)‖ * (p : ℝ) ^ (-κ)) := by
    apply Finset.prod_pos
    intro b _
    have hpr : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    exact mul_pos (norm_pos_iff.mpr (betaT_ne_zero p _ _ _ _ _)) (Real.rpow_pos_of_pos hpr _)
  have hBne : B.det ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hprod_pos hBnorm)
  obtain ⟨hnat, hlc⟩ := hlead hBne
  refine ⟨hAeval, hnat, ?_, hord_le, hoS⟩
  rw [hlc]
  exact hBnorm

end Formalism.GM.MeanGammaLemmas

namespace Formalism.GM.MeanGammaLemmas
open Polynomial Finset Formalism.GM.M

lemma lead_bound (p : ℕ) [hp : Fact p.Prime] {n : ℕ} (β : Fin n → ℝ) (dgs : Fin n → ℕ) (κ La Lnorm : ℝ)
    (hβ : ∀ b, 0 < β b) (hprod : ∏ b, (β b * (p : ℝ) ^ (-κ)) ≤ Lnorm)
    (hrow : ∀ b, -Real.logb p (β b) + (dgs b : ℝ) / ((p : ℝ) - 1) + κ ≤ La) :
    -Real.logb p Lnorm + ((∑ b, dgs b : ℕ) : ℝ) / ((p : ℝ) - 1) ≤ n * La := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hpos : 0 < ∏ b, (β b * (p : ℝ) ^ (-κ)) :=
    Finset.prod_pos (fun b _ => mul_pos (hβ b) (Real.rpow_pos_of_pos hp0 _))
  have h1 : Real.logb p (∏ b, (β b * (p : ℝ) ^ (-κ))) ≤ Real.logb p Lnorm :=
    Real.logb_le_logb_of_le hp1 hpos hprod
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have h2 : Real.logb p (∏ b, (β b * (p : ℝ) ^ (-κ))) = ∑ b, (Real.logb p (β b) - κ) := by
    simp only [Real.logb]
    rw [Real.log_prod (fun b _ => (mul_pos (hβ b) (Real.rpow_pos_of_pos hp0 _)).ne'), Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    rw [Real.log_mul (hβ b).ne' (Real.rpow_pos_of_pos hp0 _).ne', Real.log_rpow hp0, add_div,
      mul_div_assoc, div_self hlogp.ne']
    ring
  have h3 : ∑ b, (-Real.logb p (β b) + (dgs b : ℝ) / ((p : ℝ) - 1) + κ) ≤ n * La := by
    calc _ ≤ ∑ _b : Fin n, La := Finset.sum_le_sum (fun b _ => hrow b)
      _ = n * La := by simp
  have h4 : ∑ b, (-Real.logb p (β b) + (dgs b : ℝ) / ((p : ℝ) - 1) + κ) =
      -(∑ b, (Real.logb p (β b) - κ)) + ((∑ b, dgs b : ℕ) : ℝ) / ((p : ℝ) - 1) := by
    rw [Nat.cast_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  linarith

end Formalism.GM.MeanGammaLemmas

namespace Formalism.GM
open Polynomial Finset Formalism.GM.M Formalism.GM.MeanGammaLemmas

theorem meanGam_of (hDeg : GamDeg) (hLead : GamLead) (hInt : GamInt) (hW : Formalism.GM.WindowFullAP) :
    MeanGam := by
  obtain ⟨C, hC⟩ := hInt
  refine ⟨(C : ℝ) + 3, by positivity, ?_⟩
  intro p hp K r hr LLw q J M ρ z w n₀ f ord s d Yw a E κ U V dg hρ hr2 hv hli hspan hord hfil hE hYw hd
    hcop hSs hdeg hsY hz hκ hL4 hsmith
  classical
  have hr1 : 1 ≤ r := by omega
  have hmem : ∀ b, f b ∈ MMwZ p LLw J M ρ w := fun b => hspan ▸ Submodule.subset_span ⟨b, rfl⟩
  have hPol : ∀ b, f b ∈ Pol p r LLw := fun b =>
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp
      (Submodule.mem_inf.mp (hmem b)).1).1).1).1
  have hPolZ : ∀ b, f b ∈ PolZ p r LLw := fun b =>
    Submodule.mem_inf.mpr ⟨hPol b, (Submodule.mem_inf.mp (hmem b)).2⟩
  have hCI := fun x y => hC p K r LLw ρ z (f x) (f y) hr1 hv (hPolZ x) (hPolZ y)
  choose cc hcc using hCI
  set S := LLw.total with hSdef
  set o := LLw.deg (Fin.last K) with hodef
  set cI := C * (K + 3) * r ^ 2 * (Nat.log p (S + o + r) + 1) with hcIdef
  obtain ⟨hAeval, hnat, hlead, hord_le, hoS⟩ := lead_part hDeg hLead LLw J M ρ z w n₀ f ord κ ⌈κ⌉₊ cI cc
    hr1 hv hli hspan hord hfil hL4 (fun x y n hn => hcc x y n hn)
  set Aq := binMatK ℚ_[p] (2 * S) (coefT p (S + o) ⌈κ⌉₊ cc) with hAqdef

  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hlg0 : 0 ≤ Real.logb p (8 * a + r) := by
    apply Real.logb_nonneg hp1
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    have : (0 : ℝ) ≤ a := by positivity
    linarith
  have hlgdef : lgV2 p a r = Real.logb p (8 * a + r) + 1 := rfl
  have h12 : (12 : ℝ) ≤ ((K : ℝ) + 3) * (r : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    have : (0 : ℝ) ≤ K := by positivity
    nlinarith
  have hκ12 : 12 * (Real.logb p (8 * a + r) + 1) ≤ κ := by
    rw [hlgdef] at hκ
    nlinarith
  have hκ0 : 0 ≤ κ := by linarith
  have hS2a : S ≤ 2 * a := le_trans hSs (le_trans (Nat.le_add_right _ _) hsY)
  have ho2a : o ≤ 2 * a := hdeg _
  have hcI : (cI : ℝ) ≤ C * κ := by
    have hl := nlog_le p (S + o + r) (8 * a + r) (by omega)
    have hcast : (((8 * a + r : ℕ)) : ℝ) = 8 * (a : ℝ) + r := by push_cast; ring
    rw [hcast] at hl
    have hC0 : (0 : ℝ) ≤ C := by positivity
    have hK0 : (0 : ℝ) ≤ ((K : ℝ) + 3) * (r : ℝ) ^ 2 := by positivity
    calc (cI : ℝ) = (C : ℝ) * ((((K : ℝ) + 3) * (r : ℝ) ^ 2) * ((Nat.log p (S + o + r) : ℝ) + 1)) := by
          rw [hcIdef]; push_cast; ring
      _ ≤ (C : ℝ) * ((((K : ℝ) + 3) * (r : ℝ) ^ 2) * lgV2 p a r) := by
          rw [hlgdef]; gcongr
      _ ≤ C * κ := by gcongr
  have hLB := lead_bound p (fun b => ‖betaT p (⌈κ⌉₊ + cI) z o S (ord b)‖) (fun b => S + o - ord b) κ
    ((C + 3) * κ) ‖Aq.det.leadingCoeff‖ (fun b => norm_pos_iff.mpr (betaT_ne_zero p _ _ _ _ _)) hlead
    (fun b => per_row p a r S o z (ord b) cI κ C (hord_le b) ho2a hS2a hz hr1 hκ12 hcI)

  set alg := algebraMap ℚ_[p] (PadicAlgCl p) with halg
  set c' : Fin n₀ → Fin n₀ → ℕ → PadicAlgCl p := fun i j k => alg (coefT p (S + o) ⌈κ⌉₊ cc i j k) with hc'
  have hAK : binMatK (PadicAlgCl p) (2 * S) c' = Aq.map (Polynomial.map alg) :=
    binMatK_map ℚ_[p] (PadicAlgCl p) alg (2 * S) _
  have hDk : (binMatK (PadicAlgCl p) (2 * S) c').det = Aq.det.map alg := by
    rw [hAK]; exact split_det p Aq
  obtain ⟨hsplit, hcard⟩ := splits_form (binMatK (PadicAlgCl p) (2 * S) c').det
  have hlc : (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff = alg Aq.det.leadingCoeff := by
    rw [hDk, leadingCoeff_map]
  have hnd : (binMatK (PadicAlgCl p) (2 * S) c').det.natDegree = Aq.det.natDegree := by
    rw [hDk, natDegree_map]
  have hlcnorm : ‖(binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff‖ = ‖Aq.det.leadingCoeff‖ := by
    rw [hlc, halg, norm_algebraMap']
  have hprod_pos : 0 < ∏ b, (‖betaT p (⌈κ⌉₊ + cI) z o S (ord b)‖ * (p : ℝ) ^ (-κ)) := by
    apply Finset.prod_pos
    intro b _
    exact mul_pos (norm_pos_iff.mpr (betaT_ne_zero p _ _ _ _ _)) (Real.rpow_pos_of_pos (by linarith) _)
  have hleadne : (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff ≠ 0 := by
    rw [← norm_pos_iff, hlcnorm]; exact lt_of_lt_of_le hprod_pos hlead
  have hLB' : -Real.logb p ‖(binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff‖ +
      ((binMatK (PadicAlgCl p) (2 * S) c').det.roots.card : ℝ) / ((p : ℝ) - 1) ≤ (n₀ : ℝ) * ((C + 3) * κ) := by
    rw [hlcnorm, hcard, hnd, hnat]; exact hLB
  have hc'norm : ∀ i j k, ‖c' i j k‖ ≤ 1 := by
    intro i j k
    simp only [hc', halg, norm_algebraMap', coefT]
    split_ifs
    · rw [norm_mul, norm_pow, Padic.norm_p]
      have h1 : ‖((cc i j k : ℤ_[p]) : ℚ_[p])‖ ≤ 1 := by
        rw [← PadicInt.norm_def]; exact PadicInt.norm_le_one _
      have h2 : ((p : ℝ)⁻¹) ^ ⌈κ⌉₊ ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1.le)
      calc ((p : ℝ)⁻¹) ^ ⌈κ⌉₊ * ‖((cc i j k : ℤ_[p]) : ℚ_[p])‖ ≤ 1 * 1 :=
            mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · simp

  set h := Nat.clog p (8 * a + r) with hhdef
  have hph : 8 * a + r ≤ p ^ h := Nat.le_pow_clog hp.out.one_lt _
  have hhl : (h : ℝ) ≤ lgV2 p a r := by
    rw [hlgdef]
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · rw [h0]; push_cast; linarith
    · have h1 := Nat.pow_pred_clog_lt_self hp.out.one_lt (x := 8 * a + r) (by omega)
      rw [← hhdef, Nat.pred_eq_sub_one] at h1
      have h2 : h - 1 ≤ Nat.log p (8 * a + r) := Nat.le_log_of_pow_le hp.out.one_lt h1.le
      have h3 := nlog_le p (8 * a + r) (8 * a + r) le_rfl
      have hcast : (((8 * a + r : ℕ)) : ℝ) = 8 * (a : ℝ) + r := by push_cast; ring
      rw [hcast] at h3
      have h4 : ((h - 1 : ℕ) : ℝ) ≤ (Nat.log p (8 * a + r) : ℝ) := by exact_mod_cast h2
      have h5 : (h : ℝ) = ((h - 1 : ℕ) : ℝ) + 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      linarith
  have hYle : Yw ≤ 2 * a + 1 := by
    have h1 := Nat.le_mul_of_pos_left (Yw - 1) hd
    have h2 : d * (Yw - 1) ≤ 2 * a := le_trans (Nat.le_add_left _ _) hsY
    omega
  have hYh : Yw ≤ p ^ h := by omega
  have hdelh : 2 * S ≤ p ^ h := by omega

  set idx : ℤ → ℕ := fun t => ((t - (s : ℤ)) / (d : ℤ)).toNat with hidxdef
  have hidx : ∀ j : ℕ, idx (progr (s : ℤ) (d : ℤ) j) = j := by
    intro j
    simp only [hidxdef, progr, add_sub_cancel_left]
    rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hd.ne')]
    simp
  set U' : ℤ → Matrix (Fin n₀) (Fin n₀) (PadicAlgCl p) := fun t => (U (idx t)).map alg with hU'
  set V' : ℤ → Matrix (Fin n₀) (Fin n₀) (PadicAlgCl p) := fun t => (V (idx t)).map alg with hV'
  set dg' : ℤ → Fin n₀ → PadicAlgCl p := fun t b => alg ((p : ℚ_[p]) ^ cI * dg (idx t) b) with hdg'
  have hsm : ∀ j ∈ range Yw, (∀ x y, ‖U' (progr (s : ℤ) (d : ℤ) j) x y‖ ≤ 1) ∧
      (∀ x y, ‖V' (progr (s : ℤ) (d : ℤ) j) x y‖ ≤ 1) ∧
      ‖(U' (progr (s : ℤ) (d : ℤ) j)).det‖ = 1 ∧ ‖(V' (progr (s : ℤ) (d : ℤ) j)).det‖ = 1 ∧
      (binMatK (PadicAlgCl p) (2 * S) c').map (Polynomial.eval ((progr (s : ℤ) (d : ℤ) j : ℤ) : PadicAlgCl p)) =
        U' (progr (s : ℤ) (d : ℤ) j) * Matrix.diagonal (dg' (progr (s : ℤ) (d : ℤ) j)) *
          V' (progr (s : ℤ) (d : ℤ) j) := by
    intro j hj
    obtain ⟨hU1, hV1, hUd, hVd, hfac⟩ := hsmith j (Finset.mem_range.mp hj)
    simp only [hU', hV', hdg', hidx]
    refine ⟨fun x y => ?_, fun x y => ?_, ?_, ?_, ?_⟩
    · rw [Matrix.map_apply, halg, norm_algebraMap']; exact hU1 x y
    · rw [Matrix.map_apply, halg, norm_algebraMap']; exact hV1 x y
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, halg, norm_algebraMap']; exact hUd
    · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, halg, norm_algebraMap']; exact hVd
    · rw [hAK]
      ext x y
      have hpt : ((progr (s : ℤ) (d : ℤ) j : ℤ) : PadicAlgCl p) = ((s + d * j : ℕ) : PadicAlgCl p) := by
        simp [progr]
      have hfe := congrFun (congrFun hfac x) y
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.mul_diagonal] at hfe
      simp only [Matrix.map_apply, hpt, eval_natCast_map, Matrix.mul_apply, Matrix.mul_diagonal]
      rw [hAeval x y (s + d * j) (le_trans hSs (Nat.le_add_right _ _)), pow_add, mul_comm ((p : ℚ_[p]) ^ ⌈κ⌉₊),
        mul_assoc, hfe, Finset.mul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp [Matrix.diagonal_apply, map_sum]
      ring
  have hcop' : IsCoprime (d : ℤ) (p : ℤ) := hcop
  have hE0 : (0 : ℝ) < E := by linarith
  have key := hW p (PadicAlgCl p) n₀ (2 * S) h E c' (binMatK (PadicAlgCl p) (2 * S) c').det.leadingCoeff
    (binMatK (PadicAlgCl p) (2 * S) c').det.roots (s : ℤ) (d : ℤ) Yw ((C + 3) * κ) U' V' dg' hcop'
    (by omega) hYh hdelh hE0 hleadne hc'norm hsplit hsm hLB'

  have hcnt : ∀ j ∈ range Yw, ((univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E))).card : ℝ) ≤
      ((univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E))).card : ℝ) := by
    intro j _
    have hsub : univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E)) ⊆
        univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E)) := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      simp only [hdg', hidx, halg, norm_algebraMap', norm_mul, norm_pow, Padic.norm_p]
      have h2 : ((p : ℝ)⁻¹) ^ cI ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1.le)
      calc ((p : ℝ)⁻¹) ^ cI * ‖dg j b‖ ≤ 1 * ‖dg j b‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ ≤ (p : ℝ) ^ (-E) := by rw [one_mul]; exact hb.le
    exact_mod_cast Finset.card_le_card hsub
  have hYpos : (0 : ℝ) < Yw := by exact_mod_cast hYw
  calc (∑ j ∈ range Yw, ((univ.filter (fun b => ‖dg j b‖ < (p : ℝ) ^ (-E))).card : ℝ)) / Yw
      ≤ (∑ j ∈ range Yw, ((univ.filter (fun b => ‖dg' (progr (s : ℤ) (d : ℤ) j) b‖ ≤ (p : ℝ) ^ (-E))).card : ℝ)) /
          Yw := div_le_div_of_nonneg_right (Finset.sum_le_sum hcnt) hYpos.le
    _ ≤ (n₀ : ℝ) * (((2 * S : ℕ) : ℝ) / Yw + ((C + 3) * κ + ((2 * S : ℕ) : ℝ) * h / Yw) / E) := key
    _ ≤ n₀ * (2 * (LLw.total : ℝ) / Yw + (((C : ℝ) + 3) * κ + 2 * (LLw.total : ℝ) * lgV2 p a r / Yw) / E) := by
      rw [← hSdef]
      push_cast
      have h1 : 2 * (S : ℝ) * h / Yw ≤ 2 * (S : ℝ) * lgV2 p a r / Yw := by
        apply div_le_div_of_nonneg_right _ hYpos.le
        exact mul_le_mul_of_nonneg_left hhl (by positivity)
      have h2 : ((C : ℝ) + 3) * κ + 2 * (S : ℝ) * h / Yw ≤ ((C : ℝ) + 3) * κ + 2 * (S : ℝ) * lgV2 p a r / Yw := by
        linarith
      have h3 := div_le_div_of_nonneg_right h2 hE0.le
      have hn0 : (0 : ℝ) ≤ n₀ := by positivity
      nlinarith

end Formalism.GM
