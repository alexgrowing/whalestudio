import Formalism.MahlerMeasure.GamInt
import Mathlib

namespace Formalism.GM.gammaIntegralityLemmas

open Finset Polynomial

variable {p : ℕ} [Fact p.Prime]

def IVP (p : ℕ) [Fact p.Prime] (D : ℕ) (g : ℕ → ℚ_[p]) : Prop :=
  (∃ P : Polynomial ℚ_[p], P.natDegree ≤ D ∧ ∀ m : ℕ, g m = P.eval (m : ℚ_[p])) ∧ ∀ m, ‖g m‖ ≤ 1

theorem norm_natCast_le_one' (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 := by
  have := Padic.norm_int_le_one (p := p) (n : ℤ)
  simpa using this

theorem norm_intCast_le_one' (n : ℤ) : ‖(n : ℚ_[p])‖ ≤ 1 :=
  Padic.norm_int_le_one n

theorem norm_sum_le_one {ι : Type} (s : Finset ι) (f : ι → ℚ_[p]) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖∑ i ∈ s, f i‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (Padic.nonarchimedean _ _).trans (max_le (h a (mem_insert_self _ _)) ?_)
    exact ih (fun i hi => h i (mem_insert_of_mem hi))

theorem IVP.mono {D D' : ℕ} {g : ℕ → ℚ_[p]} (h : IVP p D g) (hD : D ≤ D') : IVP p D' g := by
  obtain ⟨⟨P, hP, hPg⟩, hn⟩ := h
  exact ⟨⟨P, hP.trans hD, hPg⟩, hn⟩

theorem IVP.zero (D : ℕ) : IVP p D (fun _ => 0) :=
  ⟨⟨0, by simp, fun m => by simp⟩, fun m => by simp⟩

theorem IVP.add {D : ℕ} {g h : ℕ → ℚ_[p]} (hg : IVP p D g) (hh : IVP p D h) :
    IVP p D (fun m => g m + h m) := by
  obtain ⟨⟨P, hP, hPg⟩, hn⟩ := hg
  obtain ⟨⟨Q, hQ, hQh⟩, hn'⟩ := hh
  refine ⟨⟨P + Q, (natDegree_add_le _ _).trans (max_le hP hQ), fun m => by simp [hPg, hQh]⟩, fun m => ?_⟩
  exact (Padic.nonarchimedean _ _).trans (max_le (hn m) (hn' m))

theorem IVP.mul {D E : ℕ} {g h : ℕ → ℚ_[p]} (hg : IVP p D g) (hh : IVP p E h) :
    IVP p (D + E) (fun m => g m * h m) := by
  obtain ⟨⟨P, hP, hPg⟩, hn⟩ := hg
  obtain ⟨⟨Q, hQ, hQh⟩, hn'⟩ := hh
  refine ⟨⟨P * Q, (natDegree_mul_le).trans (add_le_add hP hQ), fun m => by simp [hPg, hQh]⟩, fun m => ?_⟩
  rw [norm_mul]
  exact mul_le_one₀ (hn m) (norm_nonneg _) (hn' m)

theorem IVP.smul {D : ℕ} {g : ℕ → ℚ_[p]} (q : ℚ_[p]) (hq : ‖q‖ ≤ 1) (hg : IVP p D g) :
    IVP p D (fun m => q * g m) := by
  obtain ⟨⟨P, hP, hPg⟩, hn⟩ := hg
  refine ⟨⟨Polynomial.C q * P, (natDegree_C_mul_le _ _).trans hP, fun m => by simp [hPg]⟩, fun m => ?_⟩
  rw [norm_mul]
  exact mul_le_one₀ hq (norm_nonneg _) (hn m)

theorem IVP.sum {ι : Type} {D : ℕ} (s : Finset ι) (g : ι → ℕ → ℚ_[p]) (h : ∀ i ∈ s, IVP p D (g i)) :
    IVP p D (fun m => ∑ i ∈ s, g i m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IVP.zero (p := p) D
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact IVP.add (h a (mem_insert_self _ _)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

theorem IVP.congr {D : ℕ} {g h : ℕ → ℚ_[p]} (hg : IVP p D g) (e : ∀ m, g m = h m) : IVP p D h := by
  have : g = h := funext e
  rw [← this]; exact hg

theorem IVP.choose_add (c k : ℕ) : IVP p k (fun m => (((m + c).choose k : ℕ) : ℚ_[p])) := by
  refine ⟨⟨Polynomial.C ((k.factorial : ℚ_[p])⁻¹) * (descPochhammer ℚ_[p] k).comp (X + Polynomial.C (c : ℚ_[p])),
    ?_, fun m => ?_⟩, fun m => norm_natCast_le_one' _⟩
  · refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_comp_le).trans ?_
    rw [descPochhammer_natDegree]
    have : (X + Polynomial.C (c : ℚ_[p])).natDegree ≤ 1 := by
      refine (natDegree_add_le _ _).trans ?_; simp
    nlinarith
  · simp only [eval_mul, eval_C, eval_comp, eval_add, eval_X]
    have h1 : ((m : ℚ_[p]) + c) = ((m + c : ℕ) : ℚ_[p]) := by push_cast; ring
    rw [h1, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    have : (k.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    push_cast
    field_simp

theorem IVP.newton {D : ℕ} {g : ℕ → ℚ_[p]} (hg : IVP p D g) :
    ∃ c : ℕ → ℤ_[p], ∀ m, g m = ∑ k ∈ range (D + 1), (c k : ℚ_[p]) * ((m.choose k : ℕ) : ℚ_[p]) := by
  obtain ⟨⟨P, hP, hPg⟩, hn⟩ := hg
  set d : ℕ → ℚ_[p] := fun k => (fwdDiff 1)^[k] g 0 with hd
  have hd_sum : ∀ k, d k = ∑ i ∈ range (k + 1), ((-1 : ℤ) ^ (k - i) * k.choose i) • g i := by
    intro k
    simp only [hd, fwdDiff_iter_eq_sum_shift, zero_add, smul_eq_mul, mul_one]
  have hd_norm : ∀ k, ‖d k‖ ≤ 1 := by
    intro k
    rw [hd_sum]
    apply norm_sum_le_one
    intro i _
    rw [zsmul_eq_mul, norm_mul]
    exact mul_le_one₀ (by exact_mod_cast norm_intCast_le_one' _) (norm_nonneg _) (hn i)
  have hd_zero : ∀ k, D < k → d k = 0 := by
    intro k hk
    have h0 : (fwdDiff (1 : ℚ_[p]))^[k] P.eval 0 = 0 := by
      rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (by omega)]; rfl
    rw [fwdDiff_iter_eq_sum_shift] at h0
    rw [hd_sum, ← h0]
    apply sum_congr rfl
    intro i _
    rw [hPg]; simp
  refine ⟨fun k => ⟨d k, hd_norm k⟩, fun m => ?_⟩
  have hN := shift_eq_sum_fwdDiff_iter (1 : ℕ) g m 0
  simp only [zero_add, smul_eq_mul, mul_one] at hN
  rw [hN]
  change ∑ k ∈ range (m + 1), m.choose k • d k = ∑ k ∈ range (D + 1), (d k : ℚ_[p]) * ((m.choose k : ℕ) : ℚ_[p])
  have e1 : ∑ k ∈ range (m + 1), m.choose k • d k =
      ∑ k ∈ range (m + 1 + (D + 1)), m.choose k • d k := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro k hk hk'
    simp only [mem_range] at hk hk'
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
  have e2 : ∑ k ∈ range (D + 1), d k * ((m.choose k : ℕ) : ℚ_[p]) =
      ∑ k ∈ range (m + 1 + (D + 1)), d k * ((m.choose k : ℕ) : ℚ_[p]) := by
    apply sum_subset (range_subset_range.mpr (by omega))
    intro k hk hk'
    simp only [mem_range] at hk hk'
    rw [hd_zero k (by omega)]; simp
  rw [e1, e2]
  apply sum_congr rfl
  intro k _
  rw [nsmul_eq_mul]; ring

theorem choose_sub_expand (D : ℕ) : ∀ S k : ℕ, k ≤ D → ∃ e : ℕ → ℤ, ∀ n : ℕ, S ≤ n →
    (((n - S).choose k : ℕ) : ℤ) = ∑ i ∈ range (D + 1), e i * ((n.choose i : ℕ) : ℤ) := by
  intro S
  induction S with
  | zero =>
    intro k hk
    refine ⟨fun i => if i = k then 1 else 0, fun n _ => ?_⟩
    simp only [Nat.sub_zero, ite_mul, one_mul, zero_mul]
    rw [sum_ite_eq']
    simp [show k < D + 1 by omega]
  | succ S ih =>
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun i => if i = 0 then 1 else 0, fun n _ => ?_⟩
      simp only [ite_mul, one_mul, zero_mul]
      rw [sum_ite_eq']
      simp
    | succ k ihk =>
      intro hk
      obtain ⟨e1, he1⟩ := ih (k + 1) hk
      obtain ⟨e2, he2⟩ := ihk (by omega)
      refine ⟨fun i => e1 i - e2 i, fun n hn => ?_⟩
      have hpas : (n - S).choose (k + 1) = (n - (S + 1)).choose k + (n - (S + 1)).choose (k + 1) := by
        have : n - S = (n - (S + 1)) + 1 := by omega
        rw [this, Nat.choose_succ_succ]
      have h1 := he1 n (by omega)
      have h2 := he2 n hn
      have : (((n - (S + 1)).choose (k + 1) : ℕ) : ℤ) =
          (((n - S).choose (k + 1) : ℕ) : ℤ) - (((n - (S + 1)).choose k : ℕ) : ℤ) := by
        rw [hpas]; push_cast; ring
      rw [this, h1, h2, ← sum_sub_distrib]
      apply sum_congr rfl; intro i _; ring

theorem IVP.toChoose {D S : ℕ} {g : ℕ → ℚ_[p]} (hg : IVP p D g) :
    ∃ c : ℕ → ℤ_[p], ∀ n, S ≤ n →
      g (n - S) = ∑ i ∈ range (D + 1), (c i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p]) := by
  obtain ⟨d, hd⟩ := hg.newton
  have hex : ∀ k, ∃ e : ℕ → ℤ, k ≤ D → ∀ n, S ≤ n →
      (((n - S).choose k : ℕ) : ℤ) = ∑ i ∈ range (D + 1), e i * ((n.choose i : ℕ) : ℤ) := by
    intro k
    by_cases hk : k ≤ D
    · obtain ⟨e, he⟩ := choose_sub_expand D S k hk
      exact ⟨e, fun _ => he⟩
    · exact ⟨fun _ => 0, fun h => absurd h hk⟩
  choose e he using hex
  refine ⟨fun i => ∑ k ∈ range (D + 1), d k * (e k i : ℤ_[p]), fun n hn => ?_⟩
  rw [hd]
  have : ∀ k ∈ range (D + 1), (d k : ℚ_[p]) * (((n - S).choose k : ℕ) : ℚ_[p]) =
      ∑ i ∈ range (D + 1), (d k : ℚ_[p]) * (e k i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p]) := by
    intro k hk
    have h := he k (by simpa [Nat.lt_succ_iff] using hk) n hn
    have h' : (((n - S).choose k : ℕ) : ℚ_[p]) = ∑ i ∈ range (D + 1), (e k i : ℚ_[p]) * ((n.choose i : ℕ) : ℚ_[p]) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ_[p])) h
    rw [h', mul_sum]
    apply sum_congr rfl; intro i _; ring
  rw [sum_congr rfl this, sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← sum_mul]
  congr 1
  rw [PadicInt.coe_sum]
  apply sum_congr rfl; intro k _
  rw [PadicInt.coe_mul, PadicInt.coe_intCast]

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM.gammaIntegralityLemmas

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

theorem vchoose_le {t k T B : ℕ} (ht : t ≤ T) (hB : Nat.log p T ≤ B) :
    padicValNat p (t.choose k) ≤ B := by
  rw [← Nat.factorization_def _ hp.out]
  exact Nat.factorization_choose_le_log.trans ((Nat.log_mono_right ht).trans hB)

theorem vfact_split {a b T B : ℕ} (h : a + b ≤ T) (hB : Nat.log p T ≤ B) :
    padicValNat p (a + b).factorial ≤ padicValNat p a.factorial + padicValNat p b.factorial + B := by
  have e := Nat.add_choose_mul_factorial_mul_factorial a b
  have h1 : padicValNat p (a + b).factorial =
      padicValNat p ((a + b).choose b) + padicValNat p a.factorial + padicValNat p b.factorial := by
    rw [← e, padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.factorial_pos _).ne') (Nat.factorial_pos _).ne',
      padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.factorial_pos _).ne']
  have := vchoose_le (p := p) (k := b) h hB
  omega

theorem vfact_sum {ι : Type} (s : Finset ι) (α : ι → ℕ) {T B : ℕ} (h : ∑ i ∈ s, α i ≤ T)
    (hB : Nat.log p T ≤ B) :
    padicValNat p (∑ i ∈ s, α i).factorial ≤ ∑ i ∈ s, padicValNat p (α i).factorial + s.card * B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha] at h ⊢
    rw [sum_insert ha, card_insert_of_notMem ha]
    have h1 := vfact_split (p := p) h hB
    have h2 := ih (by omega)
    nlinarith

theorem vdesc_ge (x a : ℕ) (ha : a ≤ x) :
    padicValNat p a.factorial ≤ padicValNat p (x.descFactorial a) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    padicValNat.mul (by positivity) (Nat.choose_pos ha).ne']
  omega

theorem norm_nat_eq (t : ℕ) (ht : t ≠ 0) : ‖(t : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p t : ℤ)) := by
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast ht), Padic.valuation_natCast]

theorem p_real_one_le : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le

theorem zpow_mono' {a b : ℤ} (h : a ≤ b) : (p : ℝ) ^ a ≤ (p : ℝ) ^ b :=
  zpow_le_zpow_right₀ p_real_one_le h

theorem zpow_pos' (a : ℤ) : (0 : ℝ) < (p : ℝ) ^ a :=
  zpow_pos (by exact_mod_cast hp.out.pos) a

theorem norm_fact (t : ℕ) : ‖(t.factorial : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p t.factorial : ℤ)) :=
  norm_nat_eq _ (Nat.factorial_pos t).ne'

theorem norm_desc_le (x a : ℕ) : ‖((x.descFactorial a : ℕ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(padicValNat p a.factorial : ℤ)) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, norm_mul, norm_fact]
  have h1 := norm_natCast_le_one' (p := p) (x.choose a)
  have h2 := zpow_pos' (p := p) (-(padicValNat p a.factorial : ℤ))
  nlinarith [norm_nonneg ((x.choose a : ℕ) : ℚ_[p])]

theorem norm_sum_le_bound {ι : Type} (s : Finset ι) (f : ι → ℚ_[p]) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ i ∈ s, ‖f i‖ ≤ K) : ‖∑ i ∈ s, f i‖ ≤ K := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hK
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (Padic.nonarchimedean _ _).trans (max_le (h a (mem_insert_self _ _)) ?_)
    exact ih (fun i hi => h i (mem_insert_of_mem hi))

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM.gammaIntegralityLemmas

open MvPolynomial Finset

variable {p : ℕ} [hp : Fact p.Prime]

section fockS
variable {σ : Type} [Fintype σ] [DecidableEq σ]

noncomputable def wf (m : σ →₀ ℕ) : ℚ_[p] := ∏ x, ((m x).factorial : ℚ_[p])

theorem prod_eq_wf (m : σ →₀ ℕ) : (m.prod fun _ k => (k.factorial : ℚ_[p])) = wf (p := p) m := by
  unfold wf; exact Finsupp.prod_fintype _ _ (by simp)

theorem wf_add_single (m : σ →₀ ℕ) (i : σ) :
    (wf (p := p) (m + Finsupp.single i 1)) = ((m i + 1 : ℕ) : ℚ_[p]) * wf m := by
  unfold wf
  have h : ∀ x : σ, (((m + Finsupp.single i 1 : σ →₀ ℕ) x).factorial : ℚ_[p]) =
      ((m x).factorial : ℚ_[p]) * (if x = i then ((m i + 1 : ℕ) : ℚ_[p]) else 1) := by
    intro x
    by_cases hx : x = i
    · subst hx; simp [Nat.factorial_succ]; ring
    · simp [hx, Finsupp.single_apply]
  rw [Finset.prod_congr rfl (fun x _ => h x), Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp [mul_comm]

theorem fock_def' (F G : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p F G = ∑ m ∈ F.support, F.coeff m * G.coeff m * wf m := by
  unfold Formalism.GM.M.fock
  exact Finset.sum_congr rfl (fun m _ => by rw [prod_eq_wf])

theorem fock_eq_sum (F G : MvPolynomial σ ℚ_[p]) (s : Finset (σ →₀ ℕ)) (h : F.support ⊆ s) :
    Formalism.GM.M.fock p F G = ∑ m ∈ s, F.coeff m * G.coeff m * wf m := by
  rw [fock_def']
  apply Finset.sum_subset h
  intro m _ hm
  rw [notMem_support_iff.mp hm]; ring

theorem fock_symm (F G : MvPolynomial σ ℚ_[p]) : Formalism.GM.M.fock p F G = Formalism.GM.M.fock p G F := by
  rw [fock_eq_sum F G _ (Finset.subset_union_left (s₂ := G.support)),
    fock_eq_sum G F _ (Finset.subset_union_right (s₁ := F.support))]
  exact Finset.sum_congr rfl (fun m _ => by ring)

theorem fock_add_left (F F' G : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p (F + F') G = Formalism.GM.M.fock p F G + Formalism.GM.M.fock p F' G := by
  rw [fock_eq_sum (F + F') G (F.support ∪ F'.support) support_add,
    fock_eq_sum F G _ (Finset.subset_union_left (s₂ := F'.support)),
    fock_eq_sum F' G _ (Finset.subset_union_right (s₁ := F.support)), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun m _ => by rw [coeff_add]; ring)

theorem fock_smul_left (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p (c • F) G = c * Formalism.GM.M.fock p F G := by
  rw [fock_eq_sum (c • F) G F.support support_smul, fock_def', Finset.mul_sum]
  exact Finset.sum_congr rfl (fun m _ => by rw [coeff_smul, smul_eq_mul]; ring)

theorem fock_zero_left (G : MvPolynomial σ ℚ_[p]) : Formalism.GM.M.fock p 0 G = 0 := by
  simp [Formalism.GM.M.fock]

theorem fock_sum_left {ι : Type} (t : Finset ι) (F : ι → MvPolynomial σ ℚ_[p]) (G : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p (∑ i ∈ t, F i) G = ∑ i ∈ t, Formalism.GM.M.fock p (F i) G := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [fock_zero_left]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add_left, ih]

theorem fock_sum_right {ι : Type} (t : Finset ι) (F : MvPolynomial σ ℚ_[p]) (G : ι → MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p F (∑ i ∈ t, G i) = ∑ i ∈ t, Formalism.GM.M.fock p F (G i) := by
  rw [fock_symm, fock_sum_left]; exact Finset.sum_congr rfl (fun i _ => fock_symm _ _)

theorem fock_smul_right (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p F (c • G) = c * Formalism.GM.M.fock p F G := by
  rw [fock_symm, fock_smul_left, fock_symm]

theorem fock_X_mul (i : σ) (g h : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p (X i * g) h = Formalism.GM.M.fock p g (pderiv i h) := by
  have hs : (X i * g).support = g.support.map (addRightEmbedding (Finsupp.single i 1)) := by
    rw [mul_comm]; exact support_mul_X i g
  rw [fock_def', hs, Finset.sum_map, fock_def']
  refine Finset.sum_congr rfl (fun m _ => ?_)
  simp only [addRightEmbedding_apply]
  rw [mul_comm (X i) g, coeff_mul_X, coeff_pderiv, wf_add_single]
  push_cast; ring

theorem fock_monomial (α α' : σ →₀ ℕ) (c c' : ℚ_[p]) :
    Formalism.GM.M.fock p (monomial α c) (monomial α' c') = if α = α' then c * c' * wf α else 0 := by
  rw [fock_eq_sum _ _ {α} support_monomial_subset, Finset.sum_singleton, coeff_monomial, coeff_monomial]
  by_cases h : α = α'
  · subst h; simp
  · simp [h, Ne.symm h]

end fockS

section tie
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)

theorem fock_E (g h : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p (Formalism.GM.tieE w e g) h = Formalism.GM.M.fock p g (Formalism.GM.tieF w e h) := by
  have h1 : Formalism.GM.tieE w e g = ∑ c, X (e c) * (X (w c) * g) := by
    simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun c _ => by ring)
  have h2 : Formalism.GM.tieF w e h = ∑ c, pderiv (w c) (pderiv (e c) h) := by
    simp [Formalism.GM.tieF, LinearMap.sum_apply]
  rw [h1, h2, fock_sum_left, fock_sum_right]
  exact Finset.sum_congr rfl (fun c _ => by rw [fock_X_mul, fock_X_mul])

theorem fock_E_pow (j : ℕ) (g h : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p ((Formalism.GM.tieE w e ^ j) g) h = Formalism.GM.M.fock p g ((Formalism.GM.tieF w e ^ j) h) := by
  induction j generalizing h with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, fock_E, ih, pow_succ, Module.End.mul_apply]

end tie

section dop
variable {σ : Type} [DecidableEq σ]

theorem pderiv_comm' (i j : σ) (q : MvPolynomial σ ℚ_[p]) :
    pderiv i (pderiv j q) = pderiv j (pderiv i q) := by
  ext m
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv]
  by_cases h : i = j
  · subst h; rfl
  · have h1 : ((m + Finsupp.single i 1 : σ →₀ ℕ) : σ → ℕ) j = m j := by simp [Finsupp.single_apply, h]
    have h2 : ((m + Finsupp.single j 1 : σ →₀ ℕ) : σ → ℕ) i = m i := by simp [Finsupp.single_apply, Ne.symm h]
    rw [h1, h2, show m + Finsupp.single i 1 + Finsupp.single j 1 = m + Finsupp.single j 1 + Finsupp.single i 1 by
      rw [add_assoc, add_comm (Finsupp.single i 1), ← add_assoc]]
    ring

noncomputable def Dop (u v : σ) : Module.End ℚ_[p] (MvPolynomial σ ℚ_[p]) :=
  (pderiv u).toLinearMap ∘ₗ (pderiv v).toLinearMap

theorem Dop_apply (u v : σ) (q : MvPolynomial σ ℚ_[p]) : Dop u v q = pderiv u (pderiv v q) := rfl

theorem Dop_commute (u v u' v' : σ) : Commute (Dop (p := p) u v) (Dop u' v') := by
  apply LinearMap.ext; intro q
  simp only [Module.End.mul_apply, Dop_apply]
  rw [pderiv_comm' v u', pderiv_comm' u u', pderiv_comm' v v', pderiv_comm' u v']

theorem Dop_commute_sum {ι : Type} (s : Finset ι) (u v : σ) (f g : ι → σ) :
    Commute (Dop (p := p) u v) (∑ i ∈ s, Dop (f i) (g i)) :=
  Commute.sum_right _ _ _ (fun i _ => Dop_commute _ _ _ _)

theorem coeff_Dop_pow (u v : σ) (huv : u ≠ v) (a : ℕ) (G : MvPolynomial σ ℚ_[p]) (β : σ →₀ ℕ) :
    coeff β ((Dop u v ^ a) G) = coeff (β + a • (Finsupp.single u 1 + Finsupp.single v 1)) G *
      (((β u + a).descFactorial a : ℕ) : ℚ_[p]) * (((β v + a).descFactorial a : ℕ) : ℚ_[p]) := by
  induction a generalizing β with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, Dop_apply, coeff_pderiv, coeff_pderiv]
    rw [ih]
    have hv : ((β + Finsupp.single u 1 : σ →₀ ℕ) : σ → ℕ) v = β v := by
      simp [Finsupp.single_apply, huv]
    have hu' : ((β + Finsupp.single u 1 + Finsupp.single v 1 : σ →₀ ℕ) : σ → ℕ) u = β u + 1 := by
      simp [Finsupp.single_apply, huv]
    have hv' : ((β + Finsupp.single u 1 + Finsupp.single v 1 : σ →₀ ℕ) : σ → ℕ) v = β v + 1 := by
      simp [Finsupp.single_apply, huv]
    rw [hv, hu', hv']
    have hm : β + Finsupp.single u 1 + Finsupp.single v 1 + a • (Finsupp.single u 1 + Finsupp.single v 1) =
        β + (a + 1) • (Finsupp.single u 1 + Finsupp.single v 1) := by
      rw [add_smul, one_smul]; abel
    rw [hm]
    have d1 : (β u + (a + 1)).descFactorial (a + 1) = (β u + 1) * (β u + 1 + a).descFactorial a := by
      rw [show β u + (a + 1) = β u + 1 + a by ring, Nat.descFactorial_succ]
      congr 1; omega
    have d2 : (β v + (a + 1)).descFactorial (a + 1) = (β v + 1) * (β v + 1 + a).descFactorial a := by
      rw [show β v + (a + 1) = β v + 1 + a by ring, Nat.descFactorial_succ]
      congr 1; omega
    rw [d1, d2]
    push_cast
    ring

end dop

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM.gammaIntegralityLemmas

open MvPolynomial Finset

variable {p : ℕ} [hp : Fact p.Prime]

section dop2
variable {σ : Type} [DecidableEq σ]

theorem Dop_pow_monomial_add (u v : σ) (huv : u ≠ v) (a : ℕ) (δ : σ →₀ ℕ) (h : ℚ_[p]) :
    (Dop u v ^ a) (monomial (δ + a • (Finsupp.single u 1 + Finsupp.single v 1)) h) =
      monomial δ (h * (((δ u + a).descFactorial a : ℕ) : ℚ_[p]) * (((δ v + a).descFactorial a : ℕ) : ℚ_[p])) := by
  ext β
  rw [coeff_Dop_pow u v huv, coeff_monomial, coeff_monomial]
  by_cases hb : δ = β
  · subst hb; simp
  · have : δ + a • (Finsupp.single u 1 + Finsupp.single v 1) ≠ β + a • (Finsupp.single u 1 + Finsupp.single v 1) :=
      fun h' => hb (add_right_cancel h')
    simp [this, hb]

theorem Dop_pow_monomial_lt (u v : σ) (huv : u ≠ v) (a : ℕ) (γ : σ →₀ ℕ) (h : ℚ_[p]) (hlt : γ u < a) :
    (Dop u v ^ a) (monomial γ h) = 0 := by
  ext β
  rw [coeff_Dop_pow u v huv, coeff_monomial, coeff_zero]
  have : γ ≠ β + a • (Finsupp.single u 1 + Finsupp.single v 1) := by
    intro h'
    have := congrArg (fun f : σ →₀ ℕ => f u) h'
    simp [Finsupp.single_apply, huv] at this
    omega
  rw [if_neg this]; ring

theorem pderiv_X_pow_mul (i y : σ) (hiy : i ≠ y) (m : ℕ) (G : MvPolynomial σ ℚ_[p]) :
    pderiv i (X y ^ m * G) = X y ^ m * pderiv i G := by
  rw [Derivation.leibniz, X_pow_eq_monomial, pderiv_monomial]
  have : (Finsupp.single y m : σ →₀ ℕ) i = 0 := by simp [Finsupp.single_apply, Ne.symm hiy]
  rw [this]
  simp

theorem Dop_X_pow_mul (u v y : σ) (huy : u ≠ y) (hvy : v ≠ y) (m : ℕ) (G : MvPolynomial σ ℚ_[p]) :
    Dop u v (X y ^ m * G) = X y ^ m * Dop u v G := by
  rw [Dop_apply, Dop_apply, pderiv_X_pow_mul v y hvy, pderiv_X_pow_mul u y huy]

end dop2

section FT
variable {σ : Type} [DecidableEq σ] {r : ℕ} (w e : Fin r → σ)

noncomputable def FT (T : Finset (Fin r)) : Module.End ℚ_[p] (MvPolynomial σ ℚ_[p]) :=
  ∑ c ∈ T, Dop (w c) (e c)

theorem tieF_eq_FT : Formalism.GM.tieF w e = (FT (p := p) w e Finset.univ) := rfl

theorem FT_insert (c : Fin r) (T : Finset (Fin r)) (hc : c ∉ T) :
    FT (p := p) w e (insert c T) = Dop (w c) (e c) + FT w e T := by
  unfold FT; rw [sum_insert hc]

theorem tieF_split (ρ : Fin r) :
    Formalism.GM.tieF w e = Dop (p := p) (w ρ) (e ρ) + FT w e (univ.erase ρ) := by
  rw [tieF_eq_FT, ← FT_insert w e ρ _ (notMem_erase ρ univ), insert_erase (mem_univ ρ)]

theorem FT_apply (T : Finset (Fin r)) (H : MvPolynomial σ ℚ_[p]) :
    FT (p := p) w e T H = ∑ c ∈ T, Dop (w c) (e c) H := by
  unfold FT; exact LinearMap.sum_apply _ _ _

theorem FT_commute (u v : σ) (T : Finset (Fin r)) : Commute (Dop (p := p) u v) (FT w e T) :=
  Dop_commute_sum _ _ _ _ _

theorem FT_X_pow_mul (y : σ) (T : Finset (Fin r)) (hy : ∀ c ∈ T, w c ≠ y ∧ e c ≠ y) (m : ℕ)
    (G : MvPolynomial σ ℚ_[p]) : FT w e T (X y ^ m * G) = X y ^ m * FT w e T G := by
  rw [FT_apply, FT_apply, mul_sum]
  exact sum_congr rfl (fun c hc => Dop_X_pow_mul _ _ y (hy c hc).1 (hy c hc).2 m G)

theorem FT_pow_X_pow_mul (y : σ) (T : Finset (Fin r)) (hy : ∀ c ∈ T, w c ≠ y ∧ e c ≠ y) (m b : ℕ)
    (G : MvPolynomial σ ℚ_[p]) : (FT w e T ^ b) (X y ^ m * G) = X y ^ m * (FT w e T ^ b) G := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ', Module.End.mul_apply, ih, FT_X_pow_mul w e y T hy, ← Module.End.mul_apply, ← pow_succ']

theorem supp_FT_pow (T : Finset (Fin r)) (Q : ℕ → (σ →₀ ℕ) → Prop)
    (hstep : ∀ b β c, c ∈ T → Q b (β + Finsupp.single (w c) 1 + Finsupp.single (e c) 1) → Q (b + 1) β)
    (hwe : ∀ c, w c ≠ e c)
    (G : MvPolynomial σ ℚ_[p]) (h0 : ∀ β ∈ G.support, Q 0 β) :
    ∀ b, ∀ β ∈ ((FT w e T ^ b) G).support, Q b β := by
  intro b
  induction b with
  | zero => simpa using h0
  | succ b ih =>
    intro β hβ
    rw [pow_succ', Module.End.mul_apply, mem_support_iff] at hβ
    rw [FT_apply, coeff_sum] at hβ
    obtain ⟨c, hc, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
    have := coeff_Dop_pow (w c) (e c) (hwe c) 1 ((FT w e T ^ b) G) β
    rw [pow_one] at this
    rw [this] at hne
    have hm : coeff (β + 1 • (Finsupp.single (w c) 1 + Finsupp.single (e c) 1)) ((FT w e T ^ b) G) ≠ 0 := by
      intro h0'; apply hne; rw [h0']; ring
    rw [one_smul, ← add_assoc] at hm
    exact hstep b β c hc (ih _ (mem_support_iff.mpr hm))

theorem FT_pow_coeff_norm (hwe : ∀ c, w c ≠ e c) (Tb B : ℕ) (hB : Nat.log p Tb ≤ B) (K : ℝ)
    (G : MvPolynomial σ ℚ_[p]) (hG : ∀ β, ‖coeff β G‖ ≤ K) (T : Finset (Fin r)) :
    ∀ b ≤ Tb, ∀ β, ‖coeff β ((FT w e T ^ b) G)‖ ≤
      K * (p : ℝ) ^ (((T.card * B : ℕ) : ℤ) - 2 * (padicValNat p b.factorial : ℤ)) := by
  have hK : 0 ≤ K := (norm_nonneg _).trans (hG 0)
  induction T using Finset.induction_on with
  | empty =>
    intro b _ β
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simpa using hG β
    · have : FT (p := p) w e (∅ : Finset (Fin r)) = 0 := by simp [FT]
      rw [this, zero_pow hb.ne']
      simp only [LinearMap.zero_apply, coeff_zero, norm_zero]
      exact mul_nonneg hK (zpow_pos' _).le
  | insert c T hc ih =>
    intro b hb β
    rw [FT_insert w e c T hc, (FT_commute w e (w c) (e c) T).add_pow b, LinearMap.sum_apply, coeff_sum]
    apply norm_sum_le_bound _ _ _ (mul_nonneg hK (zpow_pos' _).le)
    intro a ha
    rw [mem_range] at ha
    rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, map_nsmul,
      coeff_smul, nsmul_eq_mul, norm_mul, coeff_Dop_pow _ _ (hwe c), norm_mul, norm_mul]
    have h1 := ih (b - a) (by omega) (β + a • (Finsupp.single (w c) 1 + Finsupp.single (e c) 1))
    have h2 := norm_desc_le (p := p) (β (w c) + a) a
    have h3 := norm_desc_le (p := p) (β (e c) + a) a
    have hC : ‖((b.choose a : ℕ) : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p (b.choose a) : ℤ)) :=
      norm_nat_eq _ (Nat.choose_pos (by omega)).ne'
    have hv := vchoose_le (p := p) (k := a) hb hB
    have hfac : padicValNat p b.factorial = padicValNat p (b.choose a) + padicValNat p a.factorial +
        padicValNat p (b - a).factorial := by
      rw [← Nat.choose_mul_factorial_mul_factorial (show a ≤ b by omega),
        padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.factorial_pos _).ne')
          (Nat.factorial_pos _).ne',
        padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.factorial_pos _).ne']
    rw [hC]
    calc (p : ℝ) ^ (-(padicValNat p (b.choose a) : ℤ)) *
          (‖coeff (β + a • (Finsupp.single (w c) 1 + Finsupp.single (e c) 1)) ((FT w e T ^ (b - a)) G)‖ *
            ‖((((β (w c) + a).descFactorial a) : ℕ) : ℚ_[p])‖ * ‖((((β (e c) + a).descFactorial a) : ℕ) : ℚ_[p])‖)
        ≤ (p : ℝ) ^ (-(padicValNat p (b.choose a) : ℤ)) *
          ((K * (p : ℝ) ^ (((T.card * B : ℕ) : ℤ) - 2 * (padicValNat p (b - a).factorial : ℤ))) *
            (p : ℝ) ^ (-(padicValNat p a.factorial : ℤ)) * (p : ℝ) ^ (-(padicValNat p a.factorial : ℤ))) := by
          gcongr
      _ = K * (p : ℝ) ^ ((((T.card * B : ℕ) : ℤ) - 2 * (padicValNat p (b - a).factorial : ℤ)) +
            (-(padicValNat p a.factorial : ℤ)) + (-(padicValNat p a.factorial : ℤ)) +
            (-(padicValNat p (b.choose a) : ℤ))) := by
          have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
          rw [zpow_add₀ hp0, zpow_add₀ hp0, zpow_add₀ hp0]; ring
      _ ≤ K * (p : ℝ) ^ ((((insert c T).card * B : ℕ) : ℤ) - 2 * (padicValNat p b.factorial : ℤ)) := by
          apply mul_le_mul_of_nonneg_left _ hK
          apply zpow_mono'
          rw [card_insert_of_notMem hc, hfac]
          push_cast
          linarith

end FT

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM.gammaIntegralityLemmas

open MvPolynomial Finset

variable {p : ℕ} [hp : Fact p.Prime]

section good
variable {σ : Type} [DecidableEq σ] {M : Type} [AddCommMonoid M]

def AllMono (Q : M → (σ →₀ ℕ) → Prop) (d : M) (P : MvPolynomial σ ℚ_[p]) : Prop :=
  ∀ β ∈ P.support, Q d β

variable (Q : M → (σ →₀ ℕ) → Prop)

theorem AllMono.mul (hQ : ∀ d d' β β', Q d β → Q d' β' → Q (d + d') (β + β')) {d d' : M}
    {P P' : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) (h' : AllMono Q d' P') : AllMono Q (d + d') (P * P') := by
  intro β hβ
  obtain ⟨β1, h1, β2, h2, rfl⟩ := Finset.mem_add.mp (support_mul P P' hβ)
  exact hQ _ _ _ _ (h _ h1) (h' _ h2)

theorem AllMono.add {d : M} {P P' : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) (h' : AllMono Q d P') :
    AllMono Q d (P + P') := by
  intro β hβ
  rcases Finset.mem_union.mp (support_add hβ) with h1 | h1
  · exact h _ h1
  · exact h' _ h1

theorem AllMono.zero (d : M) : AllMono Q d (0 : MvPolynomial σ ℚ_[p]) := by
  intro β hβ; simp at hβ

theorem AllMono.sum {ι : Type} (s : Finset ι) {d : M} (P : ι → MvPolynomial σ ℚ_[p])
    (h : ∀ i ∈ s, AllMono Q d (P i)) : AllMono Q d (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using AllMono.zero Q d
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self _ _)).add Q (ih (fun i hi => h i (mem_insert_of_mem hi)))

theorem AllMono.one (hQ0 : Q 0 0) : AllMono Q 0 (1 : MvPolynomial σ ℚ_[p]) := by
  intro β hβ
  have : β = 0 := by
    have h1 : (1 : MvPolynomial σ ℚ_[p]) = monomial 0 1 := rfl
    rw [h1] at hβ
    simpa using support_monomial_subset hβ
  subst this; exact hQ0

theorem AllMono.C_mul (a : ℚ_[p]) {d : M} {P : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) :
    AllMono Q d (C a * P) := by
  intro β hβ
  rw [C_mul'] at hβ
  exact h _ (support_smul hβ)

theorem AllMono.neg {d : M} {P : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) : AllMono Q d (-P) := by
  intro β hβ; rw [support_neg] at hβ; exact h _ hβ

theorem AllMono.sub {d : M} {P P' : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) (h' : AllMono Q d P') :
    AllMono Q d (P - P') := by
  rw [sub_eq_add_neg]; exact h.add Q h'.neg

theorem AllMono.congr {d d' : M} (hd : d = d') {P : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) :
    AllMono Q d' P := hd ▸ h

theorem AllMono.pow (hQ : ∀ d d' β β', Q d β → Q d' β' → Q (d + d') (β + β')) (hQ0 : Q 0 0) {d : M}
    {P : MvPolynomial σ ℚ_[p]} (h : AllMono Q d P) (n : ℕ) : AllMono Q (n • d) (P ^ n) := by
  induction n with
  | zero => simpa using AllMono.one Q hQ0
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul Q hQ h

theorem AllMono.prod (hQ : ∀ d d' β β', Q d β → Q d' β' → Q (d + d') (β + β')) (hQ0 : Q 0 0)
    {ι : Type} (s : Finset ι) (d : ι → M) (P : ι → MvPolynomial σ ℚ_[p])
    (h : ∀ i ∈ s, AllMono Q (d i) (P i)) : AllMono Q (∑ i ∈ s, d i) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using AllMono.one Q hQ0
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    exact (h a (mem_insert_self _ _)).mul Q hQ (ih (fun i hi => h i (mem_insert_of_mem hi)))

theorem AllMono.X_mul_X (u u' : σ) (d : M) (hq : Q d (Finsupp.single u 1 + Finsupp.single u' 1)) :
    AllMono Q d (X u * X u' : MvPolynomial σ ℚ_[p]) := by
  intro β hβ
  rw [X, X, monomial_mul, one_mul] at hβ
  have := support_monomial_subset hβ
  rw [Finset.mem_singleton] at this
  subst this; exact hq

end good

section intP
variable {σ : Type} [DecidableEq σ]

def IsIntP (P : MvPolynomial σ ℚ_[p]) : Prop := ∀ β, ‖coeff β P‖ ≤ 1

theorem IsIntP.mul {P P' : MvPolynomial σ ℚ_[p]} (h : IsIntP P) (h' : IsIntP P') : IsIntP (P * P') := by
  intro β
  rw [coeff_mul]
  apply norm_sum_le_one
  intro x _
  rw [norm_mul]
  exact mul_le_one₀ (h _) (norm_nonneg _) (h' _)

theorem IsIntP.add {P P' : MvPolynomial σ ℚ_[p]} (h : IsIntP P) (h' : IsIntP P') : IsIntP (P + P') := by
  intro β; rw [coeff_add]; exact (Padic.nonarchimedean _ _).trans (max_le (h β) (h' β))

theorem IsIntP.neg {P : MvPolynomial σ ℚ_[p]} (h : IsIntP P) : IsIntP (-P) := by
  intro β; rw [coeff_neg, norm_neg]; exact h β

theorem IsIntP.sub {P P' : MvPolynomial σ ℚ_[p]} (h : IsIntP P) (h' : IsIntP P') : IsIntP (P - P') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem IsIntP.C {a : ℚ_[p]} (ha : ‖a‖ ≤ 1) : IsIntP (MvPolynomial.C a : MvPolynomial σ ℚ_[p]) := by
  intro β; rw [coeff_C]; split_ifs <;> simp [ha]

theorem IsIntP.one : IsIntP (1 : MvPolynomial σ ℚ_[p]) := by
  rw [← C_1]; exact IsIntP.C (by simp)

theorem IsIntP.X (u : σ) : IsIntP (X u : MvPolynomial σ ℚ_[p]) := by
  intro β; rw [coeff_X']; split_ifs <;> simp

theorem IsIntP.sum {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ ℚ_[p]) (h : ∀ i ∈ s, IsIntP (P i)) :
    IsIntP (∑ i ∈ s, P i) := by
  intro β; rw [coeff_sum]; exact norm_sum_le_one _ _ (fun i hi => h i hi β)

theorem IsIntP.prod {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ ℚ_[p]) (h : ∀ i ∈ s, IsIntP (P i)) :
    IsIntP (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsIntP.one (p := p) (σ := σ)
  | insert a s ha ih =>
    rw [prod_insert ha]; exact (h a (mem_insert_self _ _)).mul (ih (fun i hi => h i (mem_insert_of_mem hi)))

theorem IsIntP.pow {P : MvPolynomial σ ℚ_[p]} (h : IsIntP P) (n : ℕ) : IsIntP (P ^ n) := by
  induction n with
  | zero => simpa using IsIntP.one (p := p) (σ := σ)
  | succ n ih => rw [pow_succ]; exact ih.mul h

end intP

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM.gammaIntegralityLemmas

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [hp : Fact p.Prime]

section frz
variable {N r : ℕ}

def δv (β : Fin (N + 1 + 1) × Fin r →₀ ℕ) : Fin (N + 1 + 1) → ℕ := fun i => ∑ c, β (i, c)

theorem δv_add (β β' : Fin (N + 1 + 1) × Fin r →₀ ℕ) : δv (β + β') = δv β + δv β' := by
  funext i; simp [δv, sum_add_distrib]

theorem δv_zero : δv (0 : Fin (N + 1 + 1) × Fin r →₀ ℕ) = 0 := by
  funext i; simp [δv]

theorem δv_single (a : Fin (N + 1 + 1)) (c : Fin r) :
    δv (Finsupp.single (a, c) 1) = Pi.single a 1 := by
  funext k
  simp only [δv, Finsupp.single_apply, Prod.mk.injEq, Pi.single_apply]
  by_cases h : a = k
  · subst h; simp
  · simp [h, Ne.symm h]

def GoodQ (ρ : Fin r) (D : Fin (N + 1 + 1) → ℕ) (β : Fin (N + 1 + 1) × Fin r →₀ ℕ) : Prop :=
  δv β = D ∧ β (Fin.castSucc (Fin.last N), ρ) ≤ β (Fin.last (N + 1), ρ)

theorem GoodQ_add (ρ : Fin r) : ∀ d d' β β', GoodQ (N := N) ρ d β → GoodQ ρ d' β' → GoodQ ρ (d + d') (β + β') := by
  intro d d' β β' h h'
  refine ⟨by rw [δv_add, h.1, h'.1], ?_⟩
  simp only [Finsupp.add_apply]
  have := h.2; have := h'.2; omega

theorem GoodQ_zero (ρ : Fin r) : GoodQ (N := N) ρ 0 0 := ⟨δv_zero, by simp⟩

def dv (i : Fin (N + 1)) : Fin (N + 1 + 1) → ℕ := Pi.single (Fin.castSucc i) 1 + Pi.single (Fin.last (N + 1)) 1

theorem freezeSub_good (LL : Letters (N + 1)) (ρ : Fin r) (hW : LL.vec (Fin.last N) = true)
    (i : Fin (N + 1)) (c : Fin r) :
    AllMono (p := p) (GoodQ ρ) (dv i) (freezeSub p LL ρ (i, c)) := by
  have hne : ∀ (a : Fin (N + 1)), (Fin.last (N + 1) : Fin (N + 1 + 1)) ≠ Fin.castSucc a :=
    fun a h => Fin.castSucc_ne_last a h.symm
  simp only [freezeSub]
  split_ifs with hv hc hc
  · subst hc
    apply AllMono.sum
    intro c' _
    apply AllMono.X_mul_X
    refine ⟨by rw [δv_add, δv_single, δv_single]; rfl, ?_⟩
    simp only [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq]
    by_cases h1 : c' = c <;> by_cases h2 : i = Fin.last N <;> simp [h1, h2, hne, Fin.castSucc_ne_last]
  · apply AllMono.X_mul_X
    refine ⟨by rw [δv_add, δv_single, δv_single, dv]; exact add_comm _ _, ?_⟩
    simp only [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq]
    simp [hne, Ne.symm hc]
    try (split_ifs <;> omega)
  · subst hc
    apply AllMono.X_mul_X
    refine ⟨by rw [δv_add, δv_single, δv_single, dv]; exact add_comm _ _, ?_⟩
    simp only [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq]
    by_cases h2 : i = Fin.last N <;> simp [h2, hne, Fin.castSucc_ne_last]
  · have hi : i ≠ Fin.last N := by rintro rfl; simp [hW] at hv
    apply AllMono.sub
    · apply AllMono.X_mul_X
      refine ⟨by rw [δv_add, δv_single, δv_single, dv]; exact add_comm _ _, ?_⟩
      simp only [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq]
      simp [hne, Ne.symm hc]
      split_ifs <;> omega
    · apply AllMono.X_mul_X
      refine ⟨by rw [δv_add, δv_single, δv_single]; rfl, ?_⟩
      simp only [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq]
      simp [hne, hi, Ne.symm hc, Fin.castSucc_ne_last]

theorem freezeSub_int (LL : Letters (N + 1)) (ρ : Fin r) (v : Fin (N + 1) × Fin r) :
    IsIntP (freezeSub p LL ρ v) := by
  obtain ⟨i, c⟩ := v
  simp only [freezeSub]
  split_ifs
  · exact IsIntP.sum _ _ (fun _ _ => (IsIntP.X _).mul (IsIntP.X _))
  · exact (IsIntP.X _).mul (IsIntP.X _)
  · exact (IsIntP.X _).mul (IsIntP.X _)
  · exact ((IsIntP.X _).mul (IsIntP.X _)).sub ((IsIntP.X _).mul (IsIntP.X _))

theorem sum_dv (LL : Letters (N + 1)) (μ : Fin (N + 1) × Fin r →₀ ℕ) (hμ : MultiDeg LL μ) :
    (∑ v : Fin (N + 1) × Fin r, μ v • dv v.1) = (LL.snoc LL.total).deg := by
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dv, Pi.add_apply, mul_add, sum_add_distrib]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  induction k using Fin.lastCases with
  | last =>
    have hne : ∀ x : Fin (N + 1), (Fin.last (N + 1) : Fin (N + 1 + 1)) ≠ Fin.castSucc x :=
      fun x h => Fin.castSucc_ne_last x h.symm
    simp only [Pi.single_apply, hne, if_false, mul_zero, sum_const_zero, zero_add,
      if_true, mul_one]
    simp only [Letters.snoc, Fin.lastCases_last, Letters.total]
    exact sum_congr rfl (fun i _ => hμ i)
  | cast k =>
    simp only [Pi.single_apply, Fin.castSucc_inj, Fin.castSucc_ne_last k, if_false, mul_zero,
      sum_const_zero, add_zero]
    simp only [Letters.snoc, Fin.lastCases_castSucc]
    rw [Finset.sum_eq_single k]
    · simp only [if_true, mul_one]; exact hμ k
    · intro b _ hb; simp [Ne.symm hb]
    · simp

end frz

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM.gammaIntegralityLemmas

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [hp : Fact p.Prime]

section frz3
variable {N r : ℕ}

theorem aeval_expand (LL : Letters (N + 1)) (ρ : Fin r) (f : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) :
    aeval (freezeSub p LL ρ) f = ∑ μ ∈ f.support,
      C (coeff μ f) * ∏ v : Fin (N + 1) × Fin r, freezeSub p LL ρ v ^ μ v := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum]
  apply sum_congr rfl
  intro μ _
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPolynomial.algebraMap_eq]

theorem aeval_good (LL : Letters (N + 1)) (ρ : Fin r) (hW : LL.vec (Fin.last N) = true)
    (f : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hf : f ∈ Pol p r LL) :
    AllMono (p := p) (GoodQ ρ) ((LL.snoc LL.total).deg) (aeval (freezeSub p LL ρ) f) := by
  rw [aeval_expand]
  apply AllMono.sum
  intro μ hμ
  have hmd : MultiDeg LL μ := by
    have hsub : (f.support : Set (Fin (N + 1) × Fin r →₀ ℕ)) ⊆ {m | MultiDeg LL m} := hf
    exact hsub (Finset.mem_coe.mpr hμ)
  apply AllMono.C_mul
  have h := AllMono.prod (p := p) (GoodQ ρ) (GoodQ_add ρ) (GoodQ_zero ρ) univ (fun v => μ v • dv v.1)
    (fun v => freezeSub p LL ρ v ^ μ v)
    (fun v _ => (freezeSub_good LL ρ hW v.1 v.2).pow (GoodQ ρ) (GoodQ_add ρ) (GoodQ_zero ρ) (μ v))
  exact h.congr (GoodQ ρ) (sum_dv LL μ hmd)

theorem intPol_coeff {σ : Type} (f : MvPolynomial σ ℚ_[p]) (hf : f ∈ IntPol p σ) :
    ∀ μ, ‖coeff μ f‖ ≤ 1 := by
  obtain ⟨f0, rfl⟩ := hf
  intro μ
  simp only [AlgHom.toLinearMap_apply, mapAlgHom_apply, coeff_map]
  exact PadicInt.norm_le_one (coeff μ f0)

theorem aeval_int (LL : Letters (N + 1)) (ρ : Fin r)
    (f : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hf : ∀ μ, ‖coeff μ f‖ ≤ 1) :
    IsIntP (aeval (freezeSub p LL ρ) f) := by
  rw [aeval_expand]
  apply IsIntP.sum
  intro μ _
  exact (IsIntP.C (hf μ)).mul (IsIntP.prod _ _ (fun v _ => (freezeSub_int LL ρ v).pow _))

end frz3

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM.gammaIntegralityLemmas

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [hp : Fact p.Prime]

section alg
variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem wf_add_single_eq (δ : σ →₀ ℕ) (y : σ) (t : ℕ) :
    wf (p := p) (δ + Finsupp.single y t) * ((δ y).factorial : ℚ_[p]) = wf δ * ((δ y + t).factorial : ℚ_[p]) := by
  unfold wf
  rw [← Finset.mul_prod_erase univ _ (mem_univ y), ← Finset.mul_prod_erase univ (fun x => ((δ x).factorial : ℚ_[p])) (mem_univ y)]
  have : ∀ v ∈ univ.erase y, (((δ + Finsupp.single y t : σ →₀ ℕ) v).factorial : ℚ_[p]) = ((δ v).factorial : ℚ_[p]) := by
    intro v hv
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (ne_of_mem_erase hv)), add_zero]
  rw [Finset.prod_congr rfl this]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  ring

theorem X_pow_mul_monomial (y : σ) (m : ℕ) (γ : σ →₀ ℕ) (h : ℚ_[p]) :
    (X y ^ m * monomial γ h : MvPolynomial σ ℚ_[p]) = monomial (γ + Finsupp.single y m) h := by
  rw [X_pow_eq_monomial, monomial_mul, one_mul, add_comm]

theorem fock_Dop_term (x y : σ) (hxy : x ≠ y) (a a' m : ℕ) (β₀ β₀' : σ →₀ ℕ) (h h' : ℚ_[p]) :
    Formalism.GM.M.fock p ((Dop x y ^ a) (X y ^ m * monomial (β₀ + a • (Finsupp.single x 1 + Finsupp.single y 1)) h))
      ((Dop x y ^ a') (X y ^ m * monomial (β₀' + a' • (Finsupp.single x 1 + Finsupp.single y 1)) h')) =
    if β₀ = β₀' then
      h * h' * (((β₀ x + a).descFactorial a : ℕ) : ℚ_[p]) * (((β₀ x + a').descFactorial a' : ℕ) : ℚ_[p]) *
        wf (β₀ + Finsupp.single y a) * (((m + (β₀ y + a)).choose (β₀ y + a) : ℕ) : ℚ_[p]) *
        (m.factorial : ℚ_[p]) * ((((m + (β₀ y + a'))).descFactorial a' : ℕ) : ℚ_[p])
    else 0 := by
  rw [X_pow_mul_monomial, X_pow_mul_monomial]
  have e1 : β₀ + a • (Finsupp.single x 1 + Finsupp.single y 1) + Finsupp.single y m =
      (β₀ + Finsupp.single y m) + a • (Finsupp.single x 1 + Finsupp.single y 1) := by abel
  have e2 : β₀' + a' • (Finsupp.single x 1 + Finsupp.single y 1) + Finsupp.single y m =
      (β₀' + Finsupp.single y m) + a' • (Finsupp.single x 1 + Finsupp.single y 1) := by abel
  rw [e1, e2, Dop_pow_monomial_add x y hxy, Dop_pow_monomial_add x y hxy, fock_monomial]
  have hx : ∀ δ : σ →₀ ℕ, (δ + Finsupp.single y m) x = δ x := by
    intro δ; simp [Finsupp.single_apply, Ne.symm hxy]
  have hy : ∀ δ : σ →₀ ℕ, (δ + Finsupp.single y m) y = δ y + m := by
    intro δ; simp
  rw [hx, hx, hy, hy]
  by_cases hb : β₀ = β₀'
  · subst hb
    rw [if_pos rfl, if_pos rfl]

    have hk : ((β₀ y).factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have w1 := wf_add_single_eq (p := p) β₀ y m
    have w2 := wf_add_single_eq (p := p) β₀ y a
    have f1 : ((β₀ y + m).factorial : ℚ_[p]) * (((β₀ y + m + a).descFactorial a : ℕ) : ℚ_[p]) =
        ((β₀ y + m + a).factorial : ℚ_[p]) := by
      have := Nat.factorial_mul_descFactorial (show a ≤ β₀ y + m + a by omega)
      rw [show β₀ y + m + a - a = β₀ y + m by omega] at this
      exact_mod_cast this
    have f2 : (((m + (β₀ y + a)).choose (β₀ y + a) : ℕ) : ℚ_[p]) * (m.factorial : ℚ_[p]) *
        ((β₀ y + a).factorial : ℚ_[p]) = ((β₀ y + m + a).factorial : ℚ_[p]) := by
      have := Nat.add_choose_mul_factorial_mul_factorial m (β₀ y + a)
      rw [show m + (β₀ y + a) = β₀ y + m + a by ring] at this
      rw [show m + (β₀ y + a) = β₀ y + m + a by ring]
      exact_mod_cast this
    have key : wf (p := p) (β₀ + Finsupp.single y m) * (((β₀ y + m + a).descFactorial a : ℕ) : ℚ_[p]) =
        wf (β₀ + Finsupp.single y a) * (((m + (β₀ y + a)).choose (β₀ y + a) : ℕ) : ℚ_[p]) * (m.factorial : ℚ_[p]) := by
      apply mul_right_cancel₀ hk
      calc wf (p := p) (β₀ + Finsupp.single y m) * (((β₀ y + m + a).descFactorial a : ℕ) : ℚ_[p]) * ((β₀ y).factorial : ℚ_[p])
          = (wf (p := p) (β₀ + Finsupp.single y m) * ((β₀ y).factorial : ℚ_[p])) *
              (((β₀ y + m + a).descFactorial a : ℕ) : ℚ_[p]) := by ring
        _ = wf β₀ * (((β₀ y + m).factorial : ℚ_[p]) * (((β₀ y + m + a).descFactorial a : ℕ) : ℚ_[p])) := by
              rw [w1]; ring
        _ = wf β₀ * ((β₀ y + m + a).factorial : ℚ_[p]) := by rw [f1]
        _ = (wf (p := p) (β₀ + Finsupp.single y a) * ((β₀ y).factorial : ℚ_[p])) *
              (((m + (β₀ y + a)).choose (β₀ y + a) : ℕ) : ℚ_[p]) * (m.factorial : ℚ_[p]) := by
              rw [w2, ← f2]; ring
        _ = _ := by ring
    rw [show m + (β₀ y + a') = β₀ y + m + a' by ring]
    calc h * (((β₀ x + a).descFactorial a : ℕ) : ℚ_[p]) * (((β₀ y + m + a).descFactorial a : ℕ) : ℚ_[p]) *
          (h' * (((β₀ x + a').descFactorial a' : ℕ) : ℚ_[p]) * (((β₀ y + m + a').descFactorial a' : ℕ) : ℚ_[p])) *
          wf (β₀ + Finsupp.single y m)
        = h * h' * (((β₀ x + a).descFactorial a : ℕ) : ℚ_[p]) * (((β₀ x + a').descFactorial a' : ℕ) : ℚ_[p]) *
          (wf (p := p) (β₀ + Finsupp.single y m) * (((β₀ y + m + a).descFactorial a : ℕ) : ℚ_[p])) *
          (((β₀ y + m + a').descFactorial a' : ℕ) : ℚ_[p]) := by ring
      _ = _ := by rw [key]; ring
  · have : β₀ + Finsupp.single y m ≠ β₀' + Finsupp.single y m := fun h'' => hb (add_right_cancel h'')
    rw [if_neg this, if_neg hb]

end alg

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM.gammaIntegralityLemmas

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [hp : Fact p.Prime]

theorem v_prod {ι : Type} (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValNat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValNat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, padicValNat.mul (hf a (mem_insert_self _ _))
      (Finset.prod_ne_zero_iff.mpr (fun i hi => hf i (mem_insert_of_mem hi))),
      ih (fun i hi => hf i (mem_insert_of_mem hi))]

theorem norm_K (κ : ℕ) (h h' : ℚ_[p]) (Eh Eh' : ℤ) (hh : ‖h‖ ≤ (p : ℝ) ^ Eh) (hh' : ‖h'‖ ≤ (p : ℝ) ^ Eh')
    (Num Den : ℕ) (hN : Num ≠ 0) (hD : Den ≠ 0) (s : ℚ_[p]) (hs : ‖s‖ = 1)
    (hE : -(κ : ℤ) + Eh + Eh' - (padicValNat p Num : ℤ) + (padicValNat p Den : ℤ) ≤ 0) :
    ‖(p : ℚ_[p]) ^ κ * (s * h * h' * (Num : ℚ_[p]) / (Den : ℚ_[p]))‖ ≤ 1 := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [norm_mul, norm_div, norm_mul, norm_mul, norm_mul, hs, Padic.norm_p_pow, norm_nat_eq _ hN,
    norm_nat_eq _ hD]
  calc (p : ℝ) ^ (-(κ : ℤ)) * (1 * ‖h‖ * ‖h'‖ * (p : ℝ) ^ (-(padicValNat p Num : ℤ)) /
        (p : ℝ) ^ (-(padicValNat p Den : ℤ)))
      ≤ (p : ℝ) ^ (-(κ : ℤ)) * (1 * (p : ℝ) ^ Eh * (p : ℝ) ^ Eh' * (p : ℝ) ^ (-(padicValNat p Num : ℤ)) /
        (p : ℝ) ^ (-(padicValNat p Den : ℤ))) := by
        gcongr
    _ = (p : ℝ) ^ (-(κ : ℤ) + Eh + Eh' - (padicValNat p Num : ℤ) + (padicValNat p Den : ℤ)) := by
        rw [zpow_add₀ hp0, zpow_sub₀ hp0, zpow_add₀ hp0, zpow_add₀ hp0, zpow_neg, zpow_neg, zpow_neg]
        field_simp
    _ ≤ (p : ℝ) ^ (0 : ℤ) := zpow_mono' hE
    _ = 1 := by simp

section grp
variable {N r : ℕ}

theorem vW_ge (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ) {T B : ℕ} (hB : Nat.log p T ≤ B)
    (hT : ∀ i, δv δ i ≤ T) :
    ∑ i, padicValNat p (δv δ i).factorial ≤
      padicValNat p (∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) + (N + 2) * (r * B) := by
  rw [v_prod _ _ (fun v _ => (Nat.factorial_pos _).ne'), Fintype.sum_prod_type]
  have : ∀ i : Fin (N + 1 + 1), padicValNat p (δv δ i).factorial ≤
      ∑ c : Fin r, padicValNat p (δ (i, c)).factorial + r * B := by
    intro i
    have := vfact_sum (p := p) (univ : Finset (Fin r)) (fun c => δ (i, c)) (hT i) hB
    simpa [δv] using this
  calc ∑ i, padicValNat p (δv δ i).factorial ≤ ∑ i : Fin (N + 1 + 1), (∑ c : Fin r, padicValNat p (δ (i, c)).factorial + r * B) :=
        sum_le_sum (fun i _ => this i)
    _ = _ := by rw [sum_add_distrib]; simp

end grp

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM.gammaIntegralityLemmas

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [hp : Fact p.Prime]

section term
variable {N r : ℕ}

abbrev xW (ρ : Fin r) : Fin (N + 1 + 1) × Fin r := (Fin.castSucc (Fin.last N), ρ)
abbrev yE (ρ : Fin r) : Fin (N + 1 + 1) × Fin r := (Fin.last (N + 1), ρ)

def eWY : Fin (N + 1 + 1) → ℕ := Pi.single (Fin.castSucc (Fin.last N)) 1 + Pi.single (Fin.last (N + 1)) 1

def kap (N r B : ℕ) : ℕ := 10 * (N + 3) * r ^ 2 * (B + 1)

noncomputable def termF (LL : Letters (N + 1)) (ρ : Fin r) (z j a a' : ℕ) (β γ : Fin (N + 1 + 1) × Fin r →₀ ℕ)
    (h h' : ℚ_[p]) (m : ℕ) : ℚ_[p] :=
  ((((LL.deg (Fin.last N) + (m + LL.total) + r + z - 1).choose (LL.deg (Fin.last N)) : ℕ) : ℚ_[p]) *
    (((-1 : ℚ_[p]) ^ j / (((j.factorial : ℚ_[p]) ^ 2) *
      (((LL.deg (Fin.last N) + (m + LL.total) + r + z - 1).choose j : ℕ) : ℚ_[p]))) *
    (((j.choose a : ℕ) : ℚ_[p]) * ((j.choose a' : ℕ) : ℚ_[p]) *
      Formalism.GM.M.fock p ((Dop (xW ρ) (yE ρ) ^ a) (X (yE ρ) ^ m * monomial β h))
        ((Dop (xW ρ) (yE ρ) ^ a') (X (yE ρ) ^ m * monomial γ h')))) /
    ((((m + LL.total - LL.total).factorial * LL.total.factorial : ℕ) : ℚ_[p]) * ∏ i, ((LL.deg i).factorial : ℚ_[p])))

theorem δv_single' (a : Fin (N + 1 + 1)) (c : Fin r) (t : ℕ) :
    δv (Finsupp.single (a, c) t) = Pi.single a t := by
  funext k
  simp only [δv, Finsupp.single_apply, Prod.mk.injEq, Pi.single_apply]
  by_cases h : a = k
  · subst h; simp
  · simp [h, Ne.symm h]

theorem xW_ne_yE (ρ : Fin r) : xW (N := N) ρ ≠ yE ρ := by
  simp [xW, yE, Fin.castSucc_ne_last]

theorem le_δv (β : Fin (N + 1 + 1) × Fin r →₀ ℕ) (i : Fin (N + 1 + 1)) (c : Fin r) : β (i, c) ≤ δv β i :=
  Finset.single_le_sum (f := fun c => β (i, c)) (fun _ _ => Nat.zero_le _) (mem_univ c)

theorem deg_le_total (LL : Letters (N + 1)) (i : Fin (N + 1)) : LL.deg i ≤ LL.total :=
  Finset.single_le_sum (f := LL.deg) (fun _ _ => Nat.zero_le _) (mem_univ i)

theorem comp_facts (LL : Letters (N + 1)) (b : ℕ) (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ) (c0 c1 : ℕ)
    (hd : δv δ + Pi.single (Fin.castSucc (Fin.last N)) c0 + Pi.single (Fin.last (N + 1)) c1 + b • eWY =
      (LL.snoc LL.total).deg) :
    (∀ k : Fin N, δv δ (Fin.castSucc (Fin.castSucc k)) = LL.deg (Fin.castSucc k)) ∧
    δv δ (Fin.castSucc (Fin.last N)) + c0 + b = LL.deg (Fin.last N) ∧
    δv δ (Fin.last (N + 1)) + c1 + b = LL.total := by
  have hne : ∀ k : Fin (N + 1), (Fin.last (N + 1) : Fin (N + 1 + 1)) ≠ Fin.castSucc k :=
    fun k h => Fin.castSucc_ne_last k h.symm
  refine ⟨fun k => ?_, ?_, ?_⟩
  · have := congrFun hd (Fin.castSucc (Fin.castSucc k))
    simp only [Pi.add_apply, Pi.smul_apply, eWY, Pi.single_apply, Fin.castSucc_inj, Fin.castSucc_ne_last,
      if_false, add_zero, smul_eq_mul, mul_zero, Letters.snoc, Fin.lastCases_castSucc] at this
    exact this
  · have := congrFun hd (Fin.castSucc (Fin.last N))
    simp only [Pi.add_apply, Pi.smul_apply, eWY, Pi.single_apply, Fin.castSucc_ne_last, if_true, if_false,
      add_zero, smul_eq_mul, mul_one, Letters.snoc, Fin.lastCases_castSucc] at this
    omega
  · have := congrFun hd (Fin.last (N + 1))
    simp only [Pi.add_apply, Pi.smul_apply, eWY, Pi.single_apply, hne, if_true, if_false,
      zero_add, smul_eq_mul, mul_one, Letters.snoc, Fin.lastCases_last] at this
    omega

end term

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM.gammaIntegralityLemmas

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [hp : Fact p.Prime]

section term2
variable {N r : ℕ}

theorem fock_zero_right' {σ : Type} [Fintype σ] [DecidableEq σ] (F : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p F 0 = 0 := by
  simp [Formalism.GM.M.fock]

theorem kap_ge (N r B : ℕ) (hr : 1 ≤ r) : (N + 4) * (r * B) + 6 * B ≤ kap N r B := by
  unfold kap
  have h1 : r ≤ r ^ 2 := by nlinarith
  have h2 : B ≤ r * B := Nat.le_mul_of_pos_left B hr
  have h3 : (N + 4) * (r * B) + 6 * B ≤ 10 * (N + 3) * (r * B) := by nlinarith
  have h4 : 10 * (N + 3) * (r * B) ≤ 10 * (N + 3) * r ^ 2 * (B + 1) := by
    have : r * B ≤ r ^ 2 * (B + 1) := by nlinarith
    calc 10 * (N + 3) * (r * B) ≤ 10 * (N + 3) * (r ^ 2 * (B + 1)) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  omega

theorem term_val (LL : Letters (N + 1)) (hr : 1 ≤ r) (B : ℕ)
    (hB : Nat.log p (LL.total + LL.deg (Fin.last N) + r) ≤ B) (j a a' : ℕ)
    (hj : j ≤ LL.deg (Fin.last N)) (ha : a ≤ j) (ha' : a' ≤ j)
    (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ)
    (hk : ∀ k : Fin N, δv δ (Fin.castSucc (Fin.castSucc k)) = LL.deg (Fin.castSucc k))
    (hW : δv δ (Fin.castSucc (Fin.last N)) = LL.deg (Fin.last N) - j)
    (hY : δv δ (Fin.last (N + 1)) = LL.total - (j - a))
    (d1 d2 : ℕ) (hd1 : padicValNat p a.factorial ≤ padicValNat p d1) (hd1' : d1 ≠ 0)
    (hd2 : padicValNat p a'.factorial ≤ padicValNat p d2) (hd2' : d2 ≠ 0) :
    -(kap N r B : ℤ) + ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a).factorial : ℤ))) +
      ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a').factorial : ℤ))) -
      (padicValNat p (j.choose a * j.choose a' * d1 * d2 * a'.factorial *
        ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) : ℤ) +
      (padicValNat p ((LL.deg (Fin.last N)).choose j * j.factorial ^ 2 * LL.total.factorial *
        ∏ i, (LL.deg i).factorial) : ℤ) ≤ 0 := by
  set o := LL.deg (Fin.last N) with ho
  set S := LL.total with hS
  have hoS : o ≤ S := deg_le_total LL (Fin.last N)
  set T := S + o + r
  have hjo : j ≤ o := hj

  have nz1 : j.choose a ≠ 0 := (Nat.choose_pos ha).ne'
  have nz2 : j.choose a' ≠ 0 := (Nat.choose_pos ha').ne'
  have nzW : (∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')
  have vN : padicValNat p (j.choose a * j.choose a' * d1 * d2 * a'.factorial *
      ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) =
      padicValNat p (j.choose a) + padicValNat p (j.choose a') + padicValNat p d1 + padicValNat p d2 +
        padicValNat p a'.factorial + padicValNat p (∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) := by
    rw [padicValNat.mul (by positivity) nzW, padicValNat.mul (by positivity) (Nat.factorial_pos _).ne',
      padicValNat.mul (by positivity) hd2', padicValNat.mul (by positivity) hd1',
      padicValNat.mul nz1 nz2]

  have nzC : o.choose j ≠ 0 := (Nat.choose_pos hjo).ne'
  have nzD : (∏ i, (LL.deg i).factorial) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')
  have vD : padicValNat p (o.choose j * j.factorial ^ 2 * S.factorial * ∏ i, (LL.deg i).factorial) =
      padicValNat p (o.choose j) + 2 * padicValNat p j.factorial + padicValNat p S.factorial +
        ∑ i, padicValNat p (LL.deg i).factorial := by
    rw [padicValNat.mul (by positivity) nzD, padicValNat.mul (by positivity) (Nat.factorial_pos _).ne',
      padicValNat.mul nzC (by positivity), padicValNat.pow,
      v_prod _ _ (fun i _ => (Nat.factorial_pos _).ne')]
  have vDn : ∑ i, padicValNat p (LL.deg i).factorial =
      ∑ k : Fin N, padicValNat p (LL.deg (Fin.castSucc k)).factorial + padicValNat p o.factorial := by
    rw [Fin.sum_univ_castSucc]

  have hTδ : ∀ i, δv δ i ≤ T := by
    intro i
    induction i using Fin.lastCases with
    | last => rw [hY]; omega
    | cast i =>
      induction i using Fin.lastCases with
      | last => rw [hW]; omega
      | cast k => rw [hk k]; have := deg_le_total LL (Fin.castSucc k); omega
  have hlog : Nat.log p T ≤ B := hB
  have vW := vW_ge (p := p) δ hlog hTδ
  have vS : ∑ i, padicValNat p (δv δ i).factorial =
      ∑ k : Fin N, padicValNat p (LL.deg (Fin.castSucc k)).factorial + padicValNat p (o - j).factorial +
        padicValNat p (S - (j - a)).factorial := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hW, hY]
    simp only [hk]

  have F1 : padicValNat p j.factorial ≤ padicValNat p a.factorial + padicValNat p (j - a).factorial + B := by
    have := vfact_split (p := p) (a := a) (b := j - a) (T := T) (by omega) hlog
    rwa [show a + (j - a) = j by omega] at this
  have F2 : padicValNat p j.factorial ≤ padicValNat p a'.factorial + padicValNat p (j - a').factorial + B := by
    have := vfact_split (p := p) (a := a') (b := j - a') (T := T) (by omega) hlog
    rwa [show a' + (j - a') = j by omega] at this
  have F3 : padicValNat p o.factorial ≤ padicValNat p (o - j).factorial + padicValNat p j.factorial + B := by
    have := vfact_split (p := p) (a := o - j) (b := j) (T := T) (by omega) hlog
    rwa [show o - j + j = o by omega] at this
  have F4 : padicValNat p S.factorial ≤ padicValNat p (S - (j - a)).factorial + padicValNat p (j - a).factorial + B := by
    have := vfact_split (p := p) (a := S - (j - a)) (b := j - a) (T := T) (by omega) hlog
    rwa [show S - (j - a) + (j - a) = S by omega] at this
  have F5 : padicValNat p (o.choose j) ≤ B := vchoose_le (show o ≤ T by omega) hlog
  have hk' := kap_ge N r B hr
  rw [vN, vD, vDn]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum]
  have hk'' : (((N + 4) * (r * B) + 6 * B : ℕ) : ℤ) ≤ (kap N r B : ℤ) := by exact_mod_cast hk'
  push_cast at hk''
  have vW' : (∑ i, (padicValNat p (δv δ i).factorial : ℤ)) ≤
      (padicValNat p (∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) : ℤ) + (N + 2) * (r * B) := by
    exact_mod_cast vW
  have vS' : (∑ i, (padicValNat p (δv δ i).factorial : ℤ)) =
      (∑ k : Fin N, (padicValNat p (LL.deg (Fin.castSucc k)).factorial : ℤ)) + (padicValNat p (o - j).factorial : ℤ) +
        (padicValNat p (S - (j - a)).factorial : ℤ) := by exact_mod_cast vS
  have F1' : (padicValNat p j.factorial : ℤ) ≤ padicValNat p a.factorial + padicValNat p (j - a).factorial + B := by
    exact_mod_cast F1
  have F2' : (padicValNat p j.factorial : ℤ) ≤ padicValNat p a'.factorial + padicValNat p (j - a').factorial + B := by
    exact_mod_cast F2
  have F3' : (padicValNat p o.factorial : ℤ) ≤ padicValNat p (o - j).factorial + padicValNat p j.factorial + B := by
    exact_mod_cast F3
  have F4' : (padicValNat p S.factorial : ℤ) ≤ padicValNat p (S - (j - a)).factorial + padicValNat p (j - a).factorial + B := by
    exact_mod_cast F4
  have F5' : (padicValNat p (o.choose j) : ℤ) ≤ B := by exact_mod_cast F5
  have hd1z : (padicValNat p a.factorial : ℤ) ≤ padicValNat p d1 := by exact_mod_cast hd1
  have hd2z : (padicValNat p a'.factorial : ℤ) ≤ padicValNat p d2 := by exact_mod_cast hd2
  have c1 : (0 : ℤ) ≤ padicValNat p (j.choose a) := by positivity
  have c2 : (0 : ℤ) ≤ padicValNat p (j.choose a') := by positivity
  linarith

end term2

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM.gammaIntegralityLemmas

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [hp : Fact p.Prime]

section term3
variable {N r : ℕ}

theorem termF_IVP (LL : Letters (N + 1)) (ρ : Fin r) (hr : 1 ≤ r) (B : ℕ)
    (hB : Nat.log p (LL.total + LL.deg (Fin.last N) + r) ≤ B) (z j a a' : ℕ)
    (hj : j ≤ LL.deg (Fin.last N)) (ha : a ≤ j) (ha' : a' ≤ j)
    (β γ : Fin (N + 1 + 1) × Fin r →₀ ℕ)
    (hβd : δv β + (j - a) • eWY = (LL.snoc LL.total).deg) (hβp : β (xW ρ) ≤ β (yE ρ))
    (hγd : δv γ + (j - a') • eWY = (LL.snoc LL.total).deg) (hγp : γ (xW ρ) ≤ γ (yE ρ))
    (h h' : ℚ_[p])
    (hh : ‖h‖ ≤ (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a).factorial : ℤ))))
    (hh' : ‖h'‖ ≤ (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a').factorial : ℤ)))) :
    IVP p (LL.total + LL.deg (Fin.last N))
      (fun m => (p : ℚ_[p]) ^ (kap N r B) * termF LL ρ z j a a' β γ h h' m) := by
  have hxy := xW_ne_yE (N := N) ρ
  set s : Fin (N + 1 + 1) × Fin r →₀ ℕ := Finsupp.single (xW ρ) 1 + Finsupp.single (yE ρ) 1 with hs
  by_cases h1 : β (xW ρ) < a
  · apply (IVP.zero (p := p) _).congr
    intro m
    unfold termF
    rw [X_pow_mul_monomial, Dop_pow_monomial_lt _ _ hxy a _ h
      (by simp [Finsupp.single_apply, hxy]; exact h1), fock_zero_left]
    simp
  by_cases h2 : γ (xW ρ) < a'
  · apply (IVP.zero (p := p) _).congr
    intro m
    unfold termF
    rw [X_pow_mul_monomial (yE ρ) m γ, Dop_pow_monomial_lt _ _ hxy a' _ h'
      (by simp [Finsupp.single_apply, hxy]; exact h2), fock_zero_right']
    simp
  push_neg at h1 h2
  have hle : ∀ (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ) (t : ℕ), t ≤ δ (xW ρ) → δ (xW ρ) ≤ δ (yE ρ) → t • s ≤ δ := by
    intro δ t ht1 ht2 v
    simp only [hs, Finsupp.smul_apply, Finsupp.add_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases hv1 : xW ρ = v
    · subst hv1; simp [Ne.symm hxy]; exact ht1
    · by_cases hv2 : yE ρ = v
      · subst hv2; simp [hv1]; omega
      · simp [hv1, hv2]
  obtain ⟨β₀, rfl⟩ : ∃ β₀, β = β₀ + a • s := ⟨β - a • s, (tsub_add_cancel_of_le (hle β a h1 hβp)).symm⟩
  obtain ⟨γ₀, rfl⟩ : ∃ γ₀, γ = γ₀ + a' • s := ⟨γ - a' • s, (tsub_add_cancel_of_le (hle γ a' h2 hγp)).symm⟩
  by_cases hb : β₀ = γ₀
  swap
  · apply (IVP.zero (p := p) _).congr
    intro m
    unfold termF
    rw [fock_Dop_term _ _ hxy, if_neg hb]
    simp
  subst hb
  set o := LL.deg (Fin.last N) with ho
  set S := LL.total with hS
  have hoS : o ≤ S := deg_le_total LL (Fin.last N)

  have hsδ : ∀ t : ℕ, δv (t • s) = Pi.single (Fin.castSucc (Fin.last N)) t + Pi.single (Fin.last (N + 1)) t := by
    intro t
    rw [hs, smul_add, Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, mul_one, δv_add,
      δv_single', δv_single']
  have hβd' : δv β₀ + Pi.single (Fin.castSucc (Fin.last N)) a + Pi.single (Fin.last (N + 1)) a + (j - a) • eWY =
      (LL.snoc LL.total).deg := by
    rw [← hβd, δv_add, hsδ, add_assoc (δv β₀)]
  obtain ⟨hk, hW, hY⟩ := comp_facts LL (j - a) β₀ a a hβd'
  set e := β₀ (yE ρ) + a with he
  set e' := β₀ (yE ρ) + a' with he'
  have heS : e ≤ S - (j - a) := by
    have := le_δv β₀ (Fin.last (N + 1)) ρ
    simp only [yE] at he
    omega
  set c1 := o + S + r + z - 1 - j with hc1
  set d1 := (β₀ (xW ρ) + a).descFactorial a with hd1
  set d2 := (β₀ (xW ρ) + a').descFactorial a' with hd2
  set δh := β₀ + Finsupp.single (yE ρ) a with hδh
  set Num := j.choose a * j.choose a' * d1 * d2 * a'.factorial * ∏ v : Fin (N + 1 + 1) × Fin r, (δh v).factorial
    with hNum
  set Den := o.choose j * j.factorial ^ 2 * S.factorial * ∏ i, (LL.deg i).factorial with hDen
  set K : ℚ_[p] := (p : ℚ_[p]) ^ (kap N r B) * ((-1 : ℚ_[p]) ^ j * h * h' * (Num : ℚ_[p]) / (Den : ℚ_[p]))
    with hK
  have nd1 : d1 ≠ 0 := by
    rw [hd1]; intro h0; rw [Nat.descFactorial_eq_zero_iff_lt] at h0; omega
  have nd2 : d2 ≠ 0 := by
    rw [hd2]; intro h0; rw [Nat.descFactorial_eq_zero_iff_lt] at h0; omega
  have hNum0 : Num ≠ 0 := by
    rw [hNum]
    refine Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero
      (Nat.choose_pos ha).ne' (Nat.choose_pos ha').ne') nd1) nd2) (Nat.factorial_pos _).ne') ?_
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')
  have hDen0 : Den ≠ 0 := by
    rw [hDen]
    refine Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.choose_pos hj).ne'
      (pow_ne_zero _ (Nat.factorial_pos _).ne')) (Nat.factorial_pos _).ne') ?_
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')

  have hδv : δv δh = δv β₀ + Pi.single (Fin.last (N + 1)) a := by rw [hδh, δv_add, δv_single']
  have hne : ∀ k : Fin (N + 1), (Fin.last (N + 1) : Fin (N + 1 + 1)) ≠ Fin.castSucc k :=
    fun k h => Fin.castSucc_ne_last k h.symm
  have hKn : ‖K‖ ≤ 1 := by
    rw [hK]
    refine norm_K _ h h' _ _ hh hh' Num Den hNum0 hDen0 _ (by simp) ?_
    rw [hNum, hDen]
    refine term_val LL hr B hB j a a' hj ha ha' δh ?_ ?_ ?_ d1 d2 ?_ nd1 ?_ nd2
    · intro k
      rw [hδv, Pi.add_apply, Pi.single_apply, if_neg (hne _).symm, add_zero, hk k]
    · rw [hδv, Pi.add_apply, Pi.single_apply, if_neg (Fin.castSucc_ne_last _), add_zero]; omega
    · rw [hδv, Pi.add_apply, Pi.single_apply, if_pos rfl]; omega
    · rw [hd1]; exact vdesc_ge _ _ (by omega)
    · rw [hd2]; exact vdesc_ge _ _ (by omega)
  have I1 := ((IVP.choose_add (p := p) c1 (o - j)).mul (IVP.choose_add e e)).mul (IVP.choose_add e' a')
  refine ((I1.smul K hKn).mono (by omega)).congr ?_
  intro m
  unfold termF
  rw [fock_Dop_term _ _ hxy, if_pos rfl, Nat.add_sub_cancel]
  have hjM : j ≤ o + (m + S) + r + z - 1 := by omega
  have hMj : o + (m + S) + r + z - 1 - j = m + c1 := by omega
  have hMo : (((o + (m + S) + r + z - 1).choose o : ℕ) : ℚ_[p]) =
      (((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p]) *
        (((o + (m + S) + r + z - 1 - j).choose (o - j) : ℕ) : ℚ_[p]) / ((o.choose j : ℕ) : ℚ_[p]) := by
    have := Nat.choose_mul (n := o + (m + S) + r + z - 1) (k := o) (s := j) hj
    rw [eq_div_iff (by exact_mod_cast (Nat.choose_pos hj).ne')]
    exact_mod_cast this
  rw [hMo, hMj, Nat.descFactorial_eq_factorial_mul_choose (m + e') a']
  have hwf : wf (p := p) δh = ((∏ v : Fin (N + 1 + 1) × Fin r, (δh v).factorial : ℕ) : ℚ_[p]) := by
    unfold wf; push_cast; rfl
  rw [hwf, hK, hNum, hDen]
  have n1 : (((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hjM).ne'
  have n2 : ((o.choose j : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.choose_pos hj).ne'
  have n3 : ((j.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have n4 : ((S.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have n5 : ((m.factorial : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have n6 : ((∏ i, (LL.deg i).factorial : ℕ) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun v _ => (Nat.factorial_pos _).ne')
  push_cast at n6 ⊢
  rw [← hd1, ← hd2, ← he, ← ho, ← hS]
  have hc := mul_inv_cancel₀ n1
  have hm := mul_inv_cancel₀ n5
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination (-((p : ℚ_[p]) ^ kap N r B * (-1 : ℚ_[p]) ^ j * h * h' * ((j.choose a : ℕ) : ℚ_[p]) *
      ((j.choose a' : ℕ) : ℚ_[p]) * (d1 : ℚ_[p]) * (d2 : ℚ_[p]) * ((a'.factorial : ℕ) : ℚ_[p]) *
      (∏ i, (((δh i).factorial : ℕ) : ℚ_[p])) * (((m + c1).choose (o - j) : ℕ) : ℚ_[p]) *
      (((m + e).choose e : ℕ) : ℚ_[p]) * (((m + e').choose a' : ℕ) : ℚ_[p]) * ((o.choose j : ℕ) : ℚ_[p])⁻¹ *
      (((j.factorial : ℕ) : ℚ_[p]) ^ 2)⁻¹ * ((S.factorial : ℕ) : ℚ_[p])⁻¹ *
      (∏ i, (((LL.deg i).factorial : ℕ) : ℚ_[p]))⁻¹)) * hc +
    (-((p : ℚ_[p]) ^ kap N r B * (-1 : ℚ_[p]) ^ j * h * h' * ((j.choose a : ℕ) : ℚ_[p]) *
      ((j.choose a' : ℕ) : ℚ_[p]) * (d1 : ℚ_[p]) * (d2 : ℚ_[p]) * ((a'.factorial : ℕ) : ℚ_[p]) *
      (∏ i, (((δh i).factorial : ℕ) : ℚ_[p])) * (((m + c1).choose (o - j) : ℕ) : ℚ_[p]) *
      (((m + e).choose e : ℕ) : ℚ_[p]) * (((m + e').choose a' : ℕ) : ℚ_[p]) * ((o.choose j : ℕ) : ℚ_[p])⁻¹ *
      (((j.factorial : ℕ) : ℚ_[p]) ^ 2)⁻¹ * ((S.factorial : ℕ) : ℚ_[p])⁻¹ *
      (∏ i, (((LL.deg i).factorial : ℕ) : ℚ_[p]))⁻¹) *
      ((((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p]) * (((o + (m + S) + r + z - 1).choose j : ℕ) : ℚ_[p])⁻¹)) * hm

end term3

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM.gammaIntegralityLemmas

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [hp : Fact p.Prime]

section expand
variable {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} (w e : Fin r → σ) (ρ : Fin r)

theorem tieF_pow_apply (j : ℕ) (Z : MvPolynomial σ ℚ_[p]) :
    (Formalism.GM.tieF w e ^ j) Z = ∑ a ∈ range (j + 1),
      ((j.choose a : ℕ) : ℚ_[p]) • (Dop (w ρ) (e ρ) ^ a) ((FT w e (univ.erase ρ) ^ (j - a)) Z) := by
  rw [tieF_split w e ρ, (FT_commute w e (w ρ) (e ρ) (univ.erase ρ)).add_pow j, LinearMap.sum_apply]
  apply sum_congr rfl
  intro a _
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, map_nsmul,
    Nat.cast_smul_eq_nsmul]

theorem fock_F_pow_expand (hy : ∀ c ∈ univ.erase ρ, w c ≠ e ρ ∧ e c ≠ e ρ)
    (G G' : MvPolynomial σ ℚ_[p]) (j m : ℕ) :
    Formalism.GM.M.fock p ((Formalism.GM.tieF w e ^ j) (X (e ρ) ^ m * G)) ((Formalism.GM.tieF w e ^ j) (X (e ρ) ^ m * G')) =
      ∑ a ∈ range (j + 1), ∑ a' ∈ range (j + 1),
        ∑ β ∈ ((FT w e (univ.erase ρ) ^ (j - a)) G).support,
          ∑ γ ∈ ((FT w e (univ.erase ρ) ^ (j - a')) G').support,
            (((j.choose a : ℕ) : ℚ_[p]) * ((j.choose a' : ℕ) : ℚ_[p]) *
              Formalism.GM.M.fock p ((Dop (w ρ) (e ρ) ^ a) (X (e ρ) ^ m *
                        monomial β (coeff β ((FT w e (univ.erase ρ) ^ (j - a)) G))))
                ((Dop (w ρ) (e ρ) ^ a') (X (e ρ) ^ m *
                  monomial γ (coeff γ ((FT w e (univ.erase ρ) ^ (j - a')) G'))))) := by
  rw [tieF_pow_apply w e ρ, tieF_pow_apply w e ρ, fock_sum_left]
  apply sum_congr rfl; intro a _
  rw [fock_sum_right]
  apply sum_congr rfl; intro a' _
  rw [fock_smul_left, fock_smul_right, FT_pow_X_pow_mul w e (e ρ) _ hy, FT_pow_X_pow_mul w e (e ρ) _ hy]
  conv_lhs => rw [((FT w e (univ.erase ρ) ^ (j - a)) G).as_sum, ((FT w e (univ.erase ρ) ^ (j - a')) G').as_sum]
  rw [mul_sum, mul_sum, map_sum, map_sum, fock_sum_left, mul_sum, mul_sum]
  apply sum_congr rfl; intro β _
  rw [fock_sum_right, mul_sum, mul_sum]
  apply sum_congr rfl; intro γ _
  ring

end expand

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM.gammaIntegralityLemmas

open MvPolynomial Finset Formalism.GM.M

variable {p : ℕ} [hp : Fact p.Prime]

section final
variable {N r : ℕ}

abbrev wv : Fin r → Fin (N + 1 + 1) × Fin r := fun c => (Fin.castSucc (Fin.last N), c)
abbrev ev : Fin r → Fin (N + 1 + 1) × Fin r := fun c => (Fin.last (N + 1), c)

theorem hy_wv (ρ : Fin r) : ∀ c ∈ univ.erase ρ, wv (N := N) c ≠ ev ρ ∧ ev (N := N) c ≠ ev ρ := by
  intro c hc
  refine ⟨?_, ?_⟩
  · simp [wv, ev, Fin.castSucc_ne_last]
  · simp only [ev, ne_eq, Prod.mk.injEq, true_and]; exact ne_of_mem_erase hc

theorem tieGam_expand (LL : Letters (N + 1)) (ρ : Fin r) (z : ℕ)
    (f f' : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (m : ℕ) :
    tieGam p LL ρ z (m + LL.total) f f' =
      ∑ j ∈ range (LL.deg (Fin.last N) + 1), ∑ a ∈ range (j + 1), ∑ a' ∈ range (j + 1),
        ∑ β ∈ ((FT wv ev (univ.erase ρ) ^ (j - a)) (aeval (freezeSub p LL ρ) f)).support,
          ∑ γ ∈ ((FT wv ev (univ.erase ρ) ^ (j - a')) (aeval (freezeSub p LL ρ) f')).support,
            termF LL ρ z j a a' β γ (coeff β ((FT wv ev (univ.erase ρ) ^ (j - a)) (aeval (freezeSub p LL ρ) f)))
              (coeff γ ((FT wv ev (univ.erase ρ) ^ (j - a')) (aeval (freezeSub p LL ρ) f'))) m := by
  have hdeg1 : (LL.snoc (m + LL.total)).deg (Fin.castSucc (Fin.last N)) = LL.deg (Fin.last N) := by
    simp [Letters.snoc]
  have hdeg2 : (LL.snoc (m + LL.total)).deg (Fin.last (N + 1)) = m + LL.total := by
    simp [Letters.snoc]
  unfold tieGam tiePhiAt freeze termF
  rw [hdeg1, hdeg2]
  unfold Formalism.GM.tiePhi
  rw [LinearMap.sum_apply, fock_sum_left, mul_sum, sum_div]
  apply sum_congr rfl; intro j _
  rw [LinearMap.smul_apply, LinearMap.comp_apply, fock_smul_left, fock_E_pow wv ev]
  simp only [Nat.add_sub_cancel]
  rw [fock_F_pow_expand wv ev ρ (hy_wv ρ)]
  simp only [mul_sum, sum_div]

end final

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM.gammaIntegralityLemmas

open MvPolynomial Finset Formalism.GM.M

theorem gamma_integrality_of_contraction : GamInt := by
  refine ⟨10, ?_⟩
  intro p _ N r LL ρ z f f' hr hW hf hf'
  set B := Nat.log p (LL.total + LL.deg (Fin.last N) + r) with hB
  have hκ : 10 * (N + 3) * r ^ 2 * (B + 1) = kap N r B := rfl
  have hwe : ∀ c : Fin r, wv (N := N) c ≠ ev c := by
    intro c; simp [wv, ev, Fin.castSucc_ne_last]

  have facts : ∀ g : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p], g ∈ PolZ p r LL →
      (∀ b ≤ LL.total + LL.deg (Fin.last N) + r, ∀ β,
        ‖coeff β ((FT wv ev (univ.erase ρ) ^ b) (aeval (freezeSub p LL ρ) g))‖ ≤
          (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p b.factorial : ℤ)))) ∧
      (∀ b, ∀ β ∈ ((FT wv ev (univ.erase ρ) ^ b) (aeval (freezeSub p LL ρ) g)).support,
        δv β + b • eWY = (LL.snoc LL.total).deg ∧ β (xW ρ) ≤ β (yE ρ)) := by
    intro g hg
    have hgP : g ∈ Pol p r LL := (Submodule.mem_inf.mp hg).1
    have hgI : g ∈ IntPol p (Fin (N + 1) × Fin r) := (Submodule.mem_inf.mp hg).2
    have hG := aeval_int LL ρ g (intPol_coeff g hgI)
    have hGg := aeval_good LL ρ hW g hgP
    refine ⟨fun b hb β => ?_, ?_⟩
    · have h1 := FT_pow_coeff_norm (p := p) wv ev hwe (LL.total + LL.deg (Fin.last N) + r) B le_rfl 1
        (aeval (freezeSub p LL ρ) g) hG (univ.erase ρ) b hb β
      refine h1.trans ?_
      rw [one_mul]
      apply zpow_mono'
      have : (univ.erase ρ).card * B ≤ r * B := by
        apply Nat.mul_le_mul_right
        rw [card_erase_of_mem (mem_univ ρ), card_univ, Fintype.card_fin]; omega
      have : (((univ.erase ρ).card * B : ℕ) : ℤ) ≤ ((r * B : ℕ) : ℤ) := by exact_mod_cast this
      linarith
    · refine supp_FT_pow wv ev (univ.erase ρ)
        (fun b β => δv β + b • eWY = (LL.snoc LL.total).deg ∧ β (xW ρ) ≤ β (yE ρ)) ?_ hwe _ ?_
      · intro b β c hc ⟨h1, h2⟩
        have hcρ : c ≠ ρ := ne_of_mem_erase hc
        refine ⟨?_, ?_⟩
        · rw [← h1, δv_add, δv_add, δv_single, δv_single, succ_nsmul, eWY]
          abel
        · simpa [Finsupp.single_apply, xW, yE, wv, ev, hcρ, Ne.symm hcρ, Fin.castSucc_ne_last] using h2
      · intro β hβ
        obtain ⟨h1, h2⟩ := hGg β hβ
        exact ⟨by rw [zero_smul, add_zero]; exact h1, h2⟩
  obtain ⟨hc1, hs1⟩ := facts f hf
  obtain ⟨hc2, hs2⟩ := facts f' hf'
  have hIVP : IVP p (LL.total + LL.deg (Fin.last N))
      (fun m => (p : ℚ_[p]) ^ (kap N r B) * tieGam p LL ρ z (m + LL.total) f f') := by
    simp only [tieGam_expand, Finset.mul_sum]
    apply IVP.sum; intro j hj
    apply IVP.sum; intro a ha
    apply IVP.sum; intro a' ha'
    apply IVP.sum; intro β hβ
    apply IVP.sum; intro γ hγ
    rw [mem_range] at hj ha ha'
    have hjo : j ≤ LL.deg (Fin.last N) := by omega
    have hoS := deg_le_total LL (Fin.last N)
    obtain ⟨hβd, hβp⟩ := hs1 (j - a) β hβ
    obtain ⟨hγd, hγp⟩ := hs2 (j - a') γ hγ
    exact termF_IVP LL ρ hr B le_rfl z j a a' hjo (by omega) (by omega) β γ hβd hβp hγd hγp _ _
      (hc1 (j - a) (by omega) β) (hc2 (j - a') (by omega) γ)
  obtain ⟨c, hc⟩ := hIVP.toChoose (S := LL.total)
  refine ⟨c, fun n hn => ?_⟩
  have := hc n hn
  simp only [Nat.sub_add_cancel hn] at this
  rw [hκ]
  exact this

end Formalism.GM.gammaIntegralityLemmas

namespace Formalism.GM

theorem gamma_integrality : M.GamInt := gammaIntegralityLemmas.gamma_integrality_of_contraction

end Formalism.GM
