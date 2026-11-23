import Mathlib

open Filter Topology Polynomial

namespace GlobalTheory.SimpleRoots

variable {d : ℕ}

theorem eval_map_eq_sum (p : Polynomial (MvPolynomial (Fin d) ℂ)) (x : Fin d → ℂ) (y : ℂ) :
    (p.map (MvPolynomial.eval x)).eval y
      = ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval x (p.coeff i) * y ^ i := by
  rw [eval_map, eval₂_eq_sum_range]

theorem analyticAt_mvPolynomial_eval (a : MvPolynomial (Fin d) ℂ) (x : Fin d → ℂ) :
    AnalyticAt ℂ (fun x : Fin d → ℂ => MvPolynomial.eval x a) x :=
  AnalyticOnNhd.eval_mvPolynomial a x (Set.mem_univ x)

theorem analyticAt_eval_map (p : Polynomial (MvPolynomial (Fin d) ℂ)) (z : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (fun w : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval w.1)).eval w.2) z := by
  simp only [eval_map_eq_sum]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact ((analyticAt_mvPolynomial_eval _ _).comp analyticAt_fst).mul (analyticAt_snd.pow i)

theorem exists_analytic_root (p : Polynomial (MvPolynomial (Fin d) ℂ)) {x₀ : Fin d → ℂ} {y₀ : ℂ}
    (h0 : (p.map (MvPolynomial.eval x₀)).eval y₀ = 0)
    (h1 : (p.map (MvPolynomial.eval x₀)).derivative.eval y₀ ≠ 0) :
    ∃ ψ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ ψ x₀ ∧ ψ x₀ = y₀ ∧
      (∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ x) = 0) ∧
      ∀ᶠ w in 𝓝 (x₀, y₀), (p.map (MvPolynomial.eval w.1)).eval w.2 = 0 ↔ ψ w.1 = w.2 := by
  set f : (Fin d → ℂ) × ℂ → ℂ := fun w => (p.map (MvPolynomial.eval w.1)).eval w.2 with hf
  have ha : AnalyticAt ℂ f (x₀, y₀) := analyticAt_eval_map p _
  have hc : ContDiffAt ℂ ⊤ f (x₀, y₀) := ha.contDiffAt
  have hd : HasFDerivAt (fun y : ℂ => f (x₀, y))
      (fderiv ℂ f (x₀, y₀) ∘L .inr ℂ (Fin d → ℂ) ℂ) y₀ :=
    ha.differentiableAt.hasFDerivAt.comp y₀ (hasFDerivAt_prodMk_right x₀ y₀)
  have hd' := ((p.map (MvPolynomial.eval x₀)).hasDerivAt y₀).hasFDerivAt
  have he := hd.unique hd'
  have hi : (fderiv ℂ f (x₀, y₀) ∘L .inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [he]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩
    ext
    simp
  refine ⟨hc.implicitFunction (by simp) hi, ?_, hc.implicitFunction_apply_self (by simp) hi, ?_, ?_⟩
  · exact (hc.contDiffAt_implicitFunction (by simp) hi).analyticAt
  · filter_upwards [hc.eventually_apply_implicitFunction (by simp) hi] with x hx
    exact hx.trans h0
  · filter_upwards [hc.eventually_apply_eq_iff_implicitFunction (by simp) hi] with w hw
    rw [← hw]
    exact Iff.of_eq (congrArg _ h0.symm)

theorem nodup_roots_of_derivative_ne_zero {P : ℂ[X]} (hP : P ≠ 0)
    (h : ∀ y, P.eval y = 0 → P.derivative.eval y ≠ 0) : P.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro y
  rw [count_roots]
  by_contra hy
  obtain ⟨h1, h2⟩ := (one_lt_rootMultiplicity_iff_isRoot hP).mp (not_le.mp hy)
  exact h y h1 h2

theorem exists_analytic_roots {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic)
    {x₀ : Fin d → ℂ}
    (h : ∀ y, (p.map (MvPolynomial.eval x₀)).eval y = 0 →
      (p.map (MvPolynomial.eval x₀)).derivative.eval y ≠ 0) :
    ∃ ψ : ℂ → (Fin d → ℂ) → ℂ,
      (∀ y ∈ (p.map (MvPolynomial.eval x₀)).roots, AnalyticAt ℂ (ψ y) x₀ ∧ ψ y x₀ = y) ∧
      ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).roots
        = (p.map (MvPolynomial.eval x₀)).roots.map fun y => ψ y x := by
  classical
  have hne : ∀ x, p.map (MvPolynomial.eval x) ≠ 0 := fun x => (hp.map _).ne_zero
  have hex : ∀ y, ∃ ψ : (Fin d → ℂ) → ℂ, y ∈ (p.map (MvPolynomial.eval x₀)).roots →
      AnalyticAt ℂ ψ x₀ ∧ ψ x₀ = y ∧
        ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (ψ x) = 0 := by
    intro y
    by_cases hy : y ∈ (p.map (MvPolynomial.eval x₀)).roots
    · have hy' := (mem_roots (hne x₀)).mp hy
      obtain ⟨ψ, h1, h2, h3, -⟩ := exists_analytic_root p hy' (h y hy')
      exact ⟨ψ, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun hy' => absurd hy' hy⟩
  choose ψ hψ using hex
  refine ⟨ψ, fun y hy => ⟨(hψ y hy).1, (hψ y hy).2.1⟩, ?_⟩
  set S := (p.map (MvPolynomial.eval x₀)).roots with hS
  have hnd : S.Nodup := nodup_roots_of_derivative_ne_zero (hne x₀) h
  have hcard : ∀ x, (p.map (MvPolynomial.eval x)).roots.card = p.natDegree := fun x => by
    rw [← hp.natDegree_map (MvPolynomial.eval x)]
    exact (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
  have e1 : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ S.toFinset, (p.map (MvPolynomial.eval x)).eval (ψ y x) = 0 :=
    (Finset.eventually_all _).mpr fun y hy => (hψ y (Multiset.mem_toFinset.mp hy)).2.2
  have e2 : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ S.toFinset, ∀ y' ∈ S.toFinset, y ≠ y' → ψ y x ≠ ψ y' x := by
    refine (Finset.eventually_all _).mpr fun y hy => (Finset.eventually_all _).mpr fun y' hy' => ?_
    by_cases hyy : y = y'
    · exact Eventually.of_forall fun _ hn => absurd hyy hn
    · obtain ⟨a1, a2, -⟩ := hψ y (Multiset.mem_toFinset.mp hy)
      obtain ⟨b1, b2, -⟩ := hψ y' (Multiset.mem_toFinset.mp hy')
      have := (a1.continuousAt.ne_iff_eventually_ne b1.continuousAt).mp (by rwa [a2, b2])
      exact this.mono fun x hx _ => hx
  filter_upwards [e1, e2] with x h1 h2
  symm
  refine Multiset.eq_of_le_of_card_le ?_ ?_
  · refine (Multiset.le_iff_subset (hnd.map_on fun y hy y' hy' hyy => ?_)).mpr fun t ht => ?_
    · by_contra hn
      exact h2 y (Multiset.mem_toFinset.mpr hy) y' (Multiset.mem_toFinset.mpr hy') hn hyy
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp ht
      exact (mem_roots (hne x)).mpr (h1 y (Multiset.mem_toFinset.mpr hy))
  · rw [Multiset.card_map, hcard, hS, hcard]

theorem differentiableAt_coeff_prod {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : Multiset ι) (ψ : ι → E → ℂ) {x₀ : E} (h : ∀ y ∈ T, DifferentiableAt ℂ (ψ y) x₀) (k : ℕ) :
    DifferentiableAt ℂ (fun x => (T.map fun y => X - C (ψ y x)).prod.coeff k) x₀ := by
  induction T using Multiset.induction_on generalizing k with
  | empty => simp
  | cons a T ih =>
    have ha := h a (Multiset.mem_cons_self a T)
    have ih' := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    simp only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul]
    refine DifferentiableAt.sub ?_ (ha.mul (ih' k))
    cases k with
    | zero => simp
    | succ k => simpa only [coeff_X_mul] using ih' k

theorem norm_coeff_prod_le (T : Multiset ℂ) {R : ℝ} (hR : 0 ≤ R) (h : ∀ y ∈ T, ‖y‖ ≤ R) (k : ℕ) :
    ‖(T.map fun y => X - C y).prod.coeff k‖ ≤ (1 + R) ^ T.card := by
  induction T using Multiset.induction_on generalizing k with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one, Multiset.card_zero, pow_zero]
    split_ifs <;> simp
  | cons a T ih =>
    have ha := h a (Multiset.mem_cons_self a T)
    have ih' := ih fun y hy => h y (Multiset.mem_cons_of_mem hy)
    simp only [Multiset.map_cons, Multiset.prod_cons, sub_mul, coeff_sub, coeff_C_mul,
      Multiset.card_cons]
    have h1 : ‖(X * (T.map fun y => X - C y).prod).coeff k‖ ≤ (1 + R) ^ T.card := by
      cases k with
      | zero => simp; positivity
      | succ k => simpa only [coeff_X_mul] using ih' k
    have h2 : ‖a * (T.map fun y => X - C y).prod.coeff k‖ ≤ R * (1 + R) ^ T.card := by
      rw [norm_mul]
      exact mul_le_mul ha (ih' k) (norm_nonneg _) hR
    refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq ?_)
    ring

theorem exists_norm_eval_le (a : MvPolynomial (Fin d) ℂ) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ x : Fin d → ℂ, ‖MvPolynomial.eval x a‖ ≤ C * (1 + ‖x‖) ^ m := by
  induction a using MvPolynomial.induction_on with
  | C c => exact ⟨‖c‖, 0, norm_nonneg _, fun x => by simp⟩
  | add a b ha hb =>
    obtain ⟨C₁, m₁, h₁, ha⟩ := ha
    obtain ⟨C₂, m₂, h₂, hb⟩ := hb
    refine ⟨C₁ + C₂, m₁ + m₂, by positivity, fun x => ?_⟩
    have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    rw [map_add, add_mul]
    refine (norm_add_le _ _).trans (add_le_add ((ha x).trans ?_) ((hb x).trans ?_))
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) h₁
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (by omega)) h₂
  | mul_X a i ha =>
    obtain ⟨C₁, m₁, h₁, ha⟩ := ha
    refine ⟨C₁, m₁ + 1, h₁, fun x => ?_⟩
    rw [map_mul, MvPolynomial.eval_X, norm_mul, pow_succ, ← mul_assoc]
    refine mul_le_mul (ha x) ?_ (norm_nonneg _) (by positivity)
    linarith [norm_le_pi_norm x i]

theorem norm_root_le {P : ℂ[X]} (hP : P.Monic) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i < P.natDegree, ‖P.coeff i‖ ≤ M) {y : ℂ} (hy : P.eval y = 0) : ‖y‖ ≤ M + 1 := by
  have h1 := IsRoot.norm_lt_cauchyBound hP.ne_zero hy
  lift M to NNReal using hM0
  have h2 : P.cauchyBound ≤ M + 1 := by
    unfold cauchyBound
    rw [hP.leadingCoeff, nnnorm_one, div_one]
    gcongr
    exact Finset.sup_le fun i hi => by exact_mod_cast hM i (Finset.mem_range.mp hi)
  exact_mod_cast (h1.trans_le h2).le

theorem exists_norm_root_le {p : Polynomial (MvPolynomial (Fin d) ℂ)} (hp : p.Monic) :
    ∃ (C : ℝ) (m : ℕ), 0 ≤ C ∧ ∀ (x : Fin d → ℂ) (y : ℂ),
      (p.map (MvPolynomial.eval x)).eval y = 0 → ‖y‖ ≤ C * (1 + ‖x‖) ^ m := by
  choose C m hC h using fun i => exists_norm_eval_le (p.coeff i)
  set s := Finset.range p.natDegree
  have hs : 0 ≤ ∑ i ∈ s, C i := Finset.sum_nonneg fun i _ => hC i
  refine ⟨∑ i ∈ s, C i + 1, ∑ i ∈ s, m i, by positivity, fun x y hy => ?_⟩
  have h1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have h2 := norm_root_le (hp.map _) (M := (∑ i ∈ s, C i) * (1 + ‖x‖) ^ (∑ i ∈ s, m i))
    (by positivity) (fun i hi => ?_) hy
  · rw [add_mul, one_mul]
    linarith [one_le_pow₀ h1 (n := ∑ i ∈ s, m i)]
  · rw [hp.natDegree_map] at hi
    have hi' : i ∈ s := Finset.mem_range.mpr hi
    rw [coeff_map]
    refine (h i x).trans (mul_le_mul (Finset.single_le_sum (fun j _ => hC j) hi')
      (pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le _) hi'))
      (by positivity) hs)

end GlobalTheory.SimpleRoots
