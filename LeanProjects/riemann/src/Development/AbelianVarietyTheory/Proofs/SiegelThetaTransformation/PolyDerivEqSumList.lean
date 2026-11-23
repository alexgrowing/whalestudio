import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivVanishesOfTranslationInvariance

open Filter Topology
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.SW.KernSym

variable {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

noncomputable abbrev lst (m : σ →₀ ℕ) : List σ := (Finsupp.toMultiset m).toList

theorem polyDeriv_eq_sum_list (P : MvPolynomial σ ℂ) (u : σ → W) {F : W → ℂ} {x : W}
    (hF : AnalyticAt ℂ F x) :
    polyDeriv P u F x = ∑ m ∈ P.support, P.coeff m * lineDerivList ℂ ((lst m).map u) F x := by
  rw [dirPolyDeriv_eq_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [dirPolyDeriv_monomial_eq_lineDerivList (Multiset.coe_toList _) u hF]

theorem polyDeriv_polyDeriv (P Q : MvPolynomial σ ℂ) (u : σ → W) {F : W × W → ℂ}
    (hF : ∀ p, AnalyticAt ℂ F p) :
    polyDeriv P u (fun z => polyDeriv Q u (fun w => F (z, w)) 0) 0 =
      ∑ m ∈ P.support, ∑ m' ∈ Q.support, P.coeff m * Q.coeff m' *
        lineDerivList ℂ ((lst m).map (fun s => (u s, 0)) ++ (lst m').map (fun s => (0, u s)))
          F 0 := by
  have h1 (z : W) : polyDeriv Q u (fun w => F (z, w)) 0 = ∑ m' ∈ Q.support, Q.coeff m' •
      lineDerivList ℂ ((lst m').map (fun s => (0, u s))) F (LinearMap.inl ℂ W W z) := by
    have ha : AnalyticAt ℂ (fun w => F (z, w)) 0 := (hF _).comp₂ analyticAt_const analyticAt_id
    rw [polyDeriv_eq_sum_list _ _ ha]
    refine Finset.sum_congr rfl fun m' _ => ?_
    have h2 := congrFun (lineDerivList_comp_linearMap (LinearMap.inr ℂ W W) ((lst m').map u)
      (fun p => F (p + (z, 0)))) 0
    rw [lineDerivList_comp_add_const] at h2
    simp only [LinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero, List.map_map] at h2
    rw [h2]
    rfl
  have h3 (m' : σ →₀ ℕ) : AnalyticAt ℂ (fun z => Q.coeff m' •
      lineDerivList ℂ ((lst m').map (fun s => (0, u s))) F (LinearMap.inl ℂ W W z)) 0 :=
    analyticAt_const.fun_smul
      ((analyticAt_lineDerivList (hF _) _).comp ((ContinuousLinearMap.inl ℂ W W).analyticAt 0))
  simp only [h1]
  rw [polyDeriv_eq_sum_list _ _ (Finset.analyticAt_fun_sum _ fun m' _ => h3 m')]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [lineDerivList_sum _ fun m' _ => h3 m', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [lineDerivList_const_smul, lineDerivList_comp_linearMap, lineDerivList_append, List.map_map,
    mul_assoc]
  simp only [map_zero]
  rfl

theorem lineDerivList_conj {V : Type} [AddCommGroup V] [Module ℂ V] [StarAddMonoid V]
    [StarModule ℂ V] (l : List V) (hl : ∀ v ∈ l, star v = v) (F : V → ℂ) :
    lineDerivList ℂ l (fun z => conj (F (star z))) =
      fun z => conj (lineDerivList ℂ l F (star z)) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    funext z
    rw [lineDerivList_cons, ih fun w hw => hl w (List.mem_cons_of_mem _ hw), lineDerivList_cons]
    simp only [lineDeriv, star_add, star_smul, hl v List.mem_cons_self]
    have h := congrFun (deriv_conj_conj (f := fun t : ℂ => lineDerivList ℂ l F (star z + t • v))) 0
    simpa [Function.comp_def] using h

theorem polyDeriv_barP_symm [StarAddMonoid W] [StarModule ℂ W] (P : MvPolynomial σ ℂ) (u : σ → W)
    (hu : ∀ s, star (u s) = u s) {F G : W → W → ℂ}
    (hF : ∀ p, AnalyticAt ℂ (fun p : W × W => F p.1 p.2) p)
    (hG : ∀ p, AnalyticAt ℂ (fun p : W × W => G p.1 p.2) p)
    (h : ∀ z w, G z w = conj (F (star w) (star z))) :
    polyDeriv P u (fun z => polyDeriv (barP P) u (G z) 0) 0 =
      conj (polyDeriv P u (fun z => polyDeriv (barP P) u (F z) 0) 0) := by
  have hs : (barP P).support = P.support :=
    MvPolynomial.support_map_of_injective _ (starRingEnd ℂ).injective
  have hc (m : σ →₀ ℕ) : (barP P).coeff m = conj (P.coeff m) := MvPolynomial.coeff_map _ _ _
  have e1 := polyDeriv_polyDeriv P (barP P) u hF
  have e2 := polyDeriv_polyDeriv P (barP P) u hG
  dsimp only at e1 e2
  rw [e1, e2, hs, Finset.sum_comm]
  simp only [map_sum, map_mul, hc, Complex.conj_conj]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  have h1 : (fun p : W × W => G p.1 p.2) =
      fun p => conj ((fun q : W × W => F q.2 q.1) (star p)) := funext fun p => h p.1 p.2
  have h2 (l : List (W × W)) := congrFun (lineDerivList_comp_linearMap
    (LinearEquiv.prodComm ℂ W W).toLinearMap l (fun p : W × W => F p.1 p.2)) 0
  simp only [LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
    Prod.swap_zero] at h2
  rw [h1, lineDerivList_conj _ (by
    simp only [List.mem_append, List.mem_map]
    rintro v (⟨s, -, rfl⟩ | ⟨s, -, rfl⟩) <;> simp [Prod.ext_iff, hu]) fun q : W × W => F q.2 q.1]
  simp only [star_zero]
  rw [h2, List.map_append, List.map_map, List.map_map,
    lineDerivList_perm (hF 0) List.perm_append_comm, mul_comm (P.coeff m')]
  rfl

theorem lineDerivList_exp (ℓ : W →L[ℂ] ℂ) (C : ℂ) (l : List W) :
    lineDerivList ℂ l (fun w => C * Complex.exp (ℓ w)) =
      fun w => (l.map ℓ).prod * (C * Complex.exp (ℓ w)) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    funext w
    rw [lineDerivList_cons, ih]
    have h := (((ℓ.hasFDerivAt (x := w)).cexp.const_mul C).const_mul
      (l.map ℓ).prod).hasLineDerivAt v
    simp only [h.lineDeriv, List.map_cons, List.prod_cons, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring

theorem polyDeriv_exp (Q : MvPolynomial σ ℂ) (u : σ → W) (ℓ : W →L[ℂ] ℂ) (C : ℂ) :
    polyDeriv Q u (fun w => C * Complex.exp (ℓ w)) 0 =
      C * MvPolynomial.eval (fun s => ℓ (u s)) Q := by
  have ha : AnalyticAt ℂ (fun w => C * Complex.exp (ℓ w)) 0 :=
    analyticAt_const.mul (ℓ.analyticAt 0).cexp
  rw [polyDeriv_eq_sum_list _ _ ha, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h : ((List.map u (lst m)).map ℓ).prod = ∏ i ∈ m.support, ℓ (u i) ^ m i := by
    rw [List.map_map, ← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList,
      Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index (by simp)
        (by simp [pow_add])]
    rfl
  rw [lineDerivList_exp, h]
  simp only [map_zero, Complex.exp_zero]
  ring

theorem coeff_aeval_smul_X [Fintype σ] (t : σ → ℂ) (Q : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m
      (MvPolynomial.aeval (fun s => t s • (MvPowerSeries.X s : MvPowerSeries σ ℂ)) Q) =
      (∏ s, t s ^ m s) * Q.coeff m := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial n c =>
    have h : n.prod (fun s k => (t s • (MvPowerSeries.X s : MvPowerSeries σ ℂ)) ^ k) =
        (∏ s, t s ^ n s) • MvPowerSeries.monomial n 1 := by
      rw [← MvPolynomial.coe_monomial, MvPolynomial.monomial_eq,
        ← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
      simp only [map_one, one_mul, smul_pow, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_prod, map_pow]
      rw [Finsupp.prod_fintype _ _ (by simp), Finset.prod_smul]
      simp
    rw [MvPolynomial.aeval_monomial, h, ← Algebra.smul_def, map_smul, map_smul,
      MvPowerSeries.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases e : m = n
    · subst e; simp [mul_comm]
    · simp [e, Ne.symm e]
  | add P Q hP hQ => simp only [map_add, hP, hQ, MvPolynomial.coeff_add, mul_add]

theorem polyDeriv_barP_exp [Fintype σ] [DecidableEq σ] (P : MvPolynomial σ ℂ) (u : σ → W)
    (π : σ → W →L[ℂ] ℂ) (hπ : ∀ s s', π s (u s') = if s = s' then 1 else 0) (t : σ → ℝ) (C : ℝ) :
    polyDeriv P u (fun z => polyDeriv (barP P) u
      (fun w => C * Complex.exp (∑ s, t s * π s z * π s w)) 0) 0 =
      ((C * ∑ m ∈ P.support, (∏ s, (m s).factorial : ℕ) * (∏ s, t s ^ m s) *
        Complex.normSq (P.coeff m) : ℝ) : ℂ) := by
  have h1 (z : W) : polyDeriv (barP P) u
      (fun w => C * Complex.exp (∑ s, t s * π s z * π s w)) 0 =
      C * MvPolynomial.eval (fun s => ((t s : ℂ) • π s) z) (barP P) := by
    have h := polyDeriv_exp (barP P) u (∑ s, (t s * π s z) • π s) C
    simpa [hπ] using h
  have h2 (s : σ) : taylorDir u ((t s : ℂ) • π s : W →L[ℂ] ℂ) = (t s : ℂ) • MvPowerSeries.X s := by
    rw [taylorDir_clm]
    simp [hπ]
  have ha (s : σ) : AnalyticAt ℂ ((t s : ℂ) • π s : W →L[ℂ] ℂ) 0 := ContinuousLinearMap.analyticAt _ _
  have h3 : taylorDir u (fun z => C * MvPolynomial.eval (fun s => ((t s : ℂ) • π s) z) (barP P)) =
      (C : ℂ) • MvPolynomial.aeval (fun s => (t s : ℂ) • (MvPowerSeries.X s : MvPowerSeries σ ℂ))
        (barP P) := by
    simp only [← h2]
    rw [← taylorDir_eval u ha, ← taylorDir_smul]
    · rfl
    · exact AnalyticAt.aeval_mvPolynomial ha _
  simp only [h1]
  rw [dirPolyDeriv_eq_sum_coeff_taylorDir, h3]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, coeff_aeval_smul_X, barP, MvPolynomial.coeff_map, ← Complex.mul_conj, smul_eq_mul]
  ring

theorem apolar_norm_pos [Fintype σ] {P : MvPolynomial σ ℂ} (hP : P ≠ 0) {t : σ → ℝ}
    (ht : ∀ s, 0 < t s) :
    0 < ∑ m ∈ P.support, ((∏ s, (m s).factorial : ℕ) : ℝ) * (∏ s, t s ^ m s) *
        Complex.normSq (P.coeff m) := by
  refine Finset.sum_pos (fun m hm => ?_) (MvPolynomial.support_nonempty.2 hP)
  refine mul_pos (mul_pos ?_ (Finset.prod_pos fun s _ => pow_pos (ht s) _))
    (Complex.normSq_pos.2 (MvPolynomial.mem_support_iff.1 hm))
  exact_mod_cast Finset.prod_pos fun s _ => Nat.factorial_pos _

end GlobalTheory.SW.KernSym
