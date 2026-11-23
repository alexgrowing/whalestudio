import Formalism.MahlerMeasure.LieRoots

namespace Formalism.GM

open Finset Polynomial

namespace GaussNormRoots

section
variable {K : Type} [NormedField K]

theorem gaussR_eq_sup_of_subset (ρ : NNReal) (P : K[X]) (s : Finset ℕ) (hs : P.support ⊆ s) :
    gaussR ρ P = s.sup (fun k => ‖P.coeff k‖₊ * ρ ^ k) := by
  unfold gaussR
  apply le_antisymm (Finset.sup_mono hs)
  refine Finset.sup_le fun k _ => ?_
  by_cases hk : k ∈ P.support
  · exact Finset.le_sup (f := fun k => ‖P.coeff k‖₊ * ρ ^ k) hk
  · rw [Polynomial.notMem_support_iff.mp hk]
    simp

theorem gaussR_C (ρ : NNReal) (a : K) : gaussR ρ (Polynomial.C a) = ‖a‖₊ := by
  rw [gaussR_eq_sup_of_subset ρ _ {0} (Polynomial.support_C_subset a)]
  simp

theorem gaussR_lin (ρ : NNReal) (q a : K) :
    gaussR ρ (Polynomial.C q * X + Polynomial.C a) = max ‖a‖₊ (‖q‖₊ * ρ) := by
  have hs : (Polynomial.C q * X + Polynomial.C a).support ⊆ {0, 1} := by
    intro k hk
    rw [Polynomial.mem_support_iff] at hk
    rcases k with _ | _ | k <;> simp_all [Polynomial.coeff_C, Polynomial.coeff_X]
  rw [gaussR_eq_sup_of_subset ρ _ _ hs]
  simp [Polynomial.coeff_C, Polynomial.coeff_X, max_comm]

theorem gaussR_multiset_prod (hG : GaussMulRad) [IsUltrametricDist K] (ρ : NNReal) (hρ : 0 < ρ)
    (m : Multiset K) (f : K → K[X]) :
    gaussR ρ (m.map f).prod = (m.map (fun ζ => gaussR ρ (f ζ))).prod := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    rw [← Polynomial.C_1, gaussR_C]
    simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [hG K ρ _ _ hρ, ih]

end

theorem multiset_sum_le_sum {α : Type} (m : Multiset α) (f g : α → ℝ) (hfg : ∀ x, f x ≤ g x) :
    (m.map f).sum ≤ (m.map g).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact add_le_add (hfg a) ih

theorem multiset_sum_neg {α : Type} (m : Multiset α) (f : α → ℝ) :
    (m.map fun x => -f x).sum = -(m.map f).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, neg_add]

theorem multiset_sum_add {α : Type} (m : Multiset α) (f g : α → ℝ) :
    (m.map fun x => f x + g x).sum = (m.map f).sum + (m.map g).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih]
    ring

theorem multiset_sum_mul_left {α : Type} (m : Multiset α) (c : ℝ) (f : α → ℝ) :
    (m.map fun x => c * f x).sum = c * (m.map f).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, mul_add]

theorem multiset_card_filter_eq_sum {α : Type} (m : Multiset α) (P : α → Prop) [DecidablePred P] :
    ((m.filter P).card : ℝ) = (m.map fun x => if P x then (1 : ℝ) else 0).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    by_cases h : P a
    · rw [Multiset.filter_cons_of_pos _ h]
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons, h, if_true]
      push_cast
      rw [ih]
      ring
    · rw [Multiset.filter_cons_of_neg _ h]
      simp only [Multiset.map_cons, Multiset.sum_cons, h, if_false]
      rw [ih]
      ring

theorem multiset_prod_pos {α : Type} (m : Multiset α) (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    0 < (m.map f).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact mul_pos (hf a) ih

theorem logb_multiset_prod {α : Type} (b : ℝ) (m : Multiset α) (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    Real.logb b (m.map f).prod = (m.map fun x => Real.logb b (f x)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [Real.logb_mul (hf a).ne' (multiset_prod_pos m f hf).ne', ih]

theorem vmin_step (p : ℕ) (hp1 : (1 : ℝ) < p) (h : ℕ) (E : ℝ) (hE : 0 ≤ E) (u : ℝ) (_hu : 0 ≤ u)
    [Decidable (u ≤ (p : ℝ) ^ (-(h : ℤ)))] :
    -Real.logb p (max u ((p : ℝ) ^ (-((h : ℝ) + E)))) ≤
      -Real.logb p (max u ((p : ℝ) ^ (-(h : ℤ)))) + E * (if u ≤ (p : ℝ) ^ (-(h : ℤ)) then 1 else 0) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hB : (0 : ℝ) < (p : ℝ) ^ (-((h : ℝ) + E)) := Real.rpow_pos_of_pos hp0 _
  have hAeq : (p : ℝ) ^ (-(h : ℤ)) = (p : ℝ) ^ (-(h : ℝ)) := by
    rw [← Real.rpow_intCast]
    norm_num
  have hBA : (p : ℝ) ^ (-((h : ℝ) + E)) ≤ (p : ℝ) ^ (-(h : ℤ)) := by
    rw [hAeq]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  split_ifs with hu
  · rw [max_eq_right hu, mul_one]
    have h1 : Real.logb p ((p : ℝ) ^ (-((h : ℝ) + E))) ≤
        Real.logb p (max u ((p : ℝ) ^ (-((h : ℝ) + E)))) :=
      Real.logb_le_logb_of_le hp1 hB (le_max_right _ _)
    have h2 : Real.logb p ((p : ℝ) ^ (-((h : ℝ) + E))) = -((h : ℝ) + E) :=
      Real.logb_rpow hp0 hp1.ne'
    have h3 : Real.logb p ((p : ℝ) ^ (-(h : ℤ))) = -(h : ℝ) := by
      rw [hAeq]
      exact Real.logb_rpow hp0 hp1.ne'
    linarith
  · push_neg at hu
    rw [max_eq_left (le_trans hBA hu.le), max_eq_left hu.le]
    simp

end GaussNormRoots

open GaussNormRoots in
theorem lieRoots_of (hG : GaussMulRad) : LieRoots := by
  unfold LieRoots
  intro p _ K _ _ _ h β E D lead roots t₀ hE hlead hD hbound
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hρ : 0 < ((p : ℝ) ^ (-E)).toNNReal := Real.toNNReal_pos.mpr (Real.rpow_pos_of_pos hp0 _)
  have hnp : ‖(p : K)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] K) p, norm_algebraMap', Padic.norm_p]
  have hnph : ‖(p : K) ^ h‖ = (p : ℝ) ^ (-(h : ℤ)) := by
    rw [norm_pow, hnp, inv_pow, zpow_neg, zpow_natCast]
  have hcomp : D.comp (C ((p : K) ^ h) * X + C (t₀ : K)) =
      C lead * (roots.map fun ζ => C ((p : K) ^ h) * X + C ((t₀ : K) - ζ)).prod := by
    rw [hD, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.multiset_prod_comp, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun ζ _ => ?_
    simp only [Function.comp_apply, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, map_sub]
    ring
  have hpt : ∀ ζ : K, ((max ‖(t₀ : K) - ζ‖₊ (‖(p : K) ^ h‖₊ * ((p : ℝ) ^ (-E)).toNNReal) : NNReal) : ℝ) =
      max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E))) := by
    intro ζ
    rw [NNReal.coe_max, NNReal.coe_mul, coe_nnnorm, coe_nnnorm, hnph,
      Real.coe_toNNReal _ (Real.rpow_pos_of_pos hp0 _).le]
    congr 1
    rw [← Real.rpow_intCast, ← Real.rpow_add hp0]
    congr 1
    push_cast
    ring
  have hreal : ((gaussR ((p : ℝ) ^ (-E)).toNNReal (D.comp (C ((p : K) ^ h) * X + C (t₀ : K))) : NNReal) : ℝ) =
      ‖lead‖ * (roots.map fun ζ => max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E)))).prod := by
    rw [hcomp, hG K _ _ _ hρ, gaussR_C, gaussR_multiset_prod hG _ hρ]
    simp only [gaussR_lin]
    rw [NNReal.coe_mul, coe_nnnorm, NNReal.coe_multiset_prod, Multiset.map_map]
    congr 1
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun ζ _ => hpt ζ)
  rw [hreal] at hbound
  have hFpos : ∀ ζ : K, 0 < max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E))) :=
    fun ζ => lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 _) (le_max_right _ _)
  have hlpos : 0 < ‖lead‖ := norm_pos_iff.mpr hlead
  have hPpos := multiset_prod_pos roots _ hFpos
  have hlog : Real.logb p (‖lead‖ * (roots.map fun ζ => max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E)))).prod)
      ≤ -(E * β) := by
    calc _ ≤ Real.logb p ((p : ℝ) ^ (-(E * β))) :=
          Real.logb_le_logb_of_le hp1 (mul_pos hlpos hPpos) hbound
      _ = -(E * β) := Real.logb_rpow hp0 hp1.ne'
  rw [Real.logb_mul hlpos.ne' hPpos.ne', logb_multiset_prod _ _ _ hFpos] at hlog
  have hstep := multiset_sum_le_sum roots
    (fun ζ => -Real.logb p (max ‖(t₀ : K) - ζ‖ ((p : ℝ) ^ (-((h : ℝ) + E)))))
    (fun ζ => vmin p h ((t₀ : K) - ζ) +
      E * (if ‖(t₀ : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)) then 1 else 0)) (fun ζ => by
        have := vmin_step p hp1 h E hE ‖(t₀ : K) - ζ‖ (norm_nonneg _)
        unfold vmin
        simpa only using this)
  rw [multiset_sum_add, multiset_sum_mul_left, multiset_sum_neg] at hstep
  rw [multiset_card_filter_eq_sum]
  linarith

end Formalism.GM
