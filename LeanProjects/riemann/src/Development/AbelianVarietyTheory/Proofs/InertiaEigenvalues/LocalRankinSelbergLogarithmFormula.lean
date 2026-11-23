import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxLocLConjBound
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLPoleAtOneConjStatement

noncomputable section

open Complex ComplexConjugate NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSLog

theorem summable_norm_log_terms (S : Multiset ℂ) (h : ∀ w ∈ S, ‖w‖ < 1) :
    Summable fun r : ℕ => ‖(S.map fun w => w ^ (r + 1)).sum / ((r + 1 : ℕ) : ℂ)‖ := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    have ha : ‖a‖ < 1 := h a (Multiset.mem_cons_self a S)
    have ih' := ih fun w hw => h w (Multiset.mem_cons_of_mem hw)
    have hg : Summable fun r : ℕ => ‖a‖ ^ (r + 1) :=
      (summable_geometric_of_lt_one (norm_nonneg _) ha).comp_injective (add_left_injective 1)
    refine (hg.add ih').of_nonneg_of_le (fun _ => norm_nonneg _) fun r => ?_
    simp only [Multiset.map_cons, Multiset.sum_cons, add_div]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    rw [norm_div, norm_pow]
    have h1 : (1 : ℝ) ≤ ‖((r + 1 : ℕ) : ℂ)‖ := by
      rw [Complex.norm_natCast]; exact_mod_cast Nat.succ_pos r
    exact div_le_self (pow_nonneg (norm_nonneg _) _) h1

theorem hasSum_log_succ (S : Multiset ℂ) (h : ∀ w ∈ S, ‖w‖ < 1) :
    HasSum (fun r : ℕ => (S.map fun w => w ^ (r + 1)).sum / ((r + 1 : ℕ) : ℂ)) (S.map fun w => -log (1 - w)).sum := by
  have := GlobalTheory.JSW.LogPos.hasSum_log S h
  rw [← hasSum_nat_add_iff' 1] at this
  simpa using this

theorem sum_pow_product_succ (z : ℂ) (r : ℕ) (A B : Multiset ℂˣ) :
    (((A ×ˢ B).map fun p : ℂˣ × ℂˣ => (p.1 : ℂ) * p.2 * z).map (fun w => w ^ r)).sum =
      (A.map fun a : ℂˣ => (a : ℂ) ^ r).sum * (B.map fun b : ℂˣ => (b : ℂ) ^ r).sum * z ^ r := by
  rw [Multiset.map_map]
  have := GlobalTheory.JSW.LogPos.sum_pow_product z r A B
  simp only [Function.comp_def]
  rw [this]; ring

theorem norm_natCast_cpow_neg (q : ℕ) (hq : 0 < q) (s : ℂ) : ‖(q : ℂ) ^ (-s)‖ = (q : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos hq, neg_re]

theorem norm_natCast_cpow_neg_le (q : ℕ) (s : ℂ) : ‖(q : ℂ) ^ (-s)‖ ≤ (q : ℝ) ^ (-s.re) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · by_cases hs : s = 0
    · simp [hs]
    · rw [Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.2 hs), norm_zero, Nat.cast_zero]
      exact Real.rpow_nonneg le_rfl _
  · exact (norm_natCast_cpow_neg q hq s).le

theorem cpow_neg_mul_nat (q : ℕ) (s : ℂ) (n : ℕ) : (q : ℂ) ^ (-((n : ℂ) * s)) = ((q : ℂ) ^ (-s)) ^ n := by
  rw [← Complex.cpow_nat_mul, neg_mul_eq_mul_neg]

theorem locL_eq_exp (q : ℕ) (A B : Multiset ℂˣ) (s : ℂ)
    (h : ∀ α ∈ A, ∀ β ∈ B, ‖(α : ℂ)‖ * ‖(β : ℂ)‖ * (q : ℝ) ^ (-s.re) < 1) :
    Summable (fun r : ℕ => ‖(A.map fun a : ℂˣ => (a : ℂ) ^ (r + 1)).sum *
        (B.map fun b : ℂˣ => (b : ℂ) ^ (r + 1)).sum * (q : ℂ) ^ (-(((r + 1 : ℕ) : ℂ) * s)) / ((r + 1 : ℕ) : ℂ)‖) ∧
      locL q A B s = exp (∑' r : ℕ, (A.map fun a : ℂˣ => (a : ℂ) ^ (r + 1)).sum *
        (B.map fun b : ℂˣ => (b : ℂ) ^ (r + 1)).sum * (q : ℂ) ^ (-(((r + 1 : ℕ) : ℂ) * s)) / ((r + 1 : ℕ) : ℂ)) := by
  set z : ℂ := (q : ℂ) ^ (-s) with hz
  set S := (A ×ˢ B).map fun p : ℂˣ × ℂˣ => (p.1 : ℂ) * p.2 * z with hS
  have hSn : ∀ w ∈ S, ‖w‖ < 1 := by
    intro w hw
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hw
    rw [Multiset.mem_product] at hp
    rw [norm_mul, norm_mul, hz]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_natCast_cpow_neg_le q s)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (h _ hp.1 _ hp.2)
  have hterm : ∀ r : ℕ, (A.map fun a : ℂˣ => (a : ℂ) ^ (r + 1)).sum *
        (B.map fun b : ℂˣ => (b : ℂ) ^ (r + 1)).sum * (q : ℂ) ^ (-(((r + 1 : ℕ) : ℂ) * s)) / ((r + 1 : ℕ) : ℂ) =
      (S.map fun w => w ^ (r + 1)).sum / ((r + 1 : ℕ) : ℂ) := by
    intro r
    rw [hS, sum_pow_product_succ, cpow_neg_mul_nat, ← hz]
  simp only [hterm]
  refine ⟨summable_norm_log_terms S hSn, ?_⟩
  have hloc : locL q A B s = (S.map fun w => (1 - w)⁻¹).prod := by
    simp only [locL, hS, Multiset.map_map, Function.comp_def, hz]
  rw [hloc, GlobalTheory.JSW.LogPos.prod_inv_one_sub_eq_exp S hSn, (hasSum_log_succ S hSn).tsum_eq]

end GlobalTheory.JSLog

namespace GlobalTheory.JSLog

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem hasSat_sat {a : ℕ} {π : CG E a} {T : Finset (HeightOneSpectrum (𝓞 E))} (h : UnrOutside T π)
    {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ T) : π.HasSat w (sat π w) := by
  have hex : ∃ B, π.HasSat w B := h w hw
  unfold sat
  rw [dif_pos hex]
  exact hex.choose_spec

theorem sat_zero (π : CG E 0) (w : HeightOneSpectrum (𝓞 E)) : sat π w = 0 := by
  unfold sat
  split_ifs with h
  · exact Multiset.card_eq_zero.1 h.choose_spec.card
  · rfl

theorem hasProd_eq_zero_of_eq_zero {ι : Type*} {f : ι → ℂ} {P : ℂ} (h : HasProd f P) {i : ι} (hi : f i = 0) :
    P = 0 := by
  classical
  have h0 : HasProd f 0 := by
    have : Filter.Tendsto (fun s : Finset ι => ∏ b ∈ s, f b) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨{i}, fun s hs =>
        (Finset.prod_eq_zero (hs (Finset.mem_singleton_self i)) hi).symm⟩)
    exact this
  exact h.unique h0

theorem sq_norm_le {a : ℕ} {π : CG E a} (hu : π.IsUnitary) {T : Finset (HeightOneSpectrum (𝓞 E))}
    (hT : UnrOutside T π) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ T) {α : ℂˣ} (hα : α ∈ sat π w) :
    ‖(α : ℂ)‖ ^ 2 ≤ (Ideal.absNorm w.asIdeal : ℝ) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [sat_zero] at hα; simp at hα
  by_contra hlt
  push Not at hlt
  have hq : (1 : ℝ) < Ideal.absNorm w.asIdeal := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  have hq0 : (0 : ℝ) < Ideal.absNorm w.asIdeal := by linarith
  set M := ‖(α : ℂ)‖ ^ 2 with hM
  have hM0 : 0 < M := by linarith
  set x := Real.logb (Ideal.absNorm w.asIdeal : ℝ) M with hxdef
  have hx : 1 < x := by
    rw [hxdef, Real.lt_logb_iff_rpow_lt hq hM0, Real.rpow_one]; exact hlt
  have hqx : (Ideal.absNorm w.asIdeal : ℝ) ^ x = M := Real.rpow_logb hq0 hq.ne' hM0
  obtain ⟨L, hL, -, -⟩ := GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a π ha hu T hT
  obtain ⟨hP, hL1⟩ := hL x hx
  have hzero : locL (Ideal.absNorm (⟨w, hw⟩ : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}).1.asIdeal)
      (sat π w) ((sat π w).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) = 0 := by
    unfold locL
    apply Multiset.prod_eq_zero
    refine Multiset.mem_map.2 ⟨(α, Units.map (starRingEnd ℂ).toMonoidHom α),
      Multiset.mem_product.2 ⟨hα, Multiset.mem_map_of_mem _ hα⟩, ?_⟩
    have e1 : (α : ℂ) * ((Units.map (starRingEnd ℂ).toMonoidHom α : ℂˣ) : ℂ) = (M : ℂ) := by
      rw [Units.coe_map]
      change (α : ℂ) * conj (α : ℂ) = _
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hM]
    have e2 : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-(x : ℂ)) = ((M⁻¹ : ℝ) : ℂ) := by
      rw [GlobalTheory.JSW.LogPos.cpow_neg_eq, Real.rpow_neg (Nat.cast_nonneg _), hqx]
    simp only
    rw [e1, e2, ← Complex.ofReal_mul, mul_inv_cancel₀ hM0.ne', Complex.ofReal_one, sub_self, inv_zero]
  have := hasProd_eq_zero_of_eq_zero hP hzero
  have h0 : L x = 0 := by exact_mod_cast this
  linarith

theorem pair_lt_one {u v q x : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hq : 1 < q) (hx : 1 < x) (huq : u ^ 2 ≤ q)
    (hvq : v ^ 2 ≤ q) : u * v * q ^ (-x) < 1 := by
  have hq0 : 0 < q := by linarith
  have huv : u * v ≤ q := by nlinarith [sq_nonneg (u - v)]
  have h1 : q ^ (-x) < q⁻¹ := by
    rw [← Real.rpow_neg_one]; exact Real.rpow_lt_rpow_of_exponent_lt hq (by linarith)
  have h2 : 0 < q ^ (-x) := Real.rpow_pos_of_pos hq0 _
  calc u * v * q ^ (-x) ≤ q * q ^ (-x) := mul_le_mul_of_nonneg_right huv h2.le
    _ < q * q⁻¹ := mul_lt_mul_of_pos_left h1 hq0
    _ = 1 := mul_inv_cancel₀ hq0.ne'

theorem map_conj_eq_map_star (B : Multiset ℂˣ) : B.map (Units.map (starRingEnd ℂ).toMonoidHom) = B.map star :=
  Multiset.map_congr rfl fun b _ => Units.ext (by rw [Units.coe_map, Units.coe_star]; rfl)

theorem sum_pow_map_conj (n : ℕ) (B : Multiset ℂˣ) :
    ((B.map (Units.map (starRingEnd ℂ).toMonoidHom)).map fun b : ℂˣ => (b : ℂ) ^ n).sum =
      conj (B.map fun b : ℂˣ => (b : ℂ) ^ n).sum := by
  rw [map_conj_eq_map_star, GlobalTheory.JSW.LogPos.sum_pow_star]

theorem summable_of_hasProd_exp {ι : Type*} [DecidableEq ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) {P : ℂ}
    (h : HasProd (fun i => ((Real.exp (f i) : ℝ) : ℂ)) P) : Summable f := by
  have h0 : Filter.Tendsto (fun s : Finset ι => ∏ i ∈ s, ((Real.exp (f i) : ℝ) : ℂ)) Filter.atTop (nhds P) := h
  have h1 : Filter.Tendsto (fun s : Finset ι => Real.exp (∑ i ∈ s, f i)) Filter.atTop (nhds P.re) := by
    refine ((Complex.continuous_re.tendsto P).comp h0).congr fun s => ?_
    simp only [Function.comp_apply, ← Complex.ofReal_prod, Complex.ofReal_re, Real.exp_sum]
  obtain ⟨s0, hs0⟩ := Filter.eventually_atTop.1 (h1.eventually (gt_mem_nhds (lt_add_one P.re)))
  refine summable_of_sum_le (c := P.re + 1) (fun i => hf i) fun s => ?_
  have hs := hs0 (s ∪ s0) Finset.subset_union_right
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s ∪ s0, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun i _ _ => hf i
    _ ≤ Real.exp (∑ i ∈ s ∪ s0, f i) := by linarith [Real.add_one_le_exp (∑ i ∈ s ∪ s0, f i)]
    _ ≤ P.re + 1 := hs.le

theorem summable_diag {a : ℕ} (σ : CG E a) (hσ : σ.IsUnitary)
    (T : Finset (HeightOneSpectrum (𝓞 E))) (hT : UnrOutside T σ) (x : ℝ) (hx : 1 < x) :
    Summable fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ =>
      ((Ideal.absNorm p.1.1.asIdeal : ℝ) ^ (-x)) ^ (p.2 + 1) *
        normSq ((sat σ p.1.1).map fun b : ℂˣ => (b : ℂ) ^ (p.2 + 1)).sum / ((p.2 + 1 : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [sat_zero, Multiset.map_zero, Multiset.sum_zero, map_zero, mul_zero, zero_div]
    exact summable_zero
  obtain ⟨L, hL, -, -⟩ := GlobalTheory.T.rankinSelberg_partialL_pole_at_one_conj E a σ ha hσ T hT
  obtain ⟨hP, -⟩ := hL x hx
  have hloc : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, ∃ Lw : ℝ,
      HasSum (fun n : ℕ => ((Ideal.absNorm w.1.asIdeal : ℝ) ^ (-x)) ^ n *
        normSq ((sat σ w.1).map fun b : ℂˣ => (b : ℂ) ^ n).sum / n) Lw ∧
      locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ w.1).map star) x = Real.exp Lw := by
    intro w
    have hq : (1 : ℝ) < Ideal.absNorm w.1.asIdeal := by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w.1
    refine GlobalTheory.JSW.LogPos.locL_conj_eq_exp _ _ _ (fun b hb => sq_norm_le hσ hT w.2 hb) x ?_
    have h1 : (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-x) < (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ := by
      rw [← Real.rpow_neg_one]; exact Real.rpow_lt_rpow_of_exponent_lt hq (by linarith)
    have hq0 : (0 : ℝ) < Ideal.absNorm w.1.asIdeal := by linarith
    calc (Ideal.absNorm w.1.asIdeal : ℝ) * (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-x)
        < (Ideal.absNorm w.1.asIdeal : ℝ) * (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ := mul_lt_mul_of_pos_left h1 hq0
      _ = 1 := mul_inv_cancel₀ hq0.ne'
  choose Lw hsum heq using hloc
  have hterm0 : ∀ (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (n : ℕ), 0 ≤ ((Ideal.absNorm w.1.asIdeal : ℝ) ^ (-x)) ^ n *
      normSq ((sat σ w.1).map fun b : ℂˣ => (b : ℂ) ^ n).sum / (n : ℝ) := fun w n =>
    div_nonneg (mul_nonneg (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) n) (normSq_nonneg _)) (Nat.cast_nonneg n)
  have hLw0 : ∀ w, 0 ≤ Lw w := fun w => (hsum w).nonneg (hterm0 w)
  have hP' : HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => ((Real.exp (Lw w) : ℝ) : ℂ)) (L x : ℂ) := by
    refine hP.congr_fun fun w => ?_
    rw [← heq w, map_conj_eq_map_star]
  classical
  have hLs : Summable Lw := summable_of_hasProd_exp Lw hLw0 hP'
  have hshift : ∀ w, HasSum (fun r : ℕ => ((Ideal.absNorm w.1.asIdeal : ℝ) ^ (-x)) ^ (r + 1) *
      normSq ((sat σ w.1).map fun b : ℂˣ => (b : ℂ) ^ (r + 1)).sum / ((r + 1 : ℕ) : ℝ)) (Lw w) := by
    intro w
    have := (hasSum_nat_add_iff' 1).2 (hsum w)
    simpa using this
  refine (summable_prod_of_nonneg fun p => hterm0 p.1 (p.2 + 1)).2
    ⟨fun w => (hshift w).summable, ?_⟩
  exact hLs.congr fun w => ((hshift w).tsum_eq).symm

end GlobalTheory.JSLog

namespace GlobalTheory.JSLog

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem hasProd_locL_conj {a b : ℕ} (σ : CG E a) (σ' : CG E b)
    (hσ : σ.IsUnitary) (hσ' : σ'.IsUnitary) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hT : UnrOutside T σ) (hT' : UnrOutside T σ') (x : ℝ) (hx : 1 < x) :
    Summable (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ =>
      ‖((sat σ p.1.1).map fun α : ℂˣ => (α : ℂ) ^ (p.2 + 1)).sum *
        conj ((sat σ' p.1.1).map fun β : ℂˣ => (β : ℂ) ^ (p.2 + 1)).sum *
        ((Ideal.absNorm p.1.1.asIdeal : ℕ) : ℂ) ^ (-(((p.2 + 1 : ℕ) : ℂ) * (x : ℂ))) / ((p.2 + 1 : ℕ) : ℂ)‖) ∧
    HasSum (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => ∑' r : ℕ,
      ((sat σ w.1).map fun α : ℂˣ => (α : ℂ) ^ (r + 1)).sum *
        conj ((sat σ' w.1).map fun β : ℂˣ => (β : ℂ) ^ (r + 1)).sum *
        ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-(((r + 1 : ℕ) : ℂ) * (x : ℂ))) / ((r + 1 : ℕ) : ℂ))
      (∑' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, ∑' r : ℕ,
      ((sat σ w.1).map fun α : ℂˣ => (α : ℂ) ^ (r + 1)).sum *
        conj ((sat σ' w.1).map fun β : ℂˣ => (β : ℂ) ^ (r + 1)).sum *
        ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-(((r + 1 : ℕ) : ℂ) * (x : ℂ))) / ((r + 1 : ℕ) : ℂ)) ∧
    HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1)
        ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ))
      (exp (∑' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, ∑' r : ℕ,
      ((sat σ w.1).map fun α : ℂˣ => (α : ℂ) ^ (r + 1)).sum *
        conj ((sat σ' w.1).map fun β : ℂˣ => (β : ℂ) ^ (r + 1)).sum *
        ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-(((r + 1 : ℕ) : ℂ) * (x : ℂ))) / ((r + 1 : ℕ) : ℂ))) := by
  set F : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ → ℂ := fun p =>
      ((sat σ p.1.1).map fun α : ℂˣ => (α : ℂ) ^ (p.2 + 1)).sum *
        conj ((sat σ' p.1.1).map fun β : ℂˣ => (β : ℂ) ^ (p.2 + 1)).sum *
        ((Ideal.absNorm p.1.1.asIdeal : ℕ) : ℂ) ^ (-(((p.2 + 1 : ℕ) : ℂ) * (x : ℂ))) / ((p.2 + 1 : ℕ) : ℂ) with hF
  have hD := summable_diag σ hσ T hT x hx
  have hD' := summable_diag σ' hσ' T hT' x hx
  have hbound : ∀ p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ, ‖F p‖ ≤
      (((Ideal.absNorm p.1.1.asIdeal : ℝ) ^ (-x)) ^ (p.2 + 1) *
        normSq ((sat σ p.1.1).map fun b : ℂˣ => (b : ℂ) ^ (p.2 + 1)).sum / ((p.2 + 1 : ℕ) : ℝ) +
      ((Ideal.absNorm p.1.1.asIdeal : ℝ) ^ (-x)) ^ (p.2 + 1) *
        normSq ((sat σ' p.1.1).map fun b : ℂˣ => (b : ℂ) ^ (p.2 + 1)).sum / ((p.2 + 1 : ℕ) : ℝ)) / 2 := by
    rintro ⟨w, r⟩
    have hq : 0 < Ideal.absNorm w.1.asIdeal := (NumberField.HeightOneSpectrum.one_lt_absNorm w.1).trans' Nat.one_pos
    set u := ‖((sat σ w.1).map fun b : ℂˣ => (b : ℂ) ^ (r + 1)).sum‖
    set v := ‖((sat σ' w.1).map fun b : ℂˣ => (b : ℂ) ^ (r + 1)).sum‖
    set t := ((Ideal.absNorm w.1.asIdeal : ℝ) ^ (-x)) ^ (r + 1) with ht
    have ht0 : 0 ≤ t := pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _
    have hn : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos r
    have hFn : ‖F (w, r)‖ = u * v * t / ((r + 1 : ℕ) : ℝ) := by
      simp only [hF, norm_div, norm_mul, Complex.norm_conj, Complex.norm_natCast]
      rw [cpow_neg_mul_nat, norm_pow, norm_natCast_cpow_neg _ hq, Complex.ofReal_re]
    rw [hFn, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    have key : u * v * t ≤ t * (u ^ 2 + v ^ 2) / 2 := by nlinarith [mul_nonneg ht0 (sq_nonneg (u - v))]
    calc u * v * t / ((r + 1 : ℕ) : ℝ) ≤ (t * (u ^ 2 + v ^ 2) / 2) / ((r + 1 : ℕ) : ℝ) := by gcongr
      _ = _ := by ring
  have hFn : Summable fun p => ‖F p‖ :=
    ((hD.add hD').div_const 2).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have hFs : Summable F := hFn.of_norm
  have hfib : ∀ w, HasSum (fun r => F (w, r)) (∑' r, F (w, r)) := fun w => (hFs.prod_factor w).hasSum
  have hHS : HasSum (fun w => ∑' r, F (w, r)) (∑' p, F p) := hFs.hasSum.prod_fiberwise hfib
  have hEq : ∑' w, ∑' r, F (w, r) = ∑' p, F p := hHS.tsum_eq
  have hHS' : HasSum (fun w => ∑' r, F (w, r)) (∑' w, ∑' r, F (w, r)) := hEq ▸ hHS
  refine ⟨hFn, hHS', ?_⟩
  convert hHS'.cexp using 1
  funext w
  have hq : 0 < Ideal.absNorm w.1.asIdeal := (NumberField.HeightOneSpectrum.one_lt_absNorm w.1).trans' Nat.one_pos
  have hqr : (1 : ℝ) < Ideal.absNorm w.1.asIdeal := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w.1
  have hcond : ∀ α ∈ sat σ w.1, ∀ β ∈ (sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom),
      ‖(α : ℂ)‖ * ‖(β : ℂ)‖ * (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-(x : ℂ).re) < 1 := by
    intro α hα β hβ
    obtain ⟨β0, hβ0, rfl⟩ := Multiset.mem_map.1 hβ
    have hnb : ‖((Units.map (starRingEnd ℂ).toMonoidHom β0 : ℂˣ) : ℂ)‖ = ‖(β0 : ℂ)‖ := by
      rw [Units.coe_map]; exact Complex.norm_conj _
    rw [hnb, Complex.ofReal_re]
    exact pair_lt_one (norm_nonneg _) (norm_nonneg _) hqr hx (sq_norm_le hσ hT w.2 hα)
      (sq_norm_le hσ' hT' w.2 hβ0)
  rw [(locL_eq_exp _ _ _ _ hcond).2]
  simp only [Function.comp_apply, hF, sum_pow_map_conj]

theorem psum_coeM (A : Multiset ℂˣ) (n : ℕ) :
    (A.map fun α => (α : ℂ) ^ n).sum = (A.map fun α : ℂˣ => (α : ℂ) ^ n).sum := by
  simp [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]

theorem psum_conj_coeM (A : Multiset ℂˣ) (n : ℕ) :
    (A.map fun β => (starRingEnd ℂ (β : ℂ)) ^ n).sum = conj (A.map fun α : ℂˣ => (α : ℂ) ^ n).sum := by
  simp [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def,
    map_multiset_sum]

theorem logRankinSelberg : (∀ (q : ℕ) (A B : Multiset ℂˣ) (s : ℂ), 1 < q → (∀ α ∈ A, ∀ β ∈ B, ‖(α : ℂ) * (β : ℂ)‖ * (q : ℝ) ^ (-s.re) < 1) → ∃ L : ℂ, HasSum (fun r : ℕ => (A.map fun α => (α : ℂ) ^ (r + 1)).sum * (B.map fun β => (β : ℂ) ^ (r + 1)).sum * (q : ℂ) ^ (-(((r : ℂ) + 1) * s)) / ((r : ℂ) + 1)) L ∧ locL q A B s = Complex.exp L) ∧ (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∀ x : ℝ, 1 < x → Summable (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ => ‖((sat σ p.1.1).map fun α => (α : ℂ) ^ (p.2 + 1)).sum * ((sat σ' p.1.1).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (p.2 + 1)).sum * (Ideal.absNorm p.1.1.asIdeal : ℂ) ^ (-(((p.2 : ℂ) + 1) * (x : ℂ))) / ((p.2 : ℂ) + 1)‖) ∧ HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (Complex.exp (∑' p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ, ((sat σ p.1.1).map fun α => (α : ℂ) ^ (p.2 + 1)).sum * ((sat σ' p.1.1).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (p.2 + 1)).sum * (Ideal.absNorm p.1.1.asIdeal : ℂ) ^ (-(((p.2 : ℂ) + 1) * (x : ℂ))) / ((p.2 : ℂ) + 1)))) := by
  refine ⟨fun q A B s _ h => ?_, fun E _ _ _ a b σ σ' hσ hσ' T hT hT' x hx => ?_⟩
  all_goals simp only [psum_coeM, psum_conj_coeM]
  · have h' : ∀ α ∈ A, ∀ β ∈ B, ‖(α : ℂ)‖ * ‖(β : ℂ)‖ * (q : ℝ) ^ (-s.re) < 1 := fun α hα β hβ => by
      simpa only [norm_mul] using h α hα β hβ
    obtain ⟨hs, he⟩ := locL_eq_exp q A B s h'
    simp only [Nat.cast_add, Nat.cast_one] at hs he
    exact ⟨_, hs.of_norm.hasSum, he⟩
  · obtain ⟨h1, -, h3⟩ := hasProd_locL_conj σ σ' hσ hσ' T hT hT' x hx
    simp only [Nat.cast_add, Nat.cast_one] at h1 h3
    refine ⟨h1, ?_⟩
    have hF := h1.of_norm
    rw [(hF.hasSum.prod_fiberwise fun w => (hF.prod_factor w).hasSum).tsum_eq.symm]
    exact h3

end GlobalTheory.JSLog
