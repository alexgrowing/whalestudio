import Mathlib

open Filter Topology

namespace GlobalTheory.JetConj

def JetRel (S : Subring (ℂ × ℂ)) (f g : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧ ∀ n, (iteratedDeriv n f 0, iteratedDeriv n g 0) ∈ S

def IsFieldGraph (S : Subring (ℂ × ℂ)) : Prop :=
  (∀ a b, (a, b) ∈ S → (a = 0 ↔ b = 0)) ∧ ∀ a b, (a, b) ∈ S → (a⁻¹, b⁻¹) ∈ S

noncomputable def graph (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : Subring (ℂ × ℂ) :=
  (RingHom.prod (M.val : M →+* ℂ) (ρ : M →+* ℂ)).range

lemma mem_graph {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ} {a b : ℂ} :
    (a, b) ∈ graph M ρ ↔ ∃ h : a ∈ M, ρ ⟨a, h⟩ = b := by
  simp only [graph, RingHom.mem_range, RingHom.prod_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨x, hx, hy⟩
    subst hx
    exact ⟨x.2, hy⟩
  · rintro ⟨h, hb⟩
    exact ⟨⟨a, h⟩, rfl, hb⟩

lemma isFieldGraph_graph (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : IsFieldGraph (graph M ρ) := by
  refine ⟨fun a b hab => ?_, fun a b hab => ?_⟩
  · obtain ⟨h, rfl⟩ := mem_graph.1 hab
    rw [map_eq_zero]
    exact ⟨fun ha => Subtype.ext ha, fun h0 => congrArg Subtype.val h0⟩
  · obtain ⟨h, rfl⟩ := mem_graph.1 hab
    refine mem_graph.2 ⟨inv_mem h, ?_⟩
    rw [← map_inv₀]
    rfl

variable {S : Subring (ℂ × ℂ)} {f f' g g' h h' : ℂ → ℂ}

lemma pair_natCast (S : Subring (ℂ × ℂ)) (n : ℕ) : ((n : ℂ), (n : ℂ)) ∈ S := by
  convert natCast_mem S n using 1
  ext <;> simp

lemma pair_mul {a b c d : ℂ} (h1 : (a, b) ∈ S) (h2 : (c, d) ∈ S) : (a * c, b * d) ∈ S := S.mul_mem h1 h2

lemma pair_add {a b c d : ℂ} (h1 : (a, b) ∈ S) (h2 : (c, d) ∈ S) : (a + c, b + d) ∈ S := S.add_mem h1 h2

lemma pair_sub {a b c d : ℂ} (h1 : (a, b) ∈ S) (h2 : (c, d) ∈ S) : (a - c, b - d) ∈ S := S.sub_mem h1 h2

lemma pair_sum {ι : Type*} (s : Finset ι) {a b : ι → ℂ} (h : ∀ i ∈ s, (a i, b i) ∈ S) :
    (∑ i ∈ s, a i, ∑ i ∈ s, b i) ∈ S := by
  have hs : (∑ i ∈ s, ((a i, b i) : ℂ × ℂ)) ∈ S := sum_mem h
  convert hs using 1
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

lemma JetRel.congr (H : JetRel S f f') (h1 : f =ᶠ[𝓝 0] g) (h2 : f' =ᶠ[𝓝 0] g') : JetRel S g g' := by
  obtain ⟨hf, hf', hd⟩ := H
  refine ⟨hf.congr h1, hf'.congr h2, fun n => ?_⟩
  rw [← h1.iteratedDeriv_eq n, ← h2.iteratedDeriv_eq n]
  exact hd n

lemma JetRel.zero (H : JetRel S f f') : (f 0, f' 0) ∈ S := by simpa using H.2.2 0

lemma JetRel.const {a b : ℂ} (h : (a, b) ∈ S) : JetRel S (fun _ => a) (fun _ => b) := by
  refine ⟨analyticAt_const, analyticAt_const, fun n => ?_⟩
  rw [iteratedDeriv_const, iteratedDeriv_const]
  split_ifs
  · exact h
  · exact S.zero_mem

lemma JetRel.sub (H : JetRel S f f') (K : JetRel S g g') :
    JetRel S (fun z => f z - g z) (fun z => f' z - g' z) := by
  obtain ⟨hf, hf', hdf⟩ := H
  obtain ⟨hg, hg', hdg⟩ := K
  refine ⟨by fun_prop, by fun_prop, fun n => ?_⟩
  rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, iteratedDeriv_fun_sub hf'.contDiffAt hg'.contDiffAt]
  exact pair_sub (hdf n) (hdg n)

private lemma iteratedDeriv_mul_mem_of_iteratedDeriv_mem (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0) (hg : AnalyticAt ℂ g 0)
    (hg' : AnalyticAt ℂ g' 0) (n : ℕ) (H : ∀ i ≤ n, (iteratedDeriv i f 0, iteratedDeriv i f' 0) ∈ S)
    (K : ∀ i ≤ n, (iteratedDeriv i g 0, iteratedDeriv i g' 0) ∈ S) :
    (iteratedDeriv n (fun z => f z * g z) 0, iteratedDeriv n (fun z => f' z * g' z) 0) ∈ S := by
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, iteratedDeriv_fun_mul hf'.contDiffAt hg'.contDiffAt]
  exact pair_sum _ fun i hi => pair_mul (pair_mul (pair_natCast S _)
    (H i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))) (K (n - i) (Nat.sub_le n i))

lemma JetRel.mul (H : JetRel S f f') (K : JetRel S g g') :
    JetRel S (fun z => f z * g z) (fun z => f' z * g' z) := by
  obtain ⟨hf, hf', hdf⟩ := H
  obtain ⟨hg, hg', hdg⟩ := K
  exact ⟨by fun_prop, by fun_prop, fun n => iteratedDeriv_mul_mem_of_iteratedDeriv_mem hf hf' hg hg' n (fun i _ => hdf i) (fun i _ => hdg i)⟩

lemma JetRel.pow (H : JetRel S f f') (k : ℕ) : JetRel S (fun z => f z ^ k) (fun z => f' z ^ k) := by
  induction k with
  | zero => simpa using JetRel.const (S := S) (a := 1) (b := 1) S.one_mem
  | succ k ih => simpa [pow_succ] using ih.mul H

lemma JetRel.deriv (H : JetRel S f f') : JetRel S (deriv f) (deriv f') := by
  obtain ⟨hf, hf', hd⟩ := H
  refine ⟨hf.deriv, hf'.deriv, fun n => ?_⟩
  rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
  exact hd (n + 1)

lemma JetRel.comp_mul (hf : Differentiable ℂ f) (hf' : Differentiable ℂ f') {c : ℂ} (hc : (c, c) ∈ S)
    (H : JetRel S f f') : JetRel S (fun z => f (c * z)) (fun z => f' (c * z)) := by
  obtain ⟨-, -, hd⟩ := H
  have d1 : Differentiable ℂ (fun z => f (c * z)) := by fun_prop
  have d2 : Differentiable ℂ (fun z => f' (c * z)) := by fun_prop
  refine ⟨d1.analyticAt 0, d2.analyticAt 0, fun n => ?_⟩
  simp only [iteratedDeriv_comp_const_mul hf.contDiff c, iteratedDeriv_comp_const_mul hf'.contDiff c, mul_zero]
  exact pair_mul (by simpa using S.pow_mem hc n) (hd n)

lemma JetRel.of_comp_mul (hS : IsFieldGraph S) (hf : Differentiable ℂ f) (hf' : Differentiable ℂ f')
    {c : ℂ} (hc0 : c ≠ 0) (hc : (c, c) ∈ S)
    (H : JetRel S (fun z => f (c * z)) (fun z => f' (c * z))) : JetRel S f f' := by
  have hc' : (c⁻¹, c⁻¹) ∈ S := hS.2 c c hc
  have d1 : Differentiable ℂ (fun z => f (c * z)) := by fun_prop
  have d2 : Differentiable ℂ (fun z => f' (c * z)) := by fun_prop
  simpa [mul_inv_cancel_left₀ hc0] using JetRel.comp_mul d1 d2 hc' H

lemma exists_iteratedDeriv_ne_zero (hg : AnalyticAt ℂ g 0) (h0 : ¬ g =ᶠ[𝓝 0] 0) :
    ∃ k, iteratedDeriv k g 0 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hg.eventually_analyticAt
  have hd : DifferentiableOn ℂ g (Metric.ball 0 ε) := fun y hy =>
    (hball y hy).differentiableAt.differentiableWithinAt
  filter_upwards [Metric.ball_mem_nhds 0 hε] with z hz
  have hs := Complex.hasSum_taylorSeries_on_ball hd hz
  simp only [hcon, smul_zero] at hs
  exact (hasSum_zero.unique hs).symm

private lemma eq_div_of_binomial_convolution (a b c : ℕ → ℂ) (m n : ℕ) (hb : ∀ j < m, b j = 0) (hbm : b m ≠ 0)
    (hc : c (n + m) = ∑ j ∈ Finset.range (n + m + 1), ((n + m).choose j : ℂ) * a j * b (n + m - j)) :
    a n = (c (n + m) - ∑ j ∈ Finset.range n, ((n + m).choose j : ℂ) * a j * b (n + m - j)) *
      (((n + m).choose n : ℂ) * b m)⁻¹ := by
  have hC : ((n + m).choose n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.le_add_right n m)).ne'
  have htail : ∑ j ∈ Finset.Ico (n + 1) (n + m + 1), ((n + m).choose j : ℂ) * a j * b (n + m - j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    rw [hb (n + m - j) (by omega), mul_zero]
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : n + 1 ≤ n + m + 1), htail, add_zero,
    Finset.sum_range_succ, Nat.add_sub_cancel_left] at hc
  rw [hc, add_sub_cancel_left]
  field_simp

lemma JetRel.of_mul (hS : IsFieldGraph S) (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0)
    (G : JetRel S g g') (h0 : ¬ g =ᶠ[𝓝 0] 0)
    (H : JetRel S (fun z => f z * g z) (fun z => f' z * g' z)) : JetRel S f f' := by
  obtain ⟨hg, hg', hdg⟩ := G
  obtain ⟨-, -, hdH⟩ := H
  classical
  have hex : ∃ k, iteratedDeriv k g 0 ≠ 0 := exists_iteratedDeriv_ne_zero hg h0
  set m := Nat.find hex with hmdef
  have hm : iteratedDeriv m g 0 ≠ 0 := Nat.find_spec hex
  have hlt : ∀ j < m, iteratedDeriv j g 0 = 0 := fun j hj => not_not.1 (Nat.find_min hex hj)
  have hm' : iteratedDeriv m g' 0 ≠ 0 := fun h => hm ((hS.1 _ _ (hdg m)).2 h)
  have hlt' : ∀ j < m, iteratedDeriv j g' 0 = 0 := fun j hj => (hS.1 _ _ (hdg j)).1 (hlt j hj)
  refine ⟨hf, hf', fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc : iteratedDeriv (n + m) (fun z => f z * g z) 0 = _ := iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt
    have hc' : iteratedDeriv (n + m) (fun z => f' z * g' z) 0 = _ :=
      iteratedDeriv_fun_mul hf'.contDiffAt hg'.contDiffAt
    have e1 := eq_div_of_binomial_convolution (fun j => iteratedDeriv j f 0) (fun j => iteratedDeriv j g 0)
      (fun j => iteratedDeriv j (fun z => f z * g z) 0) m n hlt hm hc
    have e2 := eq_div_of_binomial_convolution (fun j => iteratedDeriv j f' 0) (fun j => iteratedDeriv j g' 0)
      (fun j => iteratedDeriv j (fun z => f' z * g' z) 0) m n hlt' hm' hc'
    beta_reduce at e1 e2
    rw [e1, e2]
    refine pair_mul (pair_sub (hdH (n + m)) (pair_sum _ fun j hj =>
      pair_mul (pair_mul (pair_natCast S _) (ih j (Finset.mem_range.1 hj))) (hdg _)))
      (hS.2 _ _ (pair_mul (pair_natCast S _) (hdg m)))

lemma JetRel.of_deriv_eq (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0) (G : JetRel S g g')
    (e : _root_.deriv f =ᶠ[𝓝 0] fun z => f z * g z) (e' : _root_.deriv f' =ᶠ[𝓝 0] fun z => f' z * g' z)
    (h0 : (f 0, f' 0) ∈ S) : JetRel S f f' := by
  obtain ⟨hg, hg', hdg⟩ := G
  refine ⟨hf, hf', fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simpa using h0
    | succ n =>
      rw [iteratedDeriv_succ', iteratedDeriv_succ', e.iteratedDeriv_eq n, e'.iteratedDeriv_eq n]
      exact iteratedDeriv_mul_mem_of_iteratedDeriv_mem hf hf' hg hg' n (fun i hi => ih i (Nat.lt_succ_of_le hi)) (fun i _ => hdg i)

private lemma deriv_eventuallyEq_logDeriv_pow_succ {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hne : f 0 ≠ 0) (j : ℕ) :
    AnalyticAt ℂ (fun z => _root_.deriv (fun w => f w ^ (j + 1)) z / (((j + 1 : ℕ) : ℂ) * f z ^ (j + 1))) 0 ∧
    (_root_.deriv (fun w => f w ^ (j + 1)) =ᶠ[𝓝 0] fun z =>
      _root_.deriv (fun w => f w ^ (j + 1)) z / (((j + 1 : ℕ) : ℂ) * f z ^ (j + 1)) *
        (((j + 1 : ℕ) : ℂ) * f z ^ (j + 1))) ∧
    (_root_.deriv f =ᶠ[𝓝 0] fun z =>
      f z * (_root_.deriv (fun w => f w ^ (j + 1)) z / (((j + 1 : ℕ) : ℂ) * f z ^ (j + 1)))) := by
  have hk : ((j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero j)
  have hu : AnalyticAt ℂ (fun w => f w ^ (j + 1)) 0 := by fun_prop
  have hne' : ∀ᶠ z in 𝓝 (0 : ℂ), f z ≠ 0 := hf.continuousAt.eventually_ne hne
  refine ⟨hu.deriv.fun_div (by fun_prop) (mul_ne_zero hk (pow_ne_zero _ hne)), ?_, ?_⟩
  · filter_upwards [hne'] with z hz
    rw [div_mul_cancel₀ _ (mul_ne_zero hk (pow_ne_zero _ hz))]
  · filter_upwards [hne', hf.eventually_analyticAt] with z hz hza
    have hz' : f z ^ j ≠ 0 := pow_ne_zero j hz
    rw [deriv_fun_pow hza.differentiableAt, Nat.add_sub_cancel]
    field_simp
    ring

lemma JetRel.of_pow (hS : IsFieldGraph S) (hf : AnalyticAt ℂ f 0) (hf' : AnalyticAt ℂ f' 0) {k : ℕ}
    (hk : k ≠ 0) (H : JetRel S (fun z => f z ^ k) (fun z => f' z ^ k)) (h0 : (f 0, f' 0) ∈ S)
    (hne : f 0 ≠ 0) : JetRel S f f' := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hne' : f' 0 ≠ 0 := fun h => hne ((hS.1 _ _ h0).2 h)
  obtain ⟨hv, e1, e2⟩ := deriv_eventuallyEq_logDeriv_pow_succ hf hne j
  obtain ⟨hv', e1', e2'⟩ := deriv_eventuallyEq_logDeriv_pow_succ hf' hne' j
  have G : JetRel S (fun z => ((j + 1 : ℕ) : ℂ) * f z ^ (j + 1)) (fun z => ((j + 1 : ℕ) : ℂ) * f' z ^ (j + 1)) :=
    (JetRel.const (pair_natCast S (j + 1))).mul H
  have hnz : ¬ (fun z => ((j + 1 : ℕ) : ℂ) * f z ^ (j + 1)) =ᶠ[𝓝 0] 0 := fun hev =>
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero j)) (pow_ne_zero _ hne) hev.eq_of_nhds
  have V := JetRel.of_mul hS hv hv' G hnz (H.deriv.congr e1 e1')
  exact JetRel.of_deriv_eq hf hf' V e2 e2' h0

lemma jetRel_of_weierstrass_system {p q p' q' : ℂ → ℂ} {c c' : ℂ} (hc : (c, c') ∈ S)
    (hp : AnalyticAt ℂ p 0) (hp' : AnalyticAt ℂ p' 0) (hq : AnalyticAt ℂ q 0) (hq' : AnalyticAt ℂ q' 0)
    (e1 : deriv p =ᶠ[𝓝 0] q) (e1' : deriv p' =ᶠ[𝓝 0] q')
    (e2 : deriv q =ᶠ[𝓝 0] fun z => (6 * p z) * p z - c)
    (e2' : deriv q' =ᶠ[𝓝 0] fun z => (6 * p' z) * p' z - c')
    (h0 : (p 0, p' 0) ∈ S) (h1 : (q 0, q' 0) ∈ S) : JetRel S q q' := by
  have hA : AnalyticAt ℂ (fun z => 6 * p z * p z) 0 := by fun_prop
  have hA' : AnalyticAt ℂ (fun z => 6 * p' z * p' z) 0 := by fun_prop
  have hp6 : AnalyticAt ℂ (fun z => 6 * p z) 0 := by fun_prop
  have hp6' : AnalyticAt ℂ (fun z => 6 * p' z) 0 := by fun_prop
  have h6 : ((6 : ℂ), (6 : ℂ)) ∈ S := by simpa using pair_natCast S 6
  have key : ∀ n, (iteratedDeriv n p 0, iteratedDeriv n p' 0) ∈ S ∧
      (iteratedDeriv n q 0, iteratedDeriv n q' 0) ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      cases n with
      | zero => exact ⟨by simpa using h0, by simpa using h1⟩
      | succ n =>
        refine ⟨?_, ?_⟩
        · rw [iteratedDeriv_succ', iteratedDeriv_succ', e1.iteratedDeriv_eq n, e1'.iteratedDeriv_eq n]
          exact (ih n (Nat.lt_succ_self n)).2
        · rw [iteratedDeriv_succ', iteratedDeriv_succ', e2.iteratedDeriv_eq n, e2'.iteratedDeriv_eq n,
            iteratedDeriv_fun_sub hA.contDiffAt contDiffAt_const,
            iteratedDeriv_fun_sub hA'.contDiffAt contDiffAt_const, iteratedDeriv_const, iteratedDeriv_const]
          refine pair_sub (iteratedDeriv_mul_mem_of_iteratedDeriv_mem hp6 hp6' hp hp' n (fun i hi => ?_)
            (fun i hi => (ih i (Nat.lt_succ_of_le hi)).1)) ?_
          · rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
            exact pair_mul h6 (ih i (Nat.lt_succ_of_le hi)).1
          · split_ifs
            · exact hc
            · exact S.zero_mem
  exact ⟨hq, hq', fun n => (key n).2⟩

end GlobalTheory.JetConj
