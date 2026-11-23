import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitivePresentationCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

namespace IsGermCombination

variable {σ : Type} [Fintype σ] {w : σ → ℂ} {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ}

theorem congr {f g : (σ → ℂ) → ℂ} (hf : IsGermCombination w p f) (h : ∀ᶠ z in 𝓝 w, f z = g z) :
    IsGermCombination w p g := by
  obtain ⟨c, hc, he⟩ := hf
  exact ⟨c, hc, by filter_upwards [he, h] with z hz h' using h' ▸ hz⟩

theorem zero : IsGermCombination w p (fun _ => 0) :=
  ⟨fun _ _ => 0, fun _ => analyticAt_const, Eventually.of_forall fun z => by simp⟩

theorem generator (i : Fin k) : IsGermCombination w p (p i) := by
  classical
  refine ⟨fun j _ => if j = i then 1 else 0, fun _ => analyticAt_const, Eventually.of_forall fun z => ?_⟩
  simp

theorem add {f g : (σ → ℂ) → ℂ} (hf : IsGermCombination w p f) (hg : IsGermCombination w p g) :
    IsGermCombination w p (fun z => f z + g z) := by
  obtain ⟨c, hc, he⟩ := hf
  obtain ⟨c', hc', he'⟩ := hg
  refine ⟨fun i => c i + c' i, fun i => (hc i).add (hc' i), ?_⟩
  filter_upwards [he, he'] with z hz hz'
  simp only [Pi.add_apply, hz, hz', add_mul, Finset.sum_add_distrib]

theorem mul_left {f g : (σ → ℂ) → ℂ} (hg : AnalyticAt ℂ g w) (hf : IsGermCombination w p f) :
    IsGermCombination w p (fun z => g z * f z) := by
  obtain ⟨c, hc, he⟩ := hf
  refine ⟨fun i => g * c i, fun i => hg.mul (hc i), ?_⟩
  filter_upwards [he] with z hz
  simp only [Pi.mul_apply, hz, Finset.mul_sum, mul_assoc]

theorem neg {f : (σ → ℂ) → ℂ} (hf : IsGermCombination w p f) :
    IsGermCombination w p (fun z => - f z) :=
  (mul_left (g := fun _ => (-1 : ℂ)) analyticAt_const hf).congr (Eventually.of_forall fun z => by ring)

theorem sub {f g : (σ → ℂ) → ℂ} (hf : IsGermCombination w p f) (hg : IsGermCombination w p g) :
    IsGermCombination w p (fun z => f z - g z) :=
  (hf.add hg.neg).congr (Eventually.of_forall fun z => by ring)

theorem sum {ι : Type*} (s : Finset ι) {f : ι → (σ → ℂ) → ℂ} (h : ∀ i ∈ s, IsGermCombination w p (f i)) :
    IsGermCombination w p (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IsGermCombination w p fun _ => 0)
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact (h1.add h2).congr (Eventually.of_forall fun z => by rw [Finset.sum_insert ha])

theorem pow_sub_pow {f g : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w) (hg : AnalyticAt ℂ g w)
    (h : IsGermCombination w p (fun z => f z - g z)) (n : ℕ) :
    IsGermCombination w p (fun z => f z ^ n - g z ^ n) := by
  induction n with
  | zero => exact zero.congr (Eventually.of_forall fun z => by simp)
  | succ n ih =>
    exact ((mul_left hf ih).add (mul_left (hg.pow n) h)).congr
      (Eventually.of_forall fun z => by simp only [Pi.pow_apply]; ring)

theorem prod_sub_prod {ι : Type*} (s : Finset ι) {f g : ι → (σ → ℂ) → ℂ}
    (hf : ∀ i, AnalyticAt ℂ (f i) w) (hg : ∀ i, AnalyticAt ℂ (g i) w)
    (h : ∀ i, IsGermCombination w p (fun z => f i z - g i z)) :
    IsGermCombination w p (fun z => ∏ i ∈ s, f i z - ∏ i ∈ s, g i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact zero.congr (Eventually.of_forall fun z => by simp)
  | insert a s ha ih =>
    have hgs : AnalyticAt ℂ (fun z => ∏ i ∈ s, g i z) w := Finset.analyticAt_fun_prod s fun i _ => hg i
    exact ((mul_left (hf a) ih).add (mul_left hgs (h a))).congr
      (Eventually.of_forall fun z => by rw [Finset.prod_insert ha, Finset.prod_insert ha]; ring)

end IsGermCombination

def analyticSubring {d : ℕ} (y₀ : Fin d → ℂ) : Subring ((Fin d → ℂ) → ℂ) where
  carrier := {f | AnalyticAt ℂ f y₀}
  mul_mem' ha hb := AnalyticAt.mul ha hb
  one_mem' := analyticAt_const
  add_mem' ha hb := AnalyticAt.add ha hb
  zero_mem' := analyticAt_const
  neg_mem' ha := AnalyticAt.neg ha

def evalAt {d : ℕ} (y₀ y : Fin d → ℂ) : analyticSubring y₀ →+* ℂ :=
  (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) y).comp (analyticSubring y₀).subtype

@[simp] theorem evalAt_apply {d : ℕ} (y₀ y : Fin d → ℂ) (f : analyticSubring y₀) :
    evalAt y₀ y f = (f : (Fin d → ℂ) → ℂ) y := rfl

def pev {d : ℕ} {y₀ : Fin d → ℂ} (y : Fin d → ℂ) (t : ℂ) : (analyticSubring y₀)[X] →+* ℂ :=
  (Polynomial.evalRingHom t).comp (Polynomial.mapRingHom (evalAt y₀ y))

section pev

variable {d : ℕ} {y₀ : Fin d → ℂ}

@[simp] theorem pev_C (y : Fin d → ℂ) (t : ℂ) (f : analyticSubring y₀) :
    pev y t (C f) = (f : (Fin d → ℂ) → ℂ) y := by
  simp [pev]

@[simp] theorem pev_X (y : Fin d → ℂ) (t : ℂ) : pev (y₀ := y₀) y t X = t := by
  simp [pev]

theorem pev_eq_sum_range (H : (analyticSubring y₀)[X]) {n : ℕ} (hn : H.natDegree < n) (y : Fin d → ℂ)
    (t : ℂ) : pev y t H = ∑ i ∈ Finset.range n, (H.coeff i : (Fin d → ℂ) → ℂ) y * t ^ i := by
  simp only [pev, RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, coe_mapRingHom, eval_map]
  rw [eval₂_eq_sum_range' _ hn]
  rfl

theorem analyticAt_pev_comp {σ : Type} [Fintype σ] (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (ℓ : (σ → ℂ) →L[ℂ] ℂ) (H : (analyticSubring (A w))[X]) :
    AnalyticAt ℂ (fun z => pev (A z) (ℓ z) H) w := by
  have e : (fun z => pev (A z) (ℓ z) H) =
      fun z => ∑ i ∈ Finset.range (H.natDegree + 1), (H.coeff i : (Fin d → ℂ) → ℂ) (A z) * ℓ z ^ i :=
    funext fun z => pev_eq_sum_range H (Nat.lt_succ_self _) _ _
  rw [e]
  refine Finset.analyticAt_fun_sum _ fun i _ => ?_
  exact (AnalyticAt.comp (g := ((H.coeff i : analyticSubring (A w)) : (Fin d → ℂ) → ℂ))
    (H.coeff i).2 (A.analyticAt w)).mul ((ℓ.analyticAt w).pow i)

end pev

def presPoly {d N : ℕ} {y₀ : Fin d → ℂ} (c : Fin N → (Fin d → ℂ) → ℂ) (hc : ∀ j, AnalyticAt ℂ (c j) y₀) :
    (analyticSubring y₀)[X] :=
  X ^ N + ∑ j : Fin N, C (⟨c j, hc j⟩ : analyticSubring y₀) * X ^ (j : ℕ)

theorem presPoly_monic {d N : ℕ} {y₀ : Fin d → ℂ} (c : Fin N → (Fin d → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) y₀) : (presPoly c hc).Monic :=
  monic_X_pow_add (degree_sum_fin_lt _)

theorem presPoly_degree {d N : ℕ} {y₀ : Fin d → ℂ} (c : Fin N → (Fin d → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) y₀) : (presPoly c hc).degree = N := by
  unfold presPoly
  rw [degree_add_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  exact degree_sum_fin_lt _

theorem pev_presPoly {d N : ℕ} {y₀ : Fin d → ℂ} (c : Fin N → (Fin d → ℂ) → ℂ)
    (hc : ∀ j, AnalyticAt ℂ (c j) y₀) (y : Fin d → ℂ) (t : ℂ) :
    pev y t (presPoly c hc) = t ^ N + ∑ j, c j y * t ^ (j : ℕ) := by
  simp [presPoly, map_sum]

theorem pev_eq_zero_of_presentation {σ : Type} [Fintype σ] {w : σ → ℂ} {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ}
    {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {ℓ : (σ → ℂ) →L[ℂ] ℂ} {N : ℕ} {c : Fin N → (Fin d → ℂ) → ℂ}
    {δ : (Fin d → ℂ) → ℂ} (hP : IsPrimitivePresentation w p A ℓ c δ) (H : (analyticSubring (A w))[X])
    (hH : IsGermCombination w p (fun z => pev (A z) (ℓ z) H)) :
    ∀ᶠ y in 𝓝 (A w), ∀ t : ℂ, t ^ N + ∑ j, c j y * t ^ (j : ℕ) = 0 → pev y t H = 0 := by
  obtain ⟨hc, -, h1, h2, -⟩ := hP
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact Eventually.of_forall fun y t ht => by simp at ht
  set F := presPoly c hc with hFdef
  have hmon : F.Monic := presPoly_monic c hc
  set R := H %ₘ F with hRdef
  set Q := H /ₘ F with hQdef
  have hdec : ∀ y t, pev y t H = pev y t R + pev y t F * pev y t Q := by
    intro y t
    rw [← map_mul, ← map_add, hRdef, hQdef, modByMonic_add_div]
  have hRdeg : R.natDegree < N := by
    by_cases hR0 : R = 0
    · rw [hR0, natDegree_zero]; exact hN
    rw [natDegree_lt_iff_degree_lt hR0, ← presPoly_degree c hc]
    exact degree_modByMonic_lt _ hmon
  have hRsum : ∀ y t, pev y t R = ∑ j : Fin N, (R.coeff j : (Fin d → ℂ) → ℂ) y * t ^ (j : ℕ) := by
    intro y t
    rw [pev_eq_sum_range R hRdeg, Fin.sum_univ_eq_sum_range (fun i => (R.coeff i : (Fin d → ℂ) → ℂ) y * t ^ i)]
  have hRP : IsGermCombination w p
      (fun z => ∑ j : Fin N, (R.coeff j : (Fin d → ℂ) → ℂ) (A z) * ℓ z ^ (j : ℕ)) := by
    refine (hH.sub (IsGermCombination.mul_left (analyticAt_pev_comp w A ℓ Q) h1)).congr
      (Eventually.of_forall fun z => ?_)
    rw [← hRsum, hdec, pev_presPoly]
    ring
  have hzero := h2 (fun j => (R.coeff j : (Fin d → ℂ) → ℂ)) (fun j => (R.coeff j).2) hRP
  filter_upwards [eventually_all.2 hzero] with y hy t ht
  rw [hdec, hRsum, pev_presPoly, ht, zero_mul, add_zero]
  exact Finset.sum_eq_zero fun j _ => by rw [hy j, zero_mul]

theorem roots_near_of_centred {E : Type*} [TopologicalSpace E] {n : ℕ} (b : Fin n → E → ℂ) (y₀ : E) (u : ℂ)
    (hb : ∀ j, ContinuousAt (b j) y₀) (h0 : ∀ T : ℂ, T ^ n + ∑ j, b j y₀ * T ^ (j : ℕ) = (T - u) ^ n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 y₀, ∀ x : ℂ, x ^ n + ∑ j, b j y * x ^ (j : ℕ) = 0 → ‖x - u‖ < ε := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact Eventually.of_forall fun y x hx => by simp at hx
  set S : E → ℝ := fun y => ∑ j, ‖b j y‖ with hS
  set B : ℝ := max 1 (S y₀ + 1) with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  have hSt : Tendsto S (𝓝 y₀) (𝓝 (S y₀)) :=
    tendsto_finsetSum _ fun j _ => (hb j).tendsto.norm
  have hDt : Tendsto (fun y => ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ)) (𝓝 y₀) (𝓝 0) := by
    have : Tendsto (fun y => ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ)) (𝓝 y₀)
        (𝓝 (∑ j : Fin n, ‖b j y₀ - b j y₀‖ * B ^ (j : ℕ))) :=
      tendsto_finsetSum _ fun j _ => ((tendsto_const_nhds.sub (hb j).tendsto).norm).mul_const _
    simpa using this
  have hεn : (0 : ℝ) < ε ^ n := pow_pos hε n
  filter_upwards [hSt.eventually (gt_mem_nhds (lt_add_one (S y₀))), hDt.eventually (gt_mem_nhds hεn)]
    with y hSy hDy x hx

  have hxB : ‖x‖ ≤ B := by
    by_cases hx1 : ‖x‖ ≤ 1
    · exact hx1.trans hB1
    replace hx1 := lt_of_not_ge hx1
    have hxn : x ^ n = -∑ j, b j y * x ^ (j : ℕ) := eq_neg_of_add_eq_zero_left hx
    have hle : ‖x‖ ^ n ≤ S y * ‖x‖ ^ (n - 1) := by
      calc ‖x‖ ^ n = ‖∑ j, b j y * x ^ (j : ℕ)‖ := by rw [← norm_pow, hxn, norm_neg]
        _ ≤ ∑ j, ‖b j y * x ^ (j : ℕ)‖ := norm_sum_le _ _
        _ ≤ ∑ j : Fin n, ‖b j y‖ * ‖x‖ ^ (n - 1) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx1.le (by omega)) (norm_nonneg _)
        _ = S y * ‖x‖ ^ (n - 1) := by rw [hS, Finset.sum_mul]
    have hpos : 0 < ‖x‖ ^ (n - 1) := pow_pos (zero_lt_one.trans hx1) _
    have : ‖x‖ * ‖x‖ ^ (n - 1) ≤ S y * ‖x‖ ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hn]; exact hle
    have hxS : ‖x‖ ≤ S y := le_of_mul_le_mul_right this hpos
    exact hxS.trans (hSy.le.trans (le_max_right _ _))

  have hid : (x - u) ^ n = ∑ j, (b j y₀ - b j y) * x ^ (j : ℕ) := by
    rw [← h0 x]
    have : x ^ n = -∑ j, b j y * x ^ (j : ℕ) := eq_neg_of_add_eq_zero_left hx
    rw [this]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hle : ‖x - u‖ ^ n ≤ ∑ j, ‖b j y₀ - b j y‖ * B ^ (j : ℕ) := by
    calc ‖x - u‖ ^ n = ‖∑ j, (b j y₀ - b j y) * x ^ (j : ℕ)‖ := by rw [← norm_pow, hid]
      _ ≤ ∑ j, ‖(b j y₀ - b j y) * x ^ (j : ℕ)‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n, ‖b j y₀ - b j y‖ * B ^ (j : ℕ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxB _) (norm_nonneg _)
  have : ‖x - u‖ ^ n < ε ^ n := hle.trans_lt hDy
  exact lt_of_pow_lt_pow_left₀ n hε.le this

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
