import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory
namespace CubeFace

theorem glue_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {κ : Type*} (U : κ → Set E) (f : κ → E → ℂ)
    (hU : ∀ k, IsOpen (U k)) (hcov : ∀ x, ∃ k, x ∈ U k)
    (hf : ∀ k, DifferentiableOn ℂ (f k) (U k))
    (hagree : ∀ k k' x, x ∈ U k → x ∈ U k' → f k x = f k' x)
    {S : Set E} (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ k x, ∀ l ∈ S, x ∈ U k → x + l ∈ U k ∧ f k (x + l) = f k x)
    (k k' : κ) (x y : E) (hx : x ∈ U k) (hy : y ∈ U k') : f k x = f k' y := by
  choose s hs using hcov
  have hG : ∀ k x, x ∈ U k → f (s x) x = f k x := fun k x hx => hagree _ _ _ (hs x) hx
  have hd : Differentiable ℂ (fun x => f (s x) x) := by
    intro x
    have h1 : DifferentiableAt ℂ (f (s x)) x :=
      (hf _).differentiableAt ((hU _).mem_nhds (hs x))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [(hU _).mem_nhds (hs x)] with y hy using hG _ _ hy
  have := entire_apply_eq_of_periodic_of_span_real hd hS (fun x l hl => by
    obtain ⟨h1, h2⟩ := hper (s x) x l hl (hs x)
    rw [hG _ _ h1, h2]) x y
  rw [← hG k x hx, ← hG k' y hy]
  exact this

theorem span_triples {V : Type*} [AddCommGroup V] [Module ℝ V] (Λ : Submodule ℤ V)
    (h : Submodule.span ℝ (Λ : Set V) = ⊤) :
    Submodule.span ℝ {l : Fin 3 → V | ∀ a, l a ∈ Λ} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun a _ => ?_
  have h1 : x a ∈ Submodule.span ℝ (Λ : Set V) := by rw [h]; trivial
  have h2 := Submodule.mem_map_of_mem (f := LinearMap.single ℝ (fun _ : Fin 3 => V) a) h1
  rw [Submodule.map_span] at h2
  refine Submodule.span_mono ?_ h2
  rintro _ ⟨v, hv, rfl⟩ b
  by_cases hb : b = a
  · subst hb; simpa using hv
  · simp [Pi.single_eq_of_ne hb]

theorem differentiableOn_prod {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (s : Finset α) (f : α → E → ℂ) (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) U) :
    DifferentiableOn ℂ (fun y => ∏ i ∈ s, f i y) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).fun_mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem prod_subsets (f : Finset (Fin 3) → ℂ) :
    ∏ I, f I = f ∅ * f {0} * f {1} * f {2} * f {0, 1} * f {0, 2} * f {1, 2} * f {0, 1, 2} := by
  have : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [this, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

theorem prod_alt (f : Finset (Fin 3) → ℂ) :
    ∏ I : Finset (Fin 3), f I ^ ((-1 : ℤ) ^ (3 - I.card)) =
      (f ∅)⁻¹ * f {0} * f {1} * f {2} * (f {0, 1})⁻¹ * (f {0, 2})⁻¹ * (f {1, 2})⁻¹ *
        f {0, 1, 2} := by
  rw [prod_subsets]
  have h01 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have h02 : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have h12 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have h012 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  rw [h01, h02, h12, h012]
  norm_num

theorem prod_alt_erase (a : Fin 3) (f : Finset (Fin 3) → ℂ) (hf : ∀ I, f I ≠ 0) :
    ∏ I : Finset (Fin 3), f (I.erase a) ^ ((-1 : ℤ) ^ (3 - I.card)) = 1 := by
  rw [prod_alt (fun I => f (I.erase a))]
  have := hf ∅
  have := hf {0}
  have := hf {1}
  have := hf {2}
  have := hf {0, 1}
  have := hf {0, 2}
  have := hf {1, 2}
  fin_cases a
  · have e1 : ({0, 1} : Finset (Fin 3)).erase 0 = {1} := by decide
    have e2 : ({0, 2} : Finset (Fin 3)).erase 0 = {2} := by decide
    have e3 : ({1, 2} : Finset (Fin 3)).erase 0 = {1, 2} := by decide
    have e4 : ({0, 1, 2} : Finset (Fin 3)).erase 0 = {1, 2} := by decide
    have e5 : ({0} : Finset (Fin 3)).erase 0 = ∅ := by decide
    have e6 : ({1} : Finset (Fin 3)).erase 0 = {1} := by decide
    have e7 : ({2} : Finset (Fin 3)).erase 0 = {2} := by decide
    simp only [Fin.zero_eta, e1, e2, e3, e4, e5, e6, e7, Finset.erase_empty]
    field_simp
  · have e1 : ({0, 1} : Finset (Fin 3)).erase 1 = {0} := by decide
    have e2 : ({0, 2} : Finset (Fin 3)).erase 1 = {0, 2} := by decide
    have e3 : ({1, 2} : Finset (Fin 3)).erase 1 = {2} := by decide
    have e4 : ({0, 1, 2} : Finset (Fin 3)).erase 1 = {0, 2} := by decide
    have e5 : ({0} : Finset (Fin 3)).erase 1 = {0} := by decide
    have e6 : ({1} : Finset (Fin 3)).erase 1 = ∅ := by decide
    have e7 : ({2} : Finset (Fin 3)).erase 1 = {2} := by decide
    simp only [Fin.mk_one, e1, e2, e3, e4, e5, e6, e7, Finset.erase_empty]
    field_simp
  · have e1 : ({0, 1} : Finset (Fin 3)).erase 2 = {0, 1} := by decide
    have e2 : ({0, 2} : Finset (Fin 3)).erase 2 = {0} := by decide
    have e3 : ({1, 2} : Finset (Fin 3)).erase 2 = {1} := by decide
    have e4 : ({0, 1, 2} : Finset (Fin 3)).erase 2 = {0, 1} := by decide
    have e5 : ({0} : Finset (Fin 3)).erase 2 = {0} := by decide
    have e6 : ({1} : Finset (Fin 3)).erase 2 = {1} := by decide
    have e7 : ({2} : Finset (Fin 3)).erase 2 = ∅ := by decide
    simp only [Fin.reduceFinMk, e1, e2, e3, e4, e5, e6, e7, Finset.erase_empty]
    field_simp

def diagChart {ι : Type*} (a b d o : ι) (J : Finset (Fin 3)) : ι :=
  if J = {2} then b else if J = {0, 1} then d
  else if J = {0} ∨ J = {1} ∨ J = {0, 1, 2} then a else o

theorem diagChart_self {ι : Type*} (o : ι) : diagChart o o o o = fun _ => o := by
  funext J; simp [diagChart]

theorem sum_diag {V : Type*} [AddCommGroup V] [Module ℂ V] (z : V) (J : Finset (Fin 3)) :
    ∑ a ∈ J, (![z, z, -z] : Fin 3 → V) a = diagChart z (-z) ((2 : ℂ) • z) 0 J := by
  have : J ∈ ({∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} :
      Finset (Finset (Fin 3))) := by revert J; decide
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [diagChart, two_smul]

theorem diag_mem {V ι : Type*} [AddCommGroup V] [Module ℂ V] (W : ι → Set V) {a b d o : ι}
    {z : V} (ha : z ∈ W a) (hb : -z ∈ W b) (hd : (2 : ℂ) • z ∈ W d) (ho : (0 : V) ∈ W o)
    (J : Finset (Fin 3)) :
    ∑ i ∈ J, (![z, z, -z] : Fin 3 → V) i ∈ W (diagChart a b d o J) := by
  rw [sum_diag]
  unfold diagChart
  split_ifs <;> assumption

theorem diag_prod {V ι : Type*} [AddCommGroup V] [Module ℂ V] (c : ι → ι → V → ℂ)
    (a b d a' b' d' o : ι) (ho : c o o 0 = 1) (z : V) :
    ∏ J : Finset (Fin 3), c (diagChart a b d o J) (diagChart a' b' d' o J)
      (∑ i ∈ J, (![z, z, -z] : Fin 3 → V) i) ^ ((-1 : ℤ) ^ (3 - J.card)) =
      c a a' z ^ 3 * c b b' (-z) * (c d d' ((2 : ℂ) • z))⁻¹ := by
  simp only [sum_diag]
  rw [prod_alt (fun J => c (diagChart a b d o J) (diagChart a' b' d' o J)
    (diagChart z (-z) ((2 : ℂ) • z) 0 J))]
  simp (config := {decide := true}) only [diagChart, if_true, if_false, ho]
  simp only [inv_one, mul_one, one_mul]
  ring

theorem isOpen_sums {g : ℕ} {ι : Type} (W : ι → Set (Fin g → ℂ)) (hW : ∀ i, IsOpen (W i))
    (j : Finset (Fin 3) → ι) :
    IsOpen {x : Fin 3 → Fin g → ℂ | ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)} := by
  rw [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun I => ?_
  exact (hW _).preimage (f := fun x : Fin 3 → Fin g → ℂ => ∑ a ∈ I, x a) (by fun_prop)

section Main

variable {g : ℕ} {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ)
  (hW : ∀ i, IsOpen (W i)) (hcov : ∀ z, ∃ i, z ∈ W i)
  (hc0 : ∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
  (hcc : ∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z)
  (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ)
  (hT : ∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))})
  (hT0 : ∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0)
  (hTT : ∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) →
    (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) →
    T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) *
      T j' x)
  (Λ : Submodule ℤ (Fin g → ℂ)) (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
  (hWp : ∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i)
  (hTp : ∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x)
  (i₀ : ι) (h0 : (0 : Fin g → ℂ) ∈ W i₀)

include hW hcov hc0 hT hTT hΛ hWp hTp h0 in

theorem face (a : Fin 3) (x : Fin 3 → Fin g → ℂ)
    (hx : ∀ I : Finset (Fin 3), ∑ b ∈ I, x b ∈ W i₀) (hxa : x a = 0) :
    T (fun _ => i₀) x = T (fun _ => i₀) 0 := by
  have hsum : ∀ (y : Fin 3 → Fin g → ℂ) (I : Finset (Fin 3)),
      ∑ b ∈ I, Function.update y a 0 b = ∑ b ∈ I.erase a, Function.update y a 0 b :=
    fun y I => (Finset.sum_erase I (by simp)).symm
  have hPd : Differentiable ℂ (fun y : Fin 3 → Fin g → ℂ => Function.update y a 0) := by
    refine differentiable_pi.2 fun b => ?_
    by_cases hb : b = a
    · subst hb; simp
    · simp only [Function.update_of_ne hb]; fun_prop
  have hadd : ∀ y l : Fin 3 → Fin g → ℂ, Function.update (y + l) a 0 =
      Function.update y a 0 + Function.update l a 0 := by
    intro y l
    rw [← Function.update_add, add_zero]
  have hl : ∀ l : Fin 3 → Fin g → ℂ, (∀ b, l b ∈ Λ) → ∀ b, Function.update l a 0 b ∈ Λ := by
    intro l hl b
    by_cases hb : b = a
    · subst hb; simp
    · simpa [Function.update_of_ne hb] using hl b
  have key := glue_const (κ := Finset (Fin 3) → ι)
    (fun j => (fun y : Fin 3 → Fin g → ℂ => Function.update y a 0) ⁻¹'
      {x | ∀ I : Finset (Fin 3), ∑ b ∈ I, x b ∈ W (j (I.erase a))})
    (fun j y => T (fun I => j (I.erase a)) (Function.update y a 0))
    (fun j => (isOpen_sums W hW _).preimage hPd.continuous)
    (fun y => by
      choose s hs using hcov
      refine ⟨fun I => s (∑ b ∈ I, Function.update y a 0 b), fun I => ?_⟩
      rw [hsum]
      exact hs _)
    (fun j => (hT _).comp hPd.differentiableOn (fun y hy => hy))
    (fun j j' y hy hy' => by
      beta_reduce
      rw [hTT _ _ _ hy hy']
      have := prod_alt_erase a (fun I => c (j (I.erase a)) (j' (I.erase a))
        (∑ b ∈ I, Function.update y a 0 b)) (fun I => hc0 _ _ _ (hy I) (hy' I))
      simp only [Finset.erase_idem, ← hsum] at this
      rw [this, one_mul])
    (span_triples Λ hΛ)
    (fun j y l hlm hy => by
      refine ⟨fun I => ?_, ?_⟩
      · simp only [hadd, Pi.add_apply, Finset.sum_add_distrib]
        exact (hWp _ _ _ (Λ.sum_mem fun b _ => hl l hlm b)).2 (hy I)
      · simp only [hadd]
        exact hTp _ _ _ (hl l hlm))
    (fun _ => i₀) (fun _ => i₀) x 0
    (by
      have : Function.update x a 0 = x := by rw [← hxa]; simp
      rw [Set.mem_preimage, this]
      exact hx)
    (by intro I; simpa using h0)
  have : Function.update x a 0 = x := by rw [← hxa]; simp
  simpa [this] using key

include hW hcov hc0 hcc hT hT0 hTT hΛ hWp hTp h0 in

theorem doubling (x : Fin 3 → Fin g → ℂ)
    (hx : ∀ I : Finset (Fin 3), ∑ b ∈ I, x b ∈ W i₀)
    (hx' : ∀ I : Finset (Fin 3), ∑ b ∈ I, (-x) b ∈ W i₀)
    (hx'' : ∀ I : Finset (Fin 3), ∑ b ∈ I, ((2 : ℂ) • x) b ∈ W i₀) :
    T (fun _ => i₀) ((2 : ℂ) • x) * (∏ I : Finset (Fin 3),
      T (fun _ => i₀) ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^
        ((-1 : ℤ) ^ (3 - I.card))) * T (fun _ => i₀) 0 ^ 3 =
      T (fun _ => i₀) x ^ 3 * T (fun _ => i₀) (-x) := by
  have hone : c i₀ i₀ 0 = 1 :=
    mul_left_cancel₀ (hc0 _ _ _ h0 h0) (by rw [hcc _ _ _ _ h0 h0 h0, mul_one])
  have sneg : ∀ (y : Fin 3 → Fin g → ℂ) (I : Finset (Fin 3)),
      ∑ b ∈ I, (-y) b = -∑ b ∈ I, y b := fun y I => by simp
  have stwo : ∀ (y : Fin 3 → Fin g → ℂ) (I : Finset (Fin 3)),
      ∑ b ∈ I, ((2 : ℂ) • y) b = (2 : ℂ) • ∑ b ∈ I, y b := fun y I => by
    simp [Finset.smul_sum]
  let κ := (Finset (Fin 3) → ι) × (Finset (Fin 3) → ι) × (Finset (Fin 3) → ι)
  let U : κ → Set (Fin 3 → Fin g → ℂ) := fun k =>
    {y | (∀ I : Finset (Fin 3), ∑ b ∈ I, y b ∈ W (k.1 I)) ∧
      (∀ I : Finset (Fin 3), ∑ b ∈ I, (-y) b ∈ W (k.2.1 I)) ∧
      (∀ I : Finset (Fin 3), ∑ b ∈ I, ((2 : ℂ) • y) b ∈ W (k.2.2 I))}
  let D : κ → Finset (Fin 3) → (Fin 3 → Fin g → ℂ) → ℂ := fun k I y =>
    T (diagChart (k.1 I) (k.2.1 I) (k.2.2 I) i₀) ![∑ a ∈ I, y a, ∑ a ∈ I, y a, -∑ a ∈ I, y a]
  let R : κ → (Fin 3 → Fin g → ℂ) → ℂ := fun k y =>
    T k.2.2 ((2 : ℂ) • y) * (∏ I : Finset (Fin 3), D k I y ^ ((-1 : ℤ) ^ (3 - I.card))) /
      (T k.1 y ^ 3 * T k.2.1 (-y))
  have hDm : ∀ k y, y ∈ U k → ∀ I J : Finset (Fin 3),
      ∑ i ∈ J, (![∑ a ∈ I, y a, ∑ a ∈ I, y a, -∑ a ∈ I, y a] : Fin 3 → Fin g → ℂ) i ∈
        W (diagChart (k.1 I) (k.2.1 I) (k.2.2 I) i₀ J) := fun k y hy I =>
    diag_mem W (hy.1 I) (sneg y I ▸ hy.2.1 I) (stwo y I ▸ hy.2.2 I) h0
  have hD0 : ∀ k y, y ∈ U k → ∀ I, D k I y ≠ 0 := fun k y hy I => hT0 _ _ (hDm k y hy I)
  have key := glue_const U R
    (fun k => (isOpen_sums W hW k.1).inter
      (((isOpen_sums W hW k.2.1).preimage continuous_neg).inter
        ((isOpen_sums W hW k.2.2).preimage (continuous_const_smul (2 : ℂ)))))
    (fun y => by
      choose s hs using hcov
      exact ⟨(fun I => s _, fun I => s _, fun I => s _), fun I => hs _, fun I => hs _,
        fun I => hs _⟩)
    (fun k => by
      have h1 : DifferentiableOn ℂ (T k.1) (U k) := (hT _).mono fun y hy => hy.1
      have h2 : DifferentiableOn ℂ (fun y => T k.2.1 (-y)) (U k) :=
        (hT _).comp (f := fun y : Fin 3 → Fin g → ℂ => -y) (by fun_prop) fun y hy => hy.2.1
      have h3 : DifferentiableOn ℂ (fun y => T k.2.2 ((2 : ℂ) • y)) (U k) :=
        (hT _).comp (f := fun y : Fin 3 → Fin g → ℂ => (2 : ℂ) • y) (by fun_prop)
          fun y hy => hy.2.2
      have h4 : ∀ I, DifferentiableOn ℂ (D k I) (U k) := fun I => by
        refine (hT _).comp (f := fun y : Fin 3 → Fin g → ℂ =>
          (![∑ a ∈ I, y a, ∑ a ∈ I, y a, -∑ a ∈ I, y a] : Fin 3 → Fin g → ℂ)) ?_
          fun y hy => hDm k y hy I
        refine Differentiable.differentiableOn (differentiable_pi.2 fun b => ?_)
        fin_cases b <;> simp <;> fun_prop
      have h5 : DifferentiableOn ℂ (fun y => ∏ I : Finset (Fin 3),
          D k I y ^ ((-1 : ℤ) ^ (3 - I.card))) (U k) :=
        differentiableOn_prod _ _ fun I _ => (h4 I).zpow (Or.inl fun y hy => hD0 k y hy I)
      have h6 : DifferentiableOn ℂ (fun y => (T k.1 y ^ 3 * T k.2.1 (-y))⁻¹) (U k) :=
        DifferentiableOn.fun_inv ((h1.fun_pow 3).fun_mul h2) fun y (hy : y ∈ U k) =>
          mul_ne_zero (pow_ne_zero _ (hT0 _ _ hy.1)) (hT0 _ _ hy.2.1)
      exact ((h3.fun_mul h5).fun_mul h6).congr fun y _ => div_eq_mul_inv _ _)
    (fun k k' y hy hy' => by
      have e1 := hTT _ _ _ hy.1 hy'.1
      have e2 := hTT _ _ _ hy.2.1 hy'.2.1
      have e3 := hTT _ _ _ hy.2.2 hy'.2.2
      have e4 : ∀ I, D k I y = c (k.1 I) (k'.1 I) (∑ a ∈ I, y a) ^ 3 *
          c (k.2.1 I) (k'.2.1 I) (∑ a ∈ I, (-y) a) *
          (c (k.2.2 I) (k'.2.2 I) (∑ a ∈ I, ((2 : ℂ) • y) a))⁻¹ * D k' I y := fun I => by
        rw [sneg, stwo, ← diag_prod c _ _ _ _ _ _ i₀ hone]
        exact hTT _ _ _ (hDm k y hy I) (hDm k' y hy' I)
      have n1 : (∏ I : Finset (Fin 3), c (k.1 I) (k'.1 I) (∑ a ∈ I, y a) ^
          ((-1 : ℤ) ^ (3 - I.card))) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (hc0 _ _ _ (hy.1 I) (hy'.1 I))
      have n2 : (∏ I : Finset (Fin 3), c (k.2.1 I) (k'.2.1 I) (∑ a ∈ I, (-y) a) ^
          ((-1 : ℤ) ^ (3 - I.card))) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (hc0 _ _ _ (hy.2.1 I) (hy'.2.1 I))
      have n3 : (∏ I : Finset (Fin 3), c (k.2.2 I) (k'.2.2 I) (∑ a ∈ I, ((2 : ℂ) • y) a) ^
          ((-1 : ℤ) ^ (3 - I.card))) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (hc0 _ _ _ (hy.2.2 I) (hy'.2.2 I))
      have m1 := hT0 _ _ hy'.1
      have m2 := hT0 _ _ hy'.2.1
      have e5 : (∏ I : Finset (Fin 3), D k I y ^ ((-1 : ℤ) ^ (3 - I.card))) =
          (∏ I : Finset (Fin 3), c (k.1 I) (k'.1 I) (∑ a ∈ I, y a) ^
            ((-1 : ℤ) ^ (3 - I.card))) ^ 3 *
          (∏ I : Finset (Fin 3), c (k.2.1 I) (k'.2.1 I) (∑ a ∈ I, (-y) a) ^
            ((-1 : ℤ) ^ (3 - I.card))) *
          (∏ I : Finset (Fin 3), c (k.2.2 I) (k'.2.2 I) (∑ a ∈ I, ((2 : ℂ) • y) a) ^
            ((-1 : ℤ) ^ (3 - I.card)))⁻¹ *
          ∏ I : Finset (Fin 3), D k' I y ^ ((-1 : ℤ) ^ (3 - I.card)) := by
        rw [← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
          ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun I _ => ?_
        rw [e4 I, mul_zpow, mul_zpow, mul_zpow, _root_.inv_zpow, pow_three, pow_three, mul_zpow,
          mul_zpow]
      change T k.2.2 ((2 : ℂ) • y) * _ / (T k.1 y ^ 3 * T k.2.1 (-y)) =
        T k'.2.2 ((2 : ℂ) • y) * _ / (T k'.1 y ^ 3 * T k'.2.1 (-y))
      rw [e5, e1, e2, e3]
      generalize (∏ I : Finset (Fin 3), c (k.1 I) (k'.1 I) (∑ a ∈ I, y a) ^
          ((-1 : ℤ) ^ (3 - I.card))) = A at n1 ⊢
      generalize (∏ I : Finset (Fin 3), c (k.2.1 I) (k'.2.1 I) (∑ a ∈ I, (-y) a) ^
          ((-1 : ℤ) ^ (3 - I.card))) = B at n2 ⊢
      generalize (∏ I : Finset (Fin 3), c (k.2.2 I) (k'.2.2 I) (∑ a ∈ I, ((2 : ℂ) • y) a) ^
          ((-1 : ℤ) ^ (3 - I.card))) = C at n3 ⊢
      field_simp)
    (span_triples Λ hΛ)
    (fun k y l hl hy => by
      have hl1 : ∀ a, (-l) a ∈ Λ := fun a => Λ.neg_mem (hl a)
      have hl2 : ∀ a, ((2 : ℂ) • l) a ∈ Λ := fun a => by
        rw [Pi.smul_apply, two_smul]; exact Λ.add_mem (hl a) (hl a)
      have hs : ∀ (j : Finset (Fin 3) → ι) (y l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) →
          (∀ I : Finset (Fin 3), ∑ b ∈ I, y b ∈ W (j I)) →
          ∀ I : Finset (Fin 3), ∑ b ∈ I, (y + l) b ∈ W (j I) := fun j y l hl hy I => by
        simp only [Pi.add_apply, Finset.sum_add_distrib]
        exact (hWp _ _ _ (Λ.sum_mem fun b _ => hl b)).2 (hy I)
      have hD : ∀ I, D k I (y + l) = D k I y := fun I => by
        have hm : ∑ a ∈ I, l a ∈ Λ := Λ.sum_mem fun b _ => hl b
        have := hTp (diagChart (k.1 I) (k.2.1 I) (k.2.2 I) i₀)
          ![∑ a ∈ I, y a, ∑ a ∈ I, y a, -∑ a ∈ I, y a]
          ![∑ a ∈ I, l a, ∑ a ∈ I, l a, -∑ a ∈ I, l a] (fun a => by
            fin_cases a
            · exact hm
            · exact hm
            · exact Λ.neg_mem hm)
        refine Eq.trans ?_ this
        refine congrArg (T _) ?_
        funext b
        fin_cases b <;> simp [Finset.sum_add_distrib, add_comm]
      refine ⟨⟨hs _ _ _ hl hy.1, ?_, ?_⟩, ?_⟩
      · rw [neg_add]; exact hs _ _ _ hl1 hy.2.1
      · rw [smul_add]; exact hs _ _ _ hl2 hy.2.2
      · simp only [R, hD]
        rw [neg_add, smul_add, hTp _ _ _ hl, hTp _ _ _ hl1, hTp _ _ _ hl2])
    (fun _ => i₀, fun _ => i₀, fun _ => i₀) (fun _ => i₀, fun _ => i₀, fun _ => i₀) x 0
    ⟨hx, hx', hx''⟩
    ⟨fun I => by simpa using h0, fun I => by simpa using h0, fun I => by simpa using h0⟩
  have m0 : T (fun _ => i₀) 0 ≠ 0 := hT0 _ _ fun I => by simpa using h0
  have m1 := hT0 (fun _ => i₀) _ hx
  have m2 := hT0 (fun _ => i₀) _ hx'
  have hz : (![0, 0, -0] : Fin 3 → Fin g → ℂ) = 0 := by
    funext b; fin_cases b <;> simp
  have hp := prod_alt_erase 0 (fun _ => T (fun _ => i₀) 0) fun _ => m0
  simp only [R, D, diagChart_self, smul_zero, Pi.zero_apply, Finset.sum_const_zero, hz, hp] at key
  rw [neg_zero, div_eq_div_iff (mul_ne_zero (pow_ne_zero _ m1) m2)
    (mul_ne_zero (pow_ne_zero _ m0) m0)] at key
  refine mul_right_cancel₀ m0 ?_
  linear_combination key

end Main

end CubeFace

theorem cube_section_faces_and_doubling : (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∀ (i₀ : ι), 0 ∈ W i₀ → ∀ F : (Fin 3 → Fin g → ℂ) → ℂ, F = T (fun _ => i₀) → (∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) := by
  intro g ι W c hW hcov _ hc0 hcc T hT hT0 hTT Λ _ hΛ hWp _ hTp i₀ h0 F hF
  subst hF
  have hO := CubeFace.isOpen_sums W hW (fun _ => i₀)
  have hn : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W i₀ :=
    hO.mem_nhds fun I => by simpa using h0
  have hn1 : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ I : Finset (Fin 3), ∑ a ∈ I, (-x) a ∈ W i₀ :=
    (hO.preimage continuous_neg).mem_nhds fun I => by simpa using h0
  have hn2 : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ),
      ∀ I : Finset (Fin 3), ∑ a ∈ I, ((2 : ℂ) • x) a ∈ W i₀ :=
    (hO.preimage (continuous_const_smul (2 : ℂ))).mem_nhds fun I => by simpa using h0
  refine ⟨fun a => ?_, ?_⟩
  · filter_upwards [hn] with x hx hxa
    exact CubeFace.face W c hW hcov hc0 T hT hTT Λ hΛ hWp hTp i₀ h0 a x hx hxa
  · filter_upwards [hn, hn1, hn2] with x hx hx1 hx2
    exact CubeFace.doubling W c hW hcov hc0 hcc T hT hT0 hTT Λ hΛ hWp hTp i₀ h0 x hx hx1 hx2

end GlobalTheory
