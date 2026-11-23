import Mathlib

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.AnalyticWord

variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}

def word (Z : ι → Module.End ℂ V) (l : List ι) : Module.End ℂ V := (l.map Z).prod

lemma word_nil (Z : ι → Module.End ℂ V) : word Z [] = 1 := by simp [word]

lemma word_cons (Z : ι → Module.End ℂ V) (i : ι) (l : List ι) :
    word Z (i :: l) = Z i * word Z l := by simp [word]

lemma word_append (Z : ι → Module.End ℂ V) (p q : List ι) :
    word Z (p ++ q) = word Z p * word Z q := by simp [word, List.prod_append]

lemma word_comm (Z : ι → Module.End ℂ V) (Ω : Module.End ℂ V) (hΩ : ∀ i, Ω * Z i = Z i * Ω)
    (l : List ι) : Ω * word Z l = word Z l * Ω := by
  induction l with
  | nil => rw [GlobalTheory.CompanionTheory.AnalyticWord.word_nil, mul_one, one_mul]
  | cons i l ih => rw [GlobalTheory.CompanionTheory.AnalyticWord.word_cons, ← mul_assoc, hΩ, mul_assoc, ih, mul_assoc]

def bnd [Finite ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V) {m : ℕ} (y : Fin m → V) (k : ℕ) : ℝ :=
  (((List.finite_length_eq ι k).toFinset ×ˢ (univ : Finset (Fin m))).sup
    fun p => ‖j (word Z p.1 (y p.2))‖₊ : NNReal)

section Bnd

variable [Finite ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V) {m : ℕ} (y : Fin m → V)

lemma bnd_nonneg (k : ℕ) : 0 ≤ bnd j Z y k := by
  unfold GlobalTheory.CompanionTheory.AnalyticWord.bnd
  exact NNReal.coe_nonneg _

lemma le_bnd {l : List ι} {k : ℕ} (hl : l.length = k) (e : Fin m) :
    ‖j (word Z l (y e))‖ ≤ bnd j Z y k := by
  have hmem : (l, e) ∈ (List.finite_length_eq ι k).toFinset ×ˢ (univ : Finset (Fin m)) := by
    simp [hl]
  have h := Finset.le_sup (f := fun p : List ι × Fin m => ‖j (GlobalTheory.CompanionTheory.AnalyticWord.word Z p.1 (y p.2))‖₊) hmem
  unfold GlobalTheory.CompanionTheory.AnalyticWord.bnd
  exact (coe_nnnorm _).symm.trans_le (NNReal.coe_le_coe.2 h)

lemma bnd_le {k : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ (l : List ι) (e : Fin m), l.length = k → ‖j (word Z l (y e))‖ ≤ B) :
    bnd j Z y k ≤ B := by
  unfold GlobalTheory.CompanionTheory.AnalyticWord.bnd
  have hs : ((List.finite_length_eq ι k).toFinset ×ˢ (univ : Finset (Fin m))).sup
      (fun p => ‖j (GlobalTheory.CompanionTheory.AnalyticWord.word Z p.1 (y p.2))‖₊) ≤ B.toNNReal := by
    refine Finset.sup_le fun p hp => ?_
    rw [Finset.mem_product, Set.Finite.mem_toFinset] at hp
    show ‖j (GlobalTheory.CompanionTheory.AnalyticWord.word Z p.1 (y p.2))‖₊ ≤ B.toNNReal
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hB]
    exact h p.1 p.2 hp.1
  calc _ ≤ ((B.toNNReal : NNReal) : ℝ) := NNReal.coe_le_coe.2 hs
    _ = B := Real.coe_toNNReal _ hB

lemma comb_le {l : List ι} {k : ℕ} (hl : l.length = k) (a : Fin m → ℂ) :
    ‖j (word Z l (∑ f, a f • y f))‖ ≤ (∑ f, ‖a f‖) * bnd j Z y k := by
  rw [map_sum, map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  rw [map_smul, map_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left (GlobalTheory.CompanionTheory.AnalyticWord.le_bnd j Z y hl f) (norm_nonneg _)

end Bnd

lemma quad_step {x y A B : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : x ^ 2 ≤ y * (A * y + B * x)) : x ≤ (√A + B) * y := by
  by_contra hlt
  push_neg at hlt
  have hs0 := Real.sqrt_nonneg A
  have hss : √A * √A * (y * y) = A * (y * y) := by rw [Real.mul_self_sqrt hA]
  have hx1 : √A * y ≤ x := by nlinarith [mul_nonneg hB hy]
  have hxpos : 0 < x := lt_of_le_of_lt (mul_nonneg (add_nonneg hs0 hB) hy) hlt
  nlinarith [mul_lt_mul_of_pos_left hlt hxpos, mul_nonneg (sub_nonneg.2 hx1) (mul_nonneg hs0 hy), hss]

lemma comm_S (Z : ι → Module.End ℂ V) [Fintype ι] (K : Finset ι) (c : ι → ι → ι → ℂ)
    (hcomm : ∀ κ i, Z κ * Z i - Z i * Z κ = ∑ l, c κ i l • Z l) (i : ι) :
    (∑ κ ∈ K, Z κ * Z κ) * Z i - Z i * (∑ κ ∈ K, Z κ * Z κ) =
      ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun κ _ => ?_
  have e : Z κ * Z κ * Z i - Z i * (Z κ * Z κ) =
      Z κ * (Z κ * Z i - Z i * Z κ) + (Z κ * Z i - Z i * Z κ) * Z κ := by
    simp only [mul_sub, sub_mul, mul_assoc]
    abel
  rw [e, hcomm, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, smul_add]

lemma sum_sq_le [Fintype ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V)
    (hskew : ∀ i v w, inner ℂ (j (Z i v)) (j w) = - inner ℂ (j v) (j (Z i w)))
    (S Ω : Module.End ℂ V) (hT : ∑ i, Z i * Z i = Ω + S + S) (v : V) (i : ι) :
    ‖j (Z i v)‖ ^ 2 ≤ ‖j v‖ * (‖j (Ω v)‖ + 2 * ‖j (S v)‖) := by
  have key : ∀ k, ‖j (Z k v)‖ ^ 2 = - RCLike.re (inner ℂ (j v) (j ((Z k * Z k) v))) := by
    intro k
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), hskew, Module.End.mul_apply, map_neg]
  have hsum : ∑ k, ‖j (Z k v)‖ ^ 2 = - RCLike.re (inner ℂ (j v) (j ((Ω + S + S) v))) := by
    rw [← hT, LinearMap.sum_apply, map_sum, inner_sum, map_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => key k
  have hle : ‖j (Z i v)‖ ^ 2 ≤ ∑ k, ‖j (Z k v)‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖j (Z k v)‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ i)
  rw [hsum] at hle
  have h2 : - RCLike.re (inner ℂ (j v) (j ((Ω + S + S) v))) ≤ ‖j v‖ * ‖j ((Ω + S + S) v)‖ :=
    (neg_le_abs _).trans ((RCLike.abs_re_le_norm _).trans (norm_inner_le_norm _ _))
  have h3 : ‖j ((Ω + S + S) v)‖ ≤ ‖j (Ω v)‖ + 2 * ‖j (S v)‖ := by
    rw [LinearMap.add_apply, LinearMap.add_apply, map_add, map_add]
    calc _ ≤ ‖j (Ω v) + j (S v)‖ + ‖j (S v)‖ := norm_add_le _ _
      _ ≤ ‖j (Ω v)‖ + ‖j (S v)‖ + ‖j (S v)‖ := add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by ring
  exact (hle.trans h2).trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))

section Main

variable [Fintype ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V) {m : ℕ} (y : Fin m → V)
  (S Ω : Module.End ℂ V) (K : Finset ι) (c : ι → ι → ι → ℂ) (d o : Fin m → Fin m → ℂ)

def c0 : ℝ := 2 * ∑ i, ∑ κ ∈ K, ∑ n, ‖c κ i n‖

lemma weightConst_nonneg : 0 ≤ c0 K c := by
  unfold GlobalTheory.CompanionTheory.AnalyticWord.c0
  exact mul_nonneg zero_le_two
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)

lemma comm_term
    (hS : ∀ i, S * Z i - Z i * S = ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ))
    (p l : List ι) (i : ι) (e : Fin m) :
    ‖j (word Z p ((S * Z i - Z i * S) (word Z l (y e))))‖ ≤
      c0 K c * bnd j Z y (p.length + l.length + 2) := by
  have hw : ∀ a b : ι, ‖j (GlobalTheory.CompanionTheory.AnalyticWord.word Z p ((Z a * Z b) (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e))))‖ ≤
      GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (p.length + l.length + 2) := by
    intro a b
    have h := GlobalTheory.CompanionTheory.AnalyticWord.le_bnd j Z y (l := p ++ a :: b :: l)
      (k := p.length + l.length + 2)
      (by simp only [List.length_append, List.length_cons]; omega) e
    simpa only [GlobalTheory.CompanionTheory.AnalyticWord.word_append, GlobalTheory.CompanionTheory.AnalyticWord.word_cons, Module.End.mul_apply] using h
  have hB0 := GlobalTheory.CompanionTheory.AnalyticWord.bnd_nonneg j Z y (p.length + l.length + 2)
  rw [hS i]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, map_sum, map_smul, map_add]
  calc _ ≤ ∑ κ ∈ K, ∑ n, ‖c κ i n‖ * (2 * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (p.length + l.length + 2)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun κ _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_))
        rw [norm_smul, two_mul]
        exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hw κ n) (hw n κ)))
          (norm_nonneg _)
    _ = (∑ κ ∈ K, ∑ n, ‖c κ i n‖) * (2 * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (p.length + l.length + 2)) := by
        simp only [Finset.sum_mul]
    _ ≤ (∑ i', ∑ κ ∈ K, ∑ n, ‖c κ i' n‖) *
          (2 * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (p.length + l.length + 2)) :=
        mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := fun i' => ∑ κ ∈ K, ∑ n, ‖c κ i' n‖)
            (fun i' _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (Finset.mem_univ i))
          (mul_nonneg zero_le_two hB0)
    _ = GlobalTheory.CompanionTheory.AnalyticWord.c0 K c * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (p.length + l.length + 2) := by
        unfold GlobalTheory.CompanionTheory.AnalyticWord.c0
        ring

lemma comm_word
    (hS : ∀ i, S * Z i - Z i * S = ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ))
    (l : List ι) : ∀ (p : List ι) (e : Fin m),
    ‖j (word Z p ((S * word Z l - word Z l * S) (y e)))‖ ≤
      l.length * c0 K c * bnd j Z y (p.length + l.length + 1) := by
  induction l with
  | nil =>
    intro p e
    simp [GlobalTheory.CompanionTheory.AnalyticWord.word_nil]
  | cons i l ih =>
    intro p e
    have hsplit : S * GlobalTheory.CompanionTheory.AnalyticWord.word Z (i :: l) - GlobalTheory.CompanionTheory.AnalyticWord.word Z (i :: l) * S =
        (S * Z i - Z i * S) * GlobalTheory.CompanionTheory.AnalyticWord.word Z l +
          Z i * (S * GlobalTheory.CompanionTheory.AnalyticWord.word Z l - GlobalTheory.CompanionTheory.AnalyticWord.word Z l * S) := by
      rw [GlobalTheory.CompanionTheory.AnalyticWord.word_cons]
      simp only [mul_sub, sub_mul, mul_assoc]
      abel
    have h1 := GlobalTheory.CompanionTheory.AnalyticWord.comm_term j Z y S K c hS p l i e
    have h2 := ih (p ++ [i]) e
    have e2 : GlobalTheory.CompanionTheory.AnalyticWord.word Z (p ++ [i]) ((S * GlobalTheory.CompanionTheory.AnalyticWord.word Z l - GlobalTheory.CompanionTheory.AnalyticWord.word Z l * S) (y e)) =
        GlobalTheory.CompanionTheory.AnalyticWord.word Z p (Z i ((S * GlobalTheory.CompanionTheory.AnalyticWord.word Z l - GlobalTheory.CompanionTheory.AnalyticWord.word Z l * S) (y e))) := by
      rw [GlobalTheory.CompanionTheory.AnalyticWord.word_append, GlobalTheory.CompanionTheory.AnalyticWord.word_cons, GlobalTheory.CompanionTheory.AnalyticWord.word_nil, mul_one, Module.End.mul_apply]
    have hlen1 : p.length + l.length + 2 = p.length + (i :: l).length + 1 := by
      simp only [List.length_cons]; omega
    have hlen2 : (p ++ [i]).length + l.length + 1 = p.length + (i :: l).length + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [e2, hlen2] at h2
    rw [hlen1] at h1
    rw [hsplit, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, map_add, map_add]
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
    rw [List.length_cons, Nat.cast_succ]
    ring

def tot (a : Fin m → Fin m → ℂ) : ℝ := ∑ e, ∑ f, ‖a e f‖

lemma tot_nonneg (a : Fin m → Fin m → ℂ) : 0 ≤ tot a := by
  unfold GlobalTheory.CompanionTheory.AnalyticWord.tot
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma row_le_tot (a : Fin m → Fin m → ℂ) (e : Fin m) : ∑ f, ‖a e f‖ ≤ tot a := by
  unfold GlobalTheory.CompanionTheory.AnalyticWord.tot
  exact Finset.single_le_sum (f := fun e => ∑ f, ‖a e f‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ e)

lemma word_sq_le
    (hskew : ∀ i v w, inner ℂ (j (Z i v)) (j w) = - inner ℂ (j v) (j (Z i w)))
    (hT : ∑ i, Z i * Z i = Ω + S + S)
    (hS : ∀ i, S * Z i - Z i * S = ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ))
    (hΩ : ∀ i, Ω * Z i = Z i * Ω)
    (hSy : ∀ b, S (y b) = ∑ e, d b e • y e) (hOy : ∀ b, Ω (y b) = ∑ e, o b e • y e)
    (l : List ι) (i : ι) (e : Fin m) :
    ‖j (word Z (i :: l) (y e))‖ ^ 2 ≤ bnd j Z y l.length *
      ((tot o + 2 * tot d) * bnd j Z y l.length +
        2 * l.length * c0 K c * bnd j Z y (l.length + 1)) := by
  have hB0 := GlobalTheory.CompanionTheory.AnalyticWord.bnd_nonneg j Z y l.length
  have hv : ‖j (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e))‖ ≤ GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y l.length :=
    GlobalTheory.CompanionTheory.AnalyticWord.le_bnd j Z y (l := l) rfl e
  have hOmega : ‖j (Ω (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e)))‖ ≤
      GlobalTheory.CompanionTheory.AnalyticWord.tot o * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y l.length := by
    have h : Ω (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e)) = GlobalTheory.CompanionTheory.AnalyticWord.word Z l (∑ f, o e f • y f) := by
      rw [← hOy e]
      exact LinearMap.congr_fun (GlobalTheory.CompanionTheory.AnalyticWord.word_comm Z Ω hΩ l) (y e)
    rw [h]
    exact (GlobalTheory.CompanionTheory.AnalyticWord.comb_le j Z y (l := l) rfl (o e)).trans
      (mul_le_mul_of_nonneg_right (GlobalTheory.CompanionTheory.AnalyticWord.row_le_tot o e) hB0)
  have hSv : ‖j (S (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e)))‖ ≤
      GlobalTheory.CompanionTheory.AnalyticWord.tot d * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y l.length +
        l.length * GlobalTheory.CompanionTheory.AnalyticWord.c0 K c * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (l.length + 1) := by
    have hdec : S (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e)) = GlobalTheory.CompanionTheory.AnalyticWord.word Z l (∑ f, d e f • y f) +
        GlobalTheory.CompanionTheory.AnalyticWord.word Z [] ((S * GlobalTheory.CompanionTheory.AnalyticWord.word Z l - GlobalTheory.CompanionTheory.AnalyticWord.word Z l * S) (y e)) := by
      rw [GlobalTheory.CompanionTheory.AnalyticWord.word_nil, Module.End.one_apply, LinearMap.sub_apply, Module.End.mul_apply,
        Module.End.mul_apply, ← hSy e]
      abel
    have hc := GlobalTheory.CompanionTheory.AnalyticWord.comm_word j Z y S K c hS l [] e
    rw [List.length_nil, zero_add] at hc
    rw [hdec, map_add]
    exact (norm_add_le _ _).trans (add_le_add
      ((GlobalTheory.CompanionTheory.AnalyticWord.comb_le j Z y (l := l) rfl (d e)).trans
        (mul_le_mul_of_nonneg_right (GlobalTheory.CompanionTheory.AnalyticWord.row_le_tot d e) hB0)) hc)
  have hmain := GlobalTheory.CompanionTheory.AnalyticWord.sum_sq_le j Z hskew S Ω hT
    (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e)) i
  rw [GlobalTheory.CompanionTheory.AnalyticWord.word_cons, Module.End.mul_apply]
  have hnn : 0 ≤ ‖j (Ω (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e)))‖ + 2 * ‖j (S (GlobalTheory.CompanionTheory.AnalyticWord.word Z l (y e)))‖ := by
    positivity
  refine hmain.trans ((mul_le_mul hv (add_le_add hOmega (mul_le_mul_of_nonneg_left hSv zero_le_two))
    hnn hB0).trans (le_of_eq ?_))
  ring

lemma bnd_succ_le
    (hskew : ∀ i v w, inner ℂ (j (Z i v)) (j w) = - inner ℂ (j v) (j (Z i w)))
    (hT : ∑ i, Z i * Z i = Ω + S + S)
    (hS : ∀ i, S * Z i - Z i * S = ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ))
    (hΩ : ∀ i, Ω * Z i = Z i * Ω)
    (hSy : ∀ b, S (y b) = ∑ e, d b e • y e) (hOy : ∀ b, Ω (y b) = ∑ e, o b e • y e) (n : ℕ) :
    bnd j Z y (n + 1) ≤ (√(tot o + 2 * tot d) + 2 * n * c0 K c) * bnd j Z y n := by
  have hA : 0 ≤ GlobalTheory.CompanionTheory.AnalyticWord.tot o + 2 * GlobalTheory.CompanionTheory.AnalyticWord.tot d :=
    add_nonneg (GlobalTheory.CompanionTheory.AnalyticWord.tot_nonneg o) (mul_nonneg zero_le_two (GlobalTheory.CompanionTheory.AnalyticWord.tot_nonneg d))
  have hC : 0 ≤ 2 * (n : ℝ) * GlobalTheory.CompanionTheory.AnalyticWord.c0 K c :=
    mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg n)) (GlobalTheory.CompanionTheory.AnalyticWord.weightConst_nonneg K c)
  have hBn := GlobalTheory.CompanionTheory.AnalyticWord.bnd_nonneg j Z y n
  have hBn1 := GlobalTheory.CompanionTheory.AnalyticWord.bnd_nonneg j Z y (n + 1)
  have hR0 : 0 ≤ GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y n *
      ((GlobalTheory.CompanionTheory.AnalyticWord.tot o + 2 * GlobalTheory.CompanionTheory.AnalyticWord.tot d) * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y n +
        2 * n * GlobalTheory.CompanionTheory.AnalyticWord.c0 K c * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (n + 1)) :=
    mul_nonneg hBn (add_nonneg (mul_nonneg hA hBn) (mul_nonneg hC hBn1))
  have hbound : GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (n + 1) ≤ √(GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y n *
      ((GlobalTheory.CompanionTheory.AnalyticWord.tot o + 2 * GlobalTheory.CompanionTheory.AnalyticWord.tot d) * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y n +
        2 * n * GlobalTheory.CompanionTheory.AnalyticWord.c0 K c * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (n + 1))) := by
    refine GlobalTheory.CompanionTheory.AnalyticWord.bnd_le j Z y (Real.sqrt_nonneg _) fun l e hl => ?_
    cases l with
    | nil => simp at hl
    | cons i l' =>
      have hl' : l'.length = n := by simpa using hl
      have h := GlobalTheory.CompanionTheory.AnalyticWord.word_sq_le j Z y S Ω K c d o hskew hT hS hΩ hSy hOy l' i e
      rw [hl'] at h
      exact (le_abs_self _).trans (Real.abs_le_sqrt h)
  have hsq : GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (n + 1) ^ 2 ≤ GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y n *
      ((GlobalTheory.CompanionTheory.AnalyticWord.tot o + 2 * GlobalTheory.CompanionTheory.AnalyticWord.tot d) * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y n +
        2 * n * GlobalTheory.CompanionTheory.AnalyticWord.c0 K c * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y (n + 1)) :=
    (pow_le_pow_left₀ hBn1 hbound 2).trans_eq (Real.sq_sqrt hR0)
  exact GlobalTheory.CompanionTheory.AnalyticWord.quad_step hBn1 hBn hA hC hsq

lemma bnd_fact
    (hskew : ∀ i v w, inner ℂ (j (Z i v)) (j w) = - inner ℂ (j v) (j (Z i w)))
    (hT : ∑ i, Z i * Z i = Ω + S + S)
    (hS : ∀ i, S * Z i - Z i * S = ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ))
    (hΩ : ∀ i, Ω * Z i = Z i * Ω)
    (hSy : ∀ b, S (y b) = ∑ e, d b e • y e) (hOy : ∀ b, Ω (y b) = ∑ e, o b e • y e) (k : ℕ) :
    bnd j Z y k ≤ (√(tot o + 2 * tot d) + 2 * c0 K c + 1) ^ k * (k.factorial : ℝ) *
      bnd j Z y 0 := by
  have step : ∀ a s b0 bk b1 P F r : ℝ, 0 ≤ a → 0 ≤ s → 0 ≤ b0 → 0 ≤ P → 0 ≤ F → 0 ≤ r →
      b1 ≤ (a + 2 * r * s) * bk → bk ≤ P * F * b0 →
      b1 ≤ P * (a + 2 * s + 1) * ((r + 1) * F) * b0 := by
    intro a s b0 bk b1 P F r ha hs hb0 hP hF hr h1 h2
    have hX : 0 ≤ P * F * b0 := mul_nonneg (mul_nonneg hP hF) hb0
    have hc : 0 ≤ a + 2 * r * s := add_nonneg ha (mul_nonneg (mul_nonneg zero_le_two hr) hs)
    calc b1 ≤ (a + 2 * r * s) * bk := h1
      _ ≤ (a + 2 * r * s) * (P * F * b0) := mul_le_mul_of_nonneg_left h2 hc
      _ ≤ ((a + 2 * s + 1) * (r + 1)) * (P * F * b0) :=
          mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg ha hr]) hX
      _ = P * (a + 2 * s + 1) * ((r + 1) * F) * b0 := by ring
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := GlobalTheory.CompanionTheory.AnalyticWord.bnd_succ_le j Z y S Ω K c d o hskew hT hS hΩ hSy hOy k
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    exact step _ _ _ _ _ _ _ _ (Real.sqrt_nonneg _) (GlobalTheory.CompanionTheory.AnalyticWord.weightConst_nonneg K c)
      (GlobalTheory.CompanionTheory.AnalyticWord.bnd_nonneg j Z y 0)
      (pow_nonneg (add_nonneg (add_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg zero_le_two (GlobalTheory.CompanionTheory.AnalyticWord.weightConst_nonneg K c))) zero_le_one) k)
      (Nat.cast_nonneg _) (Nat.cast_nonneg k) hs ih

lemma pow_bound (x : ι → ℂ) (k : ℕ) : ∀ (p : List ι) (e : Fin m),
    ‖j (word Z p (((∑ i, x i • Z i) ^ k) (y e)))‖ ≤
      (∑ i, ‖x i‖) ^ k * bnd j Z y (p.length + k) := by
  induction k with
  | zero =>
    intro p e
    simp only [pow_zero, Module.End.one_apply, one_mul]
    exact GlobalTheory.CompanionTheory.AnalyticWord.le_bnd j Z y (l := p) rfl e
  | succ k ih =>
    intro p e
    have hexp : GlobalTheory.CompanionTheory.AnalyticWord.word Z p (((∑ i, x i • Z i) ^ (k + 1)) (y e)) =
        ∑ i, x i • GlobalTheory.CompanionTheory.AnalyticWord.word Z (p ++ [i]) (((∑ i, x i • Z i) ^ k) (y e)) := by
      rw [pow_succ', Module.End.mul_apply, LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, map_smul, GlobalTheory.CompanionTheory.AnalyticWord.word_append, GlobalTheory.CompanionTheory.AnalyticWord.word_cons, GlobalTheory.CompanionTheory.AnalyticWord.word_nil,
        mul_one, Module.End.mul_apply]
    rw [hexp, map_sum]
    refine (norm_sum_le _ _).trans ?_
    rw [pow_succ', mul_assoc, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_smul, norm_smul]
    have h := ih (p ++ [i]) e
    have hlen : (p ++ [i]).length + k = p.length + (k + 1) := by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega
    rw [hlen] at h
    exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

end Main

theorem analytic_bound : ∀ (V H : Type) [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (j : V →ₗ[ℂ] H) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Z : ι → Module.End ℂ V) (K : Finset ι) (m : ℕ) (y : Fin m → V) (d o : Fin m → Fin m → ℂ)
    (c : ι → ι → ι → ℂ),
    (∀ i v w, inner ℂ (j (Z i v)) (j w) = - inner ℂ (j v) (j (Z i w))) →
    (∀ κ i, Z κ * Z i - Z i * Z κ = ∑ l, c κ i l • Z l) →
    (∀ i, (∑ i ∈ Kᶜ, Z i * Z i - ∑ κ ∈ K, Z κ * Z κ) * Z i =
      Z i * (∑ i ∈ Kᶜ, Z i * Z i - ∑ κ ∈ K, Z κ * Z κ)) →
    (∀ b, (∑ κ ∈ K, Z κ * Z κ) (y b) = ∑ e, d b e • y e) →
    (∀ b, (∑ i ∈ Kᶜ, Z i * Z i - ∑ κ ∈ K, Z κ * Z κ) (y b) = ∑ e, o b e • y e) →
    ∀ (x : ι → ℂ), ∀ v ∈ Submodule.span ℂ (Set.range y), ∃ M C : ℝ, ∀ k : ℕ,
      ‖j (((∑ i, x i • Z i) ^ k) v)‖ ≤ M * C ^ k * (k.factorial : ℝ) := by
  intro V H _ _ _ _ j ι _ _ Z K m y d o c hskew hcomm hΩ hd ho x v hv
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
  have hT : ∑ i, Z i * Z i = (∑ i ∈ Kᶜ, Z i * Z i - ∑ κ ∈ K, Z κ * Z κ) +
      ∑ κ ∈ K, Z κ * Z κ + ∑ κ ∈ K, Z κ * Z κ := by
    rw [← Finset.sum_add_sum_compl K (fun i => Z i * Z i)]
    abel
  have hS : ∀ i, (∑ κ ∈ K, Z κ * Z κ) * Z i - Z i * (∑ κ ∈ K, Z κ * Z κ) =
      ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ) :=
    GlobalTheory.CompanionTheory.AnalyticWord.comm_S Z K c hcomm
  have hB := fun k => GlobalTheory.CompanionTheory.AnalyticWord.bnd_fact j Z y (∑ κ ∈ K, Z κ * Z κ)
    (∑ i ∈ Kᶜ, Z i * Z i - ∑ κ ∈ K, Z κ * Z κ) K c d o hskew hT hS hΩ hd ho k
  refine ⟨(∑ f, ‖a f‖) * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y 0,
    (∑ i, ‖x i‖) * (√(GlobalTheory.CompanionTheory.AnalyticWord.tot o + 2 * GlobalTheory.CompanionTheory.AnalyticWord.tot d) +
      2 * GlobalTheory.CompanionTheory.AnalyticWord.c0 K c + 1), fun k => ?_⟩
  have hf : ∀ f, ‖a f • j (((∑ i, x i • Z i) ^ k) (y f))‖ ≤
      ‖a f‖ * ((∑ i, ‖x i‖) ^ k * GlobalTheory.CompanionTheory.AnalyticWord.bnd j Z y k) := by
    intro f
    have h := GlobalTheory.CompanionTheory.AnalyticWord.pow_bound j Z y x k [] f
    rw [GlobalTheory.CompanionTheory.AnalyticWord.word_nil, Module.End.one_apply, List.length_nil, zero_add] at h
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
  simp only [map_sum, map_smul]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun f _ => hf f).trans ?_)
  rw [← Finset.sum_mul, mul_pow]
  have hsa : 0 ≤ ∑ f, ‖a f‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsx : 0 ≤ (∑ i, ‖x i‖) ^ k := pow_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) k
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB k) hsx) hsa).trans (le_of_eq ?_)
  ring

end GlobalTheory.CompanionTheory.AnalyticWord
