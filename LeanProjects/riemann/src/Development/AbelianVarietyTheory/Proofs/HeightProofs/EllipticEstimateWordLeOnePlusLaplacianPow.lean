import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.InvSqrtTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermitianJmBracket

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.Elliptic

section Abstract

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type} [Fintype ι]

open Classical in

def words (D : ι → Module.End ℂ V) (m : ℕ) : Finset (Module.End ℂ V) :=
  Nat.rec {1} (fun _ W => W ∪ Finset.univ.biUnion fun i => W.image (D i * ·)) m

def filt (D : ι → Module.End ℂ V) (m : ℕ) : Submodule ℂ (Module.End ℂ V) := Submodule.span ℂ (words D m : Set _)

def wordNorm (D : ι → Module.End ℂ V) (m : ℕ) (v : V) : ℝ := ∑ T ∈ words D m, ‖T v‖

def lap (D : ι → Module.End ℂ V) : Module.End ℂ V := 1 - ∑ i, D i * D i

variable {D : ι → Module.End ℂ V}

theorem mem_words_succ {m : ℕ} {T : Module.End ℂ V} :
    T ∈ words D (m + 1) ↔ T ∈ words D m ∨ ∃ i, ∃ T' ∈ words D m, D i * T' = T := by
  simp [words]

theorem filt_le (m : ℕ) : filt D m ≤ filt D (m + 1) :=
  Submodule.span_mono fun _ h => mem_words_succ.2 (Or.inl h)

theorem mul_mem_filt {m : ℕ} {S T : Module.End ℂ V} (hS : S ∈ Submodule.span ℂ (Set.range D)) (hT : T ∈ filt D m) :
    S * T ∈ filt D (m + 1) := by
  induction hS using Submodule.span_induction with
  | mem S hS =>
    obtain ⟨i, rfl⟩ := hS
    induction hT using Submodule.span_induction with
    | mem T hT => exact Submodule.subset_span (mem_words_succ.2 (Or.inr ⟨i, T, hT, rfl⟩))
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem comm_mem_filt (hbr : ∀ i j, D i * D j - D j * D i ∈ Submodule.span ℂ (Set.range D)) (i : ι) (m : ℕ) :
    ∀ T ∈ filt D m, D i * T - T * D i ∈ filt D m := by
  have ext : ∀ m, (∀ T ∈ words D m, D i * T - T * D i ∈ filt D m) → ∀ T ∈ filt D m, D i * T - T * D i ∈ filt D m := by
    intro m h T hT
    induction hT using Submodule.span_induction with
    | mem T hT => exact h T hT
    | zero => simp
    | add x y _ _ hx hy =>
      have : D i * (x + y) - (x + y) * D i = (D i * x - x * D i) + (D i * y - y * D i) := by noncomm_ring
      rw [this]; exact add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]; exact Submodule.smul_mem _ c hx
  induction m with
  | zero => exact ext 0 fun T hT => by simp [words] at hT; simp [hT]
  | succ m ih =>
    refine ext _ fun T hT => ?_
    rcases mem_words_succ.1 hT with h | ⟨j, T', h, rfl⟩
    · exact filt_le m (ih T (Submodule.subset_span h))
    · have : D i * (D j * T') - D j * T' * D i = (D i * D j - D j * D i) * T' + D j * (D i * T' - T' * D i) := by
        noncomm_ring
      rw [this]
      exact add_mem (mul_mem_filt (hbr i j) (Submodule.subset_span h))
        (mul_mem_filt (Submodule.subset_span ⟨j, rfl⟩) (ih T' (Submodule.subset_span h)))

theorem lap_comm_mem_filt (hbr : ∀ i j, D i * D j - D j * D i ∈ Submodule.span ℂ (Set.range D)) {m : ℕ}
    {T : Module.End ℂ V} (hT : T ∈ filt D m) : lap D * T - T * lap D ∈ filt D (m + 1) := by
  have : lap D * T - T * lap D = -∑ i, (D i * D i * T - T * (D i * D i)) := by
    simp only [lap, sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib, one_mul, mul_one]
    abel
  rw [this]
  refine neg_mem (Submodule.sum_mem _ fun i _ => ?_)
  have h1 := comm_mem_filt hbr i m T hT
  have h2 := mul_mem_filt (Submodule.subset_span ⟨i, rfl⟩) h1
  have h3 := filt_le m (comm_mem_filt hbr i m _ h1)
  have : D i * D i * T - T * (D i * D i) = D i * (D i * T - T * D i) + (D i * (D i * T - T * D i) -
    (D i * (D i * T - T * D i) - (D i * T - T * D i) * D i)) := by noncomm_ring
  rw [this]
  exact add_mem h2 (sub_mem h2 h3)

theorem wordNorm_nonneg (m : ℕ) (v : V) : 0 ≤ wordNorm D m v := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem le_wordNorm {m : ℕ} {T : Module.End ℂ V} (hT : T ∈ words D m) (v : V) : ‖T v‖ ≤ wordNorm D m v :=
  Finset.single_le_sum (f := fun T : Module.End ℂ V => ‖T v‖) (fun _ _ => norm_nonneg _) hT

theorem exists_le_wordNorm {m : ℕ} {T : Module.End ℂ V} (hT : T ∈ filt D m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖T v‖ ≤ C * wordNorm D m v := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact ⟨1, zero_le_one, fun v => by simpa using le_wordNorm hT v⟩
  | zero => exact ⟨0, le_rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a + b, add_nonneg ha hb, fun v => ?_⟩
    rw [LinearMap.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hx v) (hy v))
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    refine ⟨‖c‖ * a, by positivity, fun v => ?_⟩
    rw [LinearMap.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hx v) (norm_nonneg _)

theorem energy_le (hsk : ∀ i x y, ⟪x, D i y⟫_ℂ = -⟪D i x, y⟫_ℂ) (u : V) :
    ‖u‖ ^ 2 + ∑ i, ‖D i u‖ ^ 2 ≤ ‖u‖ * ‖lap D u‖ := by
  have h : ⟪u, lap D u⟫_ℂ = ((‖u‖ ^ 2 + ∑ i, ‖D i u‖ ^ 2 : ℝ) : ℂ) := by
    simp only [lap, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply, Module.End.mul_apply,
      inner_sub_right, inner_sum, hsk _ u, inner_self_eq_norm_sq_to_K, Finset.sum_neg_distrib, sub_neg_eq_add]
    push_cast; rfl
  have h2 := norm_inner_le_norm (𝕜 := ℂ) u (lap D u)
  rw [h, Complex.norm_real] at h2
  exact (le_abs_self _).trans h2

theorem norm_le_lap (hsk : ∀ i x y, ⟪x, D i y⟫_ℂ = -⟪D i x, y⟫_ℂ) (u : V) : ‖u‖ ≤ ‖lap D u‖ := by
  have h := energy_le hsk u
  have h0 : 0 ≤ ∑ i, ‖D i u‖ ^ 2 := by positivity
  rcases (norm_nonneg u).eq_or_lt with h1 | h1
  · rw [← h1]; exact norm_nonneg _
  · nlinarith

theorem sq_le_lap (hsk : ∀ i x y, ⟪x, D i y⟫_ℂ = -⟪D i x, y⟫_ℂ) (i : ι) (u : V) :
    ‖D i u‖ ^ 2 ≤ ‖u‖ * ‖lap D u‖ := by
  have h := energy_le hsk u
  have h0 : ‖D i u‖ ^ 2 ≤ ∑ i, ‖D i u‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖D i u‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  nlinarith [sq_nonneg ‖u‖]

theorem wordNorm_le (hsk : ∀ i x y, ⟪x, D i y⟫_ℂ = -⟪D i x, y⟫_ℂ)
    (hbr : ∀ i j, D i * D j - D j * D i ∈ Submodule.span ℂ (Set.range D)) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, wordNorm D m v ≤ C * ‖(lap D ^ m) v‖ := by
  induction m with
  | zero => exact ⟨1, zero_le_one, fun v => by simp [wordNorm, words]⟩
  | succ m ih =>
    obtain ⟨C, hC, ih⟩ := ih
    have h1 : ∀ v, wordNorm D m v ≤ C * ‖(lap D ^ (m + 1)) v‖ := fun v =>
      (ih v).trans (mul_le_mul_of_nonneg_left (by rw [pow_succ']; exact norm_le_lap hsk _) hC)
    have h2 : ∀ v, wordNorm D m (lap D v) ≤ C * ‖(lap D ^ (m + 1)) v‖ := fun v => by
      rw [pow_succ]; exact ih _
    have key : ∀ δ : ℝ, 0 < δ → ∀ T ∈ words D (m + 1), ∃ K : ℝ, 0 ≤ K ∧
        ∀ v, ‖T v‖ ≤ δ * wordNorm D (m + 1) v + K * ‖(lap D ^ (m + 1)) v‖ := by
      intro δ hδ T hT
      rcases mem_words_succ.1 hT with h | ⟨j, T', h, rfl⟩
      · refine ⟨C, hC, fun v => ((le_wordNorm h v).trans (h1 v)).trans (le_add_of_nonneg_left ?_)⟩
        exact mul_nonneg hδ.le (wordNorm_nonneg _ _)
      · obtain ⟨C', hC', h3⟩ := exists_le_wordNorm (lap_comm_mem_filt hbr (Submodule.subset_span h))
        refine ⟨C + C * C' / δ, by positivity, fun v => ?_⟩
        have e1 := sq_le_lap hsk j (T' v)
        have e2 := (le_wordNorm h v).trans (h1 v)
        have e3 := (le_wordNorm h (lap D v)).trans (h2 v)
        have e4 : ‖lap D (T' v)‖ ≤ C * ‖(lap D ^ (m + 1)) v‖ + C' * wordNorm D (m + 1) v := by
          have : lap D (T' v) = T' (lap D v) + (lap D * T' - T' * lap D) v := by simp
          rw [this]
          exact (norm_add_le _ _).trans (add_le_add e3 (h3 v))
        have hN := wordNorm_nonneg (D := D) (m + 1) v
        have ha := norm_nonneg ((lap D ^ (m + 1)) v)
        generalize wordNorm D (m + 1) v = N at *
        generalize ‖(lap D ^ (m + 1)) v‖ = a at *
        have e5 : ‖D j (T' v)‖ ^ 2 ≤ (C * a) * (C * a + C' * N) :=
          e1.trans (mul_le_mul e2 e4 (norm_nonneg _) (by positivity))
        have hq : 0 ≤ C * C' / δ := by positivity
        have hq' : C * C' / δ * δ = C * C' := div_mul_cancel₀ _ hδ.ne'
        generalize C * C' / δ = q at *
        refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (e5.trans ?_)
        have : (δ * N + (C + q) * a) ^ 2 = (C * a) * (C * a + C' * N) +
          ((δ * N) ^ 2 + 2 * δ * N * C * a + δ * N * q * a + 2 * C * q * a ^ 2 + (q * a) ^ 2) := by
          linear_combination (N * a) * hq'
        rw [this]
        exact le_add_of_nonneg_right (by positivity)
    set c : ℝ := ((words D (m + 1)).card : ℝ) with hc
    have hc0 : 0 ≤ c := by positivity
    choose! K hK0 hK using key (1 / (2 * (c + 1))) (by positivity)
    refine ⟨2 * ∑ T ∈ words D (m + 1), K T, mul_nonneg zero_le_two (Finset.sum_nonneg hK0), fun v => ?_⟩
    have h4 : wordNorm D (m + 1) v ≤ c * (1 / (2 * (c + 1)) * wordNorm D (m + 1) v) +
        (∑ T ∈ words D (m + 1), K T) * ‖(lap D ^ (m + 1)) v‖ := by
      refine (Finset.sum_le_sum fun T hT => hK T hT v).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_mul]
    have h5 : c * (1 / (2 * (c + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
    have := mul_le_mul_of_nonneg_right h5 (wordNorm_nonneg (D := D) (m + 1) v)
    nlinarith

theorem exists_le_of_mem_filt (hsk : ∀ i x y, ⟪x, D i y⟫_ℂ = -⟪D i x, y⟫_ℂ)
    (hbr : ∀ i j, D i * D j - D j * D i ∈ Submodule.span ℂ (Set.range D)) {m : ℕ} {T : Module.End ℂ V}
    (hT : T ∈ filt D m) : ∃ C : ℝ, ∀ v, ‖T v‖ ≤ C * ‖(lap D ^ m) v‖ := by
  obtain ⟨a, ha, h1⟩ := exists_le_wordNorm hT
  obtain ⟨b, -, h2⟩ := wordNorm_le hsk hbr m
  exact ⟨a * b, fun v => (h1 v).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (h2 v) ha)⟩

end Abstract

variable {n : ℕ}

theorem mem_pairs {ε : Fin n → Bool} {s : Bool} {p : Fin n × Fin n} :
    p ∈ pairs ε s ↔ p.1 < p.2 ∧ (ε p.1 == ε p.2) = s := by
  obtain ⟨a, b⟩ := p
  simp [pairs, List.mem_product]

theorem mem_lie_iff {ε : Fin n → Bool} {X : Mx n} : X ∈ lieSet ε ↔
    ∀ a b, star (X b a) * (if ε b then 1 else -1) + (if ε a then 1 else -1) * X a b = 0 := by
  show Xᴴ * Jm ε + Jm ε * X = 0 ↔ _
  rw [← Matrix.ext_iff]
  simp [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem basis_mem (ε : Fin n → Bool) : ∀ Z ∈ kList ε ++ pList ε, Z ∈ lieSet ε := by
  intro Z hZ
  rw [mem_lie_iff]
  intro a b
  simp only [kList, pList, List.mem_append, List.mem_map, List.mem_flatMap, mem_pairs, List.mem_cons,
    List.not_mem_nil, or_false] at hZ
  rcases hZ with (⟨c, -, rfl⟩ | ⟨⟨c, d⟩, ⟨h1, h2⟩, rfl | rfl⟩) | ⟨⟨c, d⟩, ⟨h1, h2⟩, rfl | rfl⟩
  · by_cases h : c = a ∧ c = b
    · obtain ⟨rfl, rfl⟩ := h
      cases hc : ε c <;> simp
    · have h' : ¬ (c = b ∧ c = a) := fun k => h k.symm
      simp [Matrix.single_apply, h, h']
  all_goals
    have h3 : c ≠ d := h1.ne
    simp only [beq_iff_eq, beq_eq_false_iff_ne] at h2
    by_cases e1 : c = a ∧ d = b
    · obtain ⟨rfl, rfl⟩ := e1
      cases hc : ε c <;> cases hd : ε d <;> simp_all [Matrix.single_apply, h3, h3.symm]
    · by_cases e2 : d = a ∧ c = b
      · obtain ⟨rfl, rfl⟩ := e2
        cases hc : ε c <;> cases hd : ε d <;> simp_all [Matrix.single_apply, h3, h3.symm]
      · have e3 : ¬ (d = b ∧ c = a) := fun h => e1 h.symm
        have e4 : ¬ (c = b ∧ d = a) := fun h => e2 h.symm
        simp [Matrix.single_apply, e1, e2, e3, e4]

theorem mem_span_basis (ε : Fin n → Bool) {X : Mx n} (hX : X ∈ lieSet ε) :
    X ∈ Submodule.span ℝ {Z | Z ∈ kList ε ++ pList ε} := by
  rw [mem_lie_iff] at hX
  set S := Submodule.span ℝ {Z | Z ∈ kList ε ++ pList ε} with hS
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by simp
  have lt : ∀ a b, a < b → Matrix.single a b (X a b) + Matrix.single b a (X b a) ∈ S := by
    intro a b hab
    have h := hX b a
    have hne := hab.ne
    by_cases e : ε a = ε b
    · have m1 : invSqrtTwo • (unitE a b - unitE b a) ∈ S := Submodule.subset_span (by
        simp only [kList, Set.mem_setOf_eq, List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inr ⟨(a, b), mem_pairs.2 ⟨hab, by simp [e]⟩, by simp⟩))
      have m2 : (invSqrtTwo * Complex.I) • (unitE a b + unitE b a) ∈ S := Submodule.subset_span (by
        simp only [kList, Set.mem_setOf_eq, List.mem_append, List.mem_flatMap]
        exact Or.inl (Or.inr ⟨(a, b), mem_pairs.2 ⟨hab, by simp [e]⟩, by simp⟩))
      have h' : X b a = -star (X a b) := by
        rw [e] at h
        cases hb : ε b <;> simp only [hb] at h <;> simp at h ⊢
        exacts [by linear_combination -h, by linear_combination h]
      convert add_mem (S.smul_mem (√2 * (X a b).re) m1) (S.smul_mem (√2 * (X a b).im) m2) using 1
      rw [h', ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul]
      push_cast
      rw [mul_right_comm, mul_inv_cancel₀ hs, ← mul_assoc, mul_right_comm _ _ invSqrtTwo, mul_inv_cancel₀ hs]
      simp only [smul_sub, smul_add, Matrix.smul_single, one_mul, smul_eq_mul, mul_one]
      rw [sub_eq_add_neg, Matrix.single_neg, add_add_add_comm, ← Matrix.single_add, ← Matrix.single_add]
      congr 2 <;> apply Complex.ext <;> simp
    · have e' : (ε a == ε b) = false := by simpa using e
      have m1 : invSqrtTwo • (unitE a b + unitE b a) ∈ S := Submodule.subset_span (by
        simp only [pList, Set.mem_setOf_eq, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨(a, b), mem_pairs.2 ⟨hab, e'⟩, by simp⟩)
      have m2 : (invSqrtTwo * Complex.I) • (unitE a b - unitE b a) ∈ S := Submodule.subset_span (by
        simp only [pList, Set.mem_setOf_eq, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨(a, b), mem_pairs.2 ⟨hab, e'⟩, by simp⟩)
      have h' : X b a = star (X a b) := by
        cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb] at h e <;> simp at h e ⊢
        exacts [by linear_combination h, by linear_combination -h]
      convert add_mem (S.smul_mem (√2 * (X a b).re) m1) (S.smul_mem (√2 * (X a b).im) m2) using 1
      rw [h', ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul]
      push_cast
      rw [mul_right_comm, mul_inv_cancel₀ hs, ← mul_assoc, mul_right_comm _ _ invSqrtTwo, mul_inv_cancel₀ hs]
      simp only [smul_sub, smul_add, Matrix.smul_single, one_mul, smul_eq_mul, mul_one]
      rw [sub_eq_add_neg, Matrix.single_neg, add_add_add_comm, ← Matrix.single_add, ← Matrix.single_add]
      congr 2 <;> apply Complex.ext <;> simp
  have dg : ∀ a, Matrix.single a a (X a a) ∈ S := by
    intro a
    have m1 : Complex.I • unitE a a ∈ S := Submodule.subset_span (by
      simp only [kList, Set.mem_setOf_eq, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl ⟨a, by simp, rfl⟩))
    have h : (X a a).re = 0 := by
      have := congrArg Complex.re (hX a a)
      cases hb : ε a <;> simp [hb] at this <;> linarith
    convert S.smul_mem (X a a).im m1 using 1
    rw [← Complex.coe_smul, smul_smul, Matrix.smul_single]
    congr 1
    apply Complex.ext <;> simp [h]
  have all : ∀ a b, Matrix.single a b (X a b) + Matrix.single b a (X b a) ∈ S := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · exact lt a b h
    · exact add_mem (dg a) (dg a)
    · rw [add_comm]; exact lt b a h
  have e : X = (1 / 2 : ℝ) • ∑ a, ∑ b, (Matrix.single a b (X a b) + Matrix.single b a (X b a)) := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun a b => Matrix.single b a (X b a)), ← Matrix.matrix_eq_sum_single, ← two_smul ℝ,
      smul_smul]
    simp
  rw [e]
  exact S.smul_mem _ (S.sum_mem fun a _ => S.sum_mem fun b _ => all a b)

theorem word_le_lapOne : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∃ (s : ℕ) (C : ℝ), ∀ v, Sm ε σ v → ‖Dw σ l v‖ ≤ C * ‖(lapOne ε σ)^[s] v‖ := by
  intro n ε H _ _ _ σ h l hl
  set L := kList ε ++ pList ε with hL
  have hB : ∀ i, L.get i ∈ lieSet ε := fun i => basis_mem ε _ (List.get_mem _ _)
  let D : Fin L.length → Module.End ℂ (smooth (Jm ε) σ) := fun i => dOp (isUnit_Jm ε) h.1 (hB i)
  have hsp : ∀ X (hX : X ∈ lieSet ε), dOp (isUnit_Jm ε) h.1 hX ∈ Submodule.span ℂ (Set.range D) := by
    intro X hX
    have h1 := mem_span_basis ε hX
    rw [← hL, ← Set.range_list_get] at h1
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 h1
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨fun i => c i, LinearMap.ext fun w => Subtype.ext ?_⟩
    rw [LinearMap.sum_apply, Submodule.coe_sum]
    exact (h.dRep_sum hB w.2 c).symm
  have hsk : ∀ i x y, ⟪x, D i y⟫_ℂ = -⟪D i x, y⟫_ℂ := fun i x y =>
    inner_dRep (isUnit_Jm ε) h.1 x.2 y.2 (hB i)
  have hbr : ∀ i j, D i * D j - D j * D i ∈ Submodule.span ℂ (Set.range D) := by
    intro i j
    have hX := hB i
    have hY := hB j
    have hm : L.get i * L.get j - L.get j * L.get i ∈ lieSet ε := by
      generalize L.get i = X at *
      generalize L.get j = Y at *
      have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
      have h2 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
      show (X * Y - Y * X)ᴴ * Jm ε + Jm ε * (X * Y - Y * X) = 0
      rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, sub_mul, mul_assoc, mul_assoc, h1, h2,
        mul_neg, mul_neg, ← mul_assoc, ← mul_assoc, h1, h2]
      noncomm_ring
    convert hsp _ hm using 1
    exact LinearMap.ext fun w => Subtype.ext (dRep_bracket n ε H σ h w w.2 _ hX _ hY)
  have hw : ∃ T ∈ filt D l.length, ∀ w : smooth (Jm ε) σ, (T w : H) = Dw σ l w := by
    induction l with
    | nil => exact ⟨1, Submodule.subset_span (by simp [words]), fun _ => rfl⟩
    | cons X l ih =>
      obtain ⟨T, hT, e⟩ := ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
      exact ⟨_, mul_mem_filt (hsp X (hl X List.mem_cons_self)) hT, fun w => by
        rw [Dw, List.foldr_cons, ← Dw, ← e]; rfl⟩
  have hA : ∀ w : smooth (Jm ε) σ, (lap D w : H) = lapOne ε σ w := by
    intro w
    have e : ∀ M : List (Mx n), ∑ i, dRep σ (M.get i) (dRep σ (M.get i) w) =
        (M.map fun Z => dRep σ Z (dRep σ Z w)).sum := fun M =>
      Fin.sum_univ_fun_getElem M fun Z => dRep σ Z (dRep σ Z w)
    simp only [lap, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply, Submodule.coe_sub,
      Submodule.coe_sum, lapOne, onePlusCas, kB, pB, e, sub_sub]
    rw [← List.sum_append, ← List.map_append, ← hL, ← e]
    rfl
  have hAs : ∀ (s : ℕ) (w : smooth (Jm ε) σ), ((lap D ^ s) w : H) = (lapOne ε σ)^[s] w := by
    intro s
    induction s with
    | zero => intro w; rfl
    | succ s ih => intro w; rw [pow_succ', Module.End.mul_apply, hA, ih, Function.iterate_succ_apply']
  obtain ⟨T, hT, e⟩ := hw
  obtain ⟨C, hC⟩ := exists_le_of_mem_filt hsk hbr hT
  refine ⟨l.length, C, fun v hv => ?_⟩
  have := hC ⟨v, hv⟩
  rwa [Submodule.coe_norm, Submodule.coe_norm, e, hAs] at this

end GlobalTheory.TypeSum.Elliptic

end
