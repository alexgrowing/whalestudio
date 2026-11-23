import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding

open Finset CompanionTheory.RgExh

namespace GlobalTheory.CompanionTheory.RgPath

variable {n : ℕ}

theorem exists_pos_lower {ι : Type*} [Finite ι] (g : ι → ℝ) :
    ∃ e : ℝ, 0 < e ∧ ∀ i, 0 < g i → e ≤ g i := by
  classical
  cases nonempty_fintype ι
  by_cases hS : (Finset.univ.filter fun i => 0 < g i).Nonempty
  · obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _ g hS
    exact ⟨g i, (Finset.mem_filter.1 hi).2,
      fun j hj => hmin j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)⟩
  · exact ⟨1, one_pos, fun j hj => (hS ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩⟩).elim⟩

theorem exists_sorted (f : Fin n → ℝ) (hf : Function.Injective f) :
    ∃ l : List (Fin n), l.Pairwise (fun a b => f b < f a) ∧ ∀ a, a ∈ l := by
  classical
  have key : ∀ S : Finset (Fin n), ∃ l : List (Fin n),
      l.Pairwise (fun a b => f b < f a) ∧ ∀ a, a ∈ l ↔ a ∈ S := by
    intro S
    induction S using Finset.induction_on_max_value f with
    | empty => exact ⟨[], List.Pairwise.nil, by simp⟩
    | insert a s ha hmax ih =>
      obtain ⟨l, hl, hm⟩ := ih
      refine ⟨a :: l, List.pairwise_cons.2 ⟨fun b hb => ?_, hl⟩, fun b => by simp [hm]⟩
      have hbs := (hm b).1 hb
      refine lt_of_le_of_ne (hmax b hbs) fun h => ha ?_
      rwa [← hf h]
  obtain ⟨l, hl, hm⟩ := key Finset.univ
  exact ⟨l, hl, fun a => (hm a).2 (Finset.mem_univ a)⟩

theorem pathEnd_append (χ : Fin n → ℂ) (l l' : List (Fin n)) :
    pathEnd χ (l ++ l') = pathEnd (pathEnd χ l) l' := by
  induction l generalizing χ with
  | nil => rfl
  | cons s l ih => exact ih _

theorem goodPath_append (χ : Fin n → ℂ) (l l' : List (Fin n)) (h : GoodPath χ l)
    (h' : GoodPath (pathEnd χ l) l') : GoodPath χ (l ++ l') := by
  induction l generalizing χ with
  | nil => exact h'
  | cons s l ih => exact ⟨h.1, ih _ h.2 h'⟩

theorem pathEnd_replicate (χ : Fin n → ℂ) (s : Fin n) (k : ℕ) :
    pathEnd χ (List.replicate k s) = χ + Pi.single s (k : ℂ) := by
  induction k generalizing χ with
  | zero => funext r; simp [pathEnd]
  | succ k ih =>
    rw [List.replicate_succ, pathEnd, ih]
    funext r
    by_cases h : r = s
    · subst h; simp; ring
    · simp [Pi.single_eq_of_ne h]

theorem goodPath_replicate (χ : Fin n → ℂ) (s : Fin n) (k : ℕ)
    (h : ∀ j : ℕ, j < k → ∀ r, r ≠ s → χ r ≠ χ s + (j : ℂ) + 1) :
    GoodPath χ (List.replicate k s) := by
  induction k generalizing χ with
  | zero => trivial
  | succ k ih =>
    rw [List.replicate_succ]
    refine ⟨fun r => ?_, ih _ fun j hj r hr => ?_⟩
    · by_cases hr : r = s
      · subst hr; simp
      · simpa using h 0 (Nat.succ_pos k) r hr
    · have := h (j + 1) (Nat.succ_lt_succ hj) r hr
      simp only [Pi.add_apply, Pi.single_eq_of_ne hr, Pi.single_eq_same, add_zero]
      intro he
      apply this
      rw [he]; push_cast; ring

def blocks (m : Fin n → ℕ) (l : List (Fin n)) : List (Fin n) :=
  l.flatMap fun a => List.replicate (m a) a

theorem blocks_good (χ : Fin n → ℂ) (m : Fin n → ℕ) (f : Fin n → ℝ)
    (hf : ∀ a, f a = (χ a).re + m a)
    (hmono : ∀ a b, (χ a).re < (χ b).re → m a ≤ m b) (l : List (Fin n)) :
    ∀ χ' : Fin n → ℂ, l.Pairwise (fun a b => f b < f a) → (∀ r, r ∈ l → χ' r = χ r) →
      (∀ r, r ∉ l → χ' r = χ r + m r) → (∀ r, r ∉ l → ∀ a ∈ l, f a < f r) →
      GoodPath χ' (blocks m l) ∧ pathEnd χ' (blocks m l) = fun a => χ a + m a := by
  induction l with
  | nil =>
    intro χ' _ _ h2 _
    exact ⟨trivial, funext fun r => h2 r (by simp)⟩
  | cons a l ih =>
    intro χ' hp h1 h2 h3
    obtain ⟨hlt, hp'⟩ := List.pairwise_cons.1 hp
    have hb : blocks m (a :: l) = List.replicate (m a) a ++ blocks m l := by
      simp [blocks, List.flatMap_cons]
    have hχa : χ' a = χ a := h1 a (by simp)
    have hne : ∀ r ∈ l, r ≠ a := fun r hr h => by
      have := hlt r hr
      rw [h] at this
      exact lt_irrefl _ this
    have hI := ih (χ' + Pi.single a (m a : ℂ)) hp'
      (fun r hr => by
        simp [Pi.single_eq_of_ne (hne r hr), h1 r (List.mem_cons_of_mem _ hr)])
      (fun r hr => by
        by_cases h : r = a
        · subst h; simp [hχa]
        · have : r ∉ a :: l := by simp [h, hr]
          simp [Pi.single_eq_of_ne h, h2 r this])
      (fun r hr b hbl => by
        by_cases h : r = a
        · subst h; exact hlt b hbl
        · exact h3 r (by simp [h, hr]) b (List.mem_cons_of_mem _ hbl))
    rw [hb, pathEnd_append, pathEnd_replicate]
    refine ⟨goodPath_append _ _ _ (goodPath_replicate _ _ _ fun j hj r hr => ?_) ?_, hI.2⟩
    · intro he
      by_cases hrl : r ∈ l
      · rw [h1 r (List.mem_cons_of_mem _ hrl), hχa] at he
        have hre : (χ r).re = (χ a).re + j + 1 := by
          have := congrArg Complex.re he
          simpa using this
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have hm := hmono a r (by linarith)
        have hm' : (m a : ℝ) ≤ m r := by exact_mod_cast hm
        have := hlt r hrl
        rw [hf, hf] at this
        linarith
      · have hnot : r ∉ a :: l := by simp [hr, hrl]
        rw [h2 r hnot, hχa] at he
        have hre : (χ r).re + m r = (χ a).re + j + 1 := by
          have := congrArg Complex.re he
          simpa using this
        have hjm : (j : ℝ) + 1 ≤ m a := by exact_mod_cast hj
        have := h3 r hnot a (by simp)
        rw [hf, hf] at this
        linarith
    · rw [pathEnd_replicate]
      exact hI.1

theorem num (χ : Fin n → ℂ) (B : ℝ) : ∃ C δ : ℝ, 0 < δ ∧ ∀ N₀ : ℝ, ∃ (m : Fin n → ℕ) (N : ℝ),
    N₀ ≤ N ∧ (∀ a b, (χ a).re < (χ b).re → m a ≤ m b) ∧ (∀ a, 1 ≤ m a) ∧ 0 < N ∧
    FarLabels χ (fun a => χ a + (m a : ℂ)) B ∧
    (∀ a b, a ≠ b → δ * N ≤ |((χ a).re + m a) - ((χ b).re + m b)|) ∧
    ∀ a, |(χ a).re + m a| ≤ C * N ∧ |(χ a).im| ≤ C := by
  classical
  set x : Fin n → ℝ := fun a => (χ a).re with hx
  set M : ℝ := ∑ a, ‖χ a‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hnorm : ∀ a, ‖χ a‖ ≤ M := fun a =>
    Finset.single_le_sum (f := fun a => ‖χ a‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have hxM : ∀ a, |x a| ≤ M := fun a => (Complex.abs_re_le_norm _).trans (hnorm a)
  have hiM : ∀ a, |(χ a).im| ≤ M := fun a => (Complex.abs_im_le_norm _).trans (hnorm a)
  obtain ⟨e1, he1, hE1⟩ := exists_pos_lower (fun p : Fin n × Fin n => x p.2 - x p.1)
  obtain ⟨κ, hκ, hK⟩ := exists_pos_lower
    (fun p : Finset (Fin n) × Finset (Fin n) => -(∑ i ∈ p.1, x i - ∑ i ∈ p.2, x i))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨ε, hε, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * (n + 1) ≤ e1 ∧ ε * (2 * n ^ 2 + 2) ≤ κ := by
    refine ⟨min (e1 / (n + 1)) (κ / (2 * n ^ 2 + 2)), lt_min (by positivity) (by positivity), ?_, ?_⟩
    · exact (le_div_iff₀ (by positivity)).1 (min_le_left _ _)
    · exact (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have hidx : ∀ a : Fin n, (0 : ℝ) ≤ ((a : ℕ) : ℝ) ∧ ((a : ℕ) : ℝ) ≤ n := fun a =>
    ⟨Nat.cast_nonneg _, by exact_mod_cast a.2.le⟩
  set c : Fin n → ℝ := fun a => x a + ε * ((a : ℕ) : ℝ) + M + 1 with hc
  have hc1 : ∀ a, 1 ≤ c a := fun a => by
    have h1 := (abs_le.1 (hxM a)).1
    have h2 : 0 ≤ ε * ((a : ℕ) : ℝ) := mul_nonneg hε.le (hidx a).1
    simp only [hc]; linarith
  have hc2 : ∀ a, c a ≤ 2 * M + 1 + ε * n := fun a => by
    have h1 := (abs_le.1 (hxM a)).2
    have h2 : ε * ((a : ℕ) : ℝ) ≤ ε * n := mul_le_mul_of_nonneg_left (hidx a).2 hε.le
    simp only [hc]; linarith
  have hmonoc : ∀ a b, x a < x b → c a ≤ c b := fun a b h => by
    have h1 : e1 ≤ x b - x a := hE1 (a, b) (sub_pos.2 h)
    have h2 : ε * ((a : ℕ) : ℝ) ≤ ε * n := mul_le_mul_of_nonneg_left (hidx a).2 hε.le
    have h3 : 0 ≤ ε * ((b : ℕ) : ℝ) := mul_nonneg hε.le (hidx b).1
    simp only [hc]; nlinarith
  have hgapc : ∀ a b, a ≠ b → ε ≤ c a - c b ∨ ε ≤ c b - c a := by
    have hlt : ∀ a b, x a < x b → ε ≤ c b - c a := fun a b h => by
      have h1 : e1 ≤ x b - x a := hE1 (a, b) (sub_pos.2 h)
      have h2 : ε * ((a : ℕ) : ℝ) ≤ ε * n := mul_le_mul_of_nonneg_left (hidx a).2 hε.le
      have h3 : 0 ≤ ε * ((b : ℕ) : ℝ) := mul_nonneg hε.le (hidx b).1
      simp only [hc]; nlinarith
    have heq : ∀ a b : Fin n, x a = x b → (a : ℕ) < (b : ℕ) → ε ≤ c b - c a := fun a b h hab => by
      have h1 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
      have h2 := mul_le_mul_of_nonneg_left h1 hε.le
      simp only [hc, h]; nlinarith
    intro a b hab
    rcases lt_trichotomy (x a) (x b) with h | h | h
    · exact Or.inr (hlt a b h)
    · rcases lt_or_gt_of_ne (fun e => hab (Fin.ext e) : (a : ℕ) ≠ (b : ℕ)) with h' | h'
      · exact Or.inr (heq a b h h')
      · exact Or.inl (heq b a h.symm h')
    · exact Or.inl (hlt b a h)
  refine ⟨3 * M + 2 + ε * n, ε / 2, by positivity, fun N₀ => ?_⟩
  set N : ℝ := max (max N₀ 2) (max (2 * (2 * M + 1) / ε * 2) (2 * (n + |B| + 1) / κ)) with hN
  have hNN₀ : N₀ ≤ N := (le_max_left _ _).trans (le_max_left _ _)
  have hN2 : 2 ≤ N := (le_max_right _ _).trans (le_max_left _ _)
  have hNa : 2 * (2 * M + 1) / ε * 2 ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hNb : 2 * (n + |B| + 1) / κ ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  have hNε : 2 * M + 1 ≤ ε / 2 * N := by
    have : 2 * (2 * M + 1) / ε ≤ N / 2 := by linarith
    rw [div_le_iff₀ hε] at this
    linarith
  have hNκ : (n : ℝ) + B < κ / 2 * N := by
    rw [div_le_iff₀ hκ] at hNb
    have := le_abs_self B
    linarith
  set m : Fin n → ℕ := fun a => ⌊N * c a⌋₊ with hm
  have hNc : ∀ a, 0 ≤ N * c a := fun a => mul_nonneg (by linarith) (by linarith [hc1 a])
  have hfl : ∀ a, (m a : ℝ) ≤ N * c a := fun a => Nat.floor_le (hNc a)
  have hfu : ∀ a, N * c a < m a + 1 := fun a => Nat.lt_floor_add_one _
  refine ⟨m, N, hNN₀, ?_, ?_, by linarith, ?_, ?_, ?_⟩
  · intro a b h
    exact Nat.floor_mono (mul_le_mul_of_nonneg_left (hmonoc a b h) (by linarith))
  · intro a
    refine Nat.le_floor ?_
    have := hc1 a
    push_cast
    nlinarith
  · intro I I' _ hcard hv
    have hvx : (∑ i ∈ I, χ i - ∑ i ∈ I', χ i).re = ∑ i ∈ I, x i - ∑ i ∈ I', x i := by
      simp [hx, Complex.re_sum]
    rw [hvx] at hv
    have hKv : κ ≤ -(∑ i ∈ I, x i - ∑ i ∈ I', x i) := hK (I, I') (by simpa using hv)
    have hsumc : ∀ S : Finset (Fin n), ∑ i ∈ S, c i =
        ∑ i ∈ S, x i + ε * ∑ i ∈ S, ((i : ℕ) : ℝ) + S.card * (M + 1) := fun S => by
      simp only [hc, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    have hup : ∑ i ∈ I, (m i : ℝ) ≤ N * ∑ i ∈ I, c i := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _ => hfl i
    have hlo : N * ∑ i ∈ I', c i - I'.card ≤ ∑ i ∈ I', (m i : ℝ) := by
      have : ∑ i ∈ I', N * c i ≤ ∑ i ∈ I', ((m i : ℝ) + 1) :=
        Finset.sum_le_sum fun i _ => (hfu i).le
      rw [Finset.sum_add_distrib, ← Finset.mul_sum] at this
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at this
      linarith
    have hA : ∑ i ∈ I, ((i : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h1 : ∑ i ∈ I, ((i : ℕ) : ℝ) ≤ I.card • (n : ℝ) :=
        Finset.sum_le_card_nsmul _ _ _ fun i _ => (hidx i).2
      have h2 : (I.card : ℝ) ≤ n := by
        have := Finset.card_le_univ I
        simp only [Fintype.card_fin] at this
        exact_mod_cast this
      rw [nsmul_eq_mul] at h1
      nlinarith
    have hA' : 0 ≤ ∑ i ∈ I', ((i : ℕ) : ℝ) := Finset.sum_nonneg fun i _ => (hidx i).1
    have hk : (I'.card : ℝ) ≤ n := by
      have := Finset.card_le_univ I'
      simp only [Fintype.card_fin] at this
      exact_mod_cast this
    have hend : (∑ i ∈ I, (χ i + (m i : ℂ)) - ∑ i ∈ I', (χ i + (m i : ℂ))).re =
        (∑ i ∈ I, x i + ∑ i ∈ I, (m i : ℝ)) - (∑ i ∈ I', x i + ∑ i ∈ I', (m i : ℝ)) := by
      simp [hx, Complex.re_sum, Finset.sum_add_distrib]
    show (∑ i ∈ I, (χ i + (m i : ℂ)) - ∑ i ∈ I', (χ i + (m i : ℂ))).re < -B
    rw [hend]
    rw [hsumc] at hup
    rw [hsumc] at hlo
    rw [hcard] at hup
    set X := ∑ i ∈ I, x i
    set X' := ∑ i ∈ I', x i
    set A := ∑ i ∈ I, ((i : ℕ) : ℝ)
    set A' := ∑ i ∈ I', ((i : ℕ) : ℝ)
    set k : ℝ := (I'.card : ℝ)
    have hinner : X - X' + ε * (A - A') ≤ -(κ / 2) := by
      have h1 : ε * (A - A') ≤ ε * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (by linarith) hε.le
      have h2 : 0 ≤ ε * (n : ℝ) ^ 2 := by positivity
      nlinarith
    have hmul : N * (X - X' + ε * (A - A')) ≤ N * (-(κ / 2)) :=
      mul_le_mul_of_nonneg_left hinner (by linarith)
    nlinarith
  · intro a b hab
    have hxa := abs_le.1 (hxM a)
    have hxb := abs_le.1 (hxM b)
    have h1 := hfl a
    have h2 := hfl b
    have h3 := hfu a
    have h4 := hfu b
    have hNp : 0 ≤ N := by linarith
    rcases hgapc a b hab with h | h
    · have hh := mul_le_mul_of_nonneg_left h hNp
      refine le_abs.2 (Or.inl ?_)
      nlinarith
    · have hh := mul_le_mul_of_nonneg_left h hNp
      refine le_abs.2 (Or.inr ?_)
      nlinarith
  · intro a
    have hNp : 0 ≤ N := by linarith
    have hεn : 0 ≤ ε * n := by positivity
    refine ⟨?_, (hiM a).trans (by linarith)⟩
    have hxa := abs_le.1 (hxM a)
    have h1 := hfl a
    have h2 : N * c a ≤ N * (2 * M + 1 + ε * n) := mul_le_mul_of_nonneg_left (hc2 a) hNp
    have hm0 : (0 : ℝ) ≤ m a := Nat.cast_nonneg _
    have h3 : M ≤ N * M := by nlinarith
    refine abs_le.2 ⟨?_, ?_⟩
    · nlinarith
    · show x a + m a ≤ _
      nlinarith

theorem pathExists : CompanionTheory.RgExh.Fin.PathExists := by
  intro n χ B
  obtain ⟨C, δ, hδ, h⟩ := num χ B
  refine ⟨C, δ, hδ, fun N₀ => ?_⟩
  obtain ⟨m, N, hN₀, hmono, hpos, hN, hfar, hgap, hb⟩ := h N₀
  have hinj : Function.Injective (fun a => (χ a).re + (m a : ℝ)) := by
    intro a b hab
    by_contra hne
    have h1 := hgap a b hne
    have h2 : ((χ a).re + (m a : ℝ)) - ((χ b).re + (m b : ℝ)) = 0 := sub_eq_zero.2 hab
    rw [h2, abs_zero] at h1
    have := mul_pos hδ hN
    linarith
  obtain ⟨l, hl, hmem⟩ := exists_sorted _ hinj
  obtain ⟨hg, he⟩ := blocks_good χ m _ (fun _ => rfl) hmono l χ hl (fun _ _ => rfl)
    (fun r hr => (hr (hmem r)).elim) (fun r hr => (hr (hmem r)).elim)
  refine ⟨blocks m l, N, hN₀, hg, ?_, ?_, ?_, ?_⟩
  · rw [he]; exact hfar
  · intro s
    refine List.mem_flatMap.2 ⟨s, hmem s, List.mem_replicate.2 ⟨?_, rfl⟩⟩
    have := hpos s
    omega
  · intro a b hab
    rw [he]
    simpa using hgap a b hab
  · intro a
    rw [he]
    simpa using hb a

end GlobalTheory.CompanionTheory.RgPath
