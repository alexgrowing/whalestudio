import Mathlib

open Finset

namespace GlobalTheory.IterGain

noncomputable def words {ι : Type} [DecidableEq ι] (B : Finset ι) : ℕ → Finset (List ι)
  | 0 => {[]}
  | k + 1 => insert [] ((words B k ×ˢ B).image (fun p => p.1 ++ [p.2]))

theorem nil_mem {ι : Type} [DecidableEq ι] (B : Finset ι) (k : ℕ) : [] ∈ words B k := by
  cases k <;> simp [words]

theorem append_mem {ι : Type} [DecidableEq ι] {B : Finset ι} {k : ℕ} {l : List ι} {i : ι}
    (hl : l ∈ words B k) (hi : i ∈ B) : l ++ [i] ∈ words B (k + 1) := by
  simp only [words, mem_insert, mem_image, mem_product, Prod.exists]
  exact Or.inr ⟨l, i, ⟨hl, hi⟩, rfl⟩

theorem mem_letters {ι : Type} [DecidableEq ι] (B : Finset ι) :
    ∀ (k : ℕ), ∀ l ∈ words B k, ∀ i ∈ l, i ∈ B := by
  intro k
  induction k with
  | zero => intro l hl i hi; simp [words] at hl; subst hl; simp at hi
  | succ k ih =>
    intro l hl i hi
    simp only [words, mem_insert, mem_image, mem_product, Prod.exists] at hl
    rcases hl with rfl | ⟨l', j, ⟨hl', hj⟩, rfl⟩
    · simp at hi
    · rcases List.mem_append.1 hi with h | h
      · exact ih l' hl' i h
      · simp at h; subst h; exact hj

theorem root_le {x y : ℝ} {m : ℕ} (hm : m ≠ 0) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ^ m ≤ y ^ m) :
    x ≤ y := (pow_le_pow_iff_left₀ hx hy hm).1 h

theorem step {G ι : Type} [DecidableEq ι] (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ))
    (Dr : ι → (G → ℂ) → G → ℂ) (m : ℕ) (C δ₀ K : ℝ) (Q : G → ℝ) (A : ℕ)
    (hm : m ≠ 0) (hδ₀ : 0 < δ₀) (hC : 1 ≤ C) (hK : 1 ≤ K) (hKm : K ^ m = C)
    (hq : ∀ g, 1 ≤ q g) (hQ1 : ∀ g, 1 ≤ Q g) (hQm : ∀ g, Q g ^ m = q g)
    (hcl : ∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒)
    (hgain : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ m ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i))
    (k : ℕ) : ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ words B k, 0 ≤ c l) →
      (∀ l ∈ words B k, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) →
      ∀ g, ‖ψ g‖ * Q g ^ k ≤ Ck * q g ^ A * ∑ l ∈ words B k, c l := by
  induction k with
  | zero =>
    refine ⟨1, zero_le_one, ?_⟩
    intro ψ _ c _ hc g
    have h := hc [] (nil_mem B 0) g
    simp only [List.foldr_nil] at h
    simp [words]
    linarith
  | succ k ih =>
    obtain ⟨Ck, hCk0, hCk⟩ := ih
    have hK0 : 0 ≤ K := by linarith
    have hC0 : 0 ≤ C := by linarith
    have hQ0 : ∀ g, 0 ≤ Q g := fun g => by linarith [hQ1 g]
    have hq0 : ∀ g, 0 ≤ q g := fun g => by linarith [hq g]
    set M := K / δ₀ with hM
    have hM0 : 0 ≤ M := div_nonneg hK0 hδ₀.le
    set X1 := M ^ (k + 1)
    set X2 := C * K ^ (k + 1) * Ck * C ^ A * ((B.card : ℝ) * ((words B k).card : ℝ))
    have hX1 : 0 ≤ X1 := pow_nonneg hM0 _
    have hX2 : 0 ≤ X2 := by positivity
    refine ⟨X1 + X2, add_nonneg hX1 hX2, ?_⟩
    intro ψ hψ c hc0 hc g
    set T := ∑ l ∈ words B (k + 1), c l with hT
    have hT0 : 0 ≤ T := sum_nonneg hc0
    have hqA : 0 ≤ q g ^ A := pow_nonneg (hq0 g) _
    obtain ⟨δ, hδ, _, hδq, hcase⟩ := hgain g
    have hδQ : δ * Q g ≤ K := by
      apply root_le hm (mul_nonneg hδ.le (hQ0 g)) hK0
      rw [mul_pow, hQm, hKm]; linarith [mul_comm (q g) (δ ^ m)]
    have hQgw : ∀ w, q g ≤ C * q w → Q g ≤ K * Q w := by
      intro w hw
      apply root_le hm (hQ0 g) (mul_nonneg hK0 (hQ0 w))
      rw [mul_pow, hQm, hKm, hQm]; exact hw
    suffices h : ‖ψ g‖ * Q g ^ (k + 1) ≤ X1 * q g ^ A * T ∨
        ‖ψ g‖ * Q g ^ (k + 1) ≤ X2 * q g ^ A * T by
      have e1 : 0 ≤ X1 * q g ^ A * T := by positivity
      have e2 : 0 ≤ X2 * q g ^ A * T := mul_nonneg (mul_nonneg hX2 hqA) hT0
      rcases h with h | h <;> nlinarith
    rcases hcase with hδ0 | ⟨Ω, hΩ, hbound⟩
    · left
      have hQM : Q g ≤ M := by
        rw [hM, le_div_iff₀ hδ₀]; nlinarith [hQ0 g]
      have h0 : ‖ψ g‖ ≤ c [] * q g ^ A := by simpa using hc [] (nil_mem B _) g
      have hcT : c [] ≤ T := single_le_sum (f := c) (fun l hl => hc0 l hl) (nil_mem B _)
      have hQk : Q g ^ (k + 1) ≤ X1 := pow_le_pow_left₀ (hQ0 g) hQM _
      calc ‖ψ g‖ * Q g ^ (k + 1) ≤ (c [] * q g ^ A) * X1 :=
            mul_le_mul h0 hQk (pow_nonneg (hQ0 g) _) (by nlinarith [norm_nonneg (ψ g)])
        _ ≤ (T * q g ^ A) * X1 := by gcongr
        _ = X1 * q g ^ A * T := by ring
    · right
      set S : ι → ℝ := fun i => ∑ l ∈ words B k, c (l ++ [i]) with hS
      have hS0 : ∀ i ∈ B, 0 ≤ S i := fun i hi =>
        sum_nonneg (fun l hl => hc0 _ (append_mem hl hi))
      have hQgk : 0 < Q g ^ k := pow_pos (by linarith [hQ1 g]) _
      set P := K ^ k * Ck * C ^ A * q g ^ A with hP
      have hP0 : 0 ≤ P := by positivity
      set ci : ι → ℝ := fun i => P * S i / Q g ^ k with hci
      have hDr : ∀ i ∈ B, 0 ≤ ci i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ ci i := by
        intro i hi
        refine ⟨div_nonneg (mul_nonneg hP0 (hS0 i hi)) hQgk.le, ?_⟩
        intro w hw
        have hb := hCk (Dr i ψ) (hcl ψ hψ i hi) (fun l => c (l ++ [i]))
          (fun l hl => hc0 _ (append_mem hl hi))
          (fun l hl g' => by
            have := hc (l ++ [i]) (append_mem hl hi) g'
            simpa [List.foldr_append] using this) w
        have h1 : Q g ^ k ≤ K ^ k * Q w ^ k := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (hQ0 g) (hQgw w (hΩ w hw).2) k
        have h2 : q w ^ A ≤ C ^ A * q g ^ A := by
          rw [← mul_pow]; exact pow_le_pow_left₀ (hq0 w) (hΩ w hw).1 A
        rw [hci, le_div_iff₀ hQgk]
        calc ‖Dr i ψ w‖ * Q g ^ k ≤ ‖Dr i ψ w‖ * (K ^ k * Q w ^ k) :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = K ^ k * (‖Dr i ψ w‖ * Q w ^ k) := by ring
          _ ≤ K ^ k * (Ck * q w ^ A * S i) :=
              mul_le_mul_of_nonneg_left hb (pow_nonneg hK0 _)
          _ ≤ K ^ k * (Ck * (C ^ A * q g ^ A) * S i) := by
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg hK0 _)
              apply mul_le_mul_of_nonneg_right _ (hS0 i hi)
              exact mul_le_mul_of_nonneg_left h2 hCk0
          _ = P * S i := by rw [hP]; ring
      have hmain := hbound ψ hψ ci hDr
      have hsum : ∑ i ∈ B, ci i = P * (∑ i ∈ B, S i) / Q g ^ k := by
        rw [hci]; simp only; rw [← Finset.sum_div, ← Finset.mul_sum]
      have hSsum : ∑ i ∈ B, S i ≤ (B.card : ℝ) * ((words B k).card : ℝ) * T := by
        calc ∑ i ∈ B, S i ≤ ∑ i ∈ B, ∑ l ∈ words B k, T :=
              sum_le_sum (fun i hi => sum_le_sum (fun l hl =>
                single_le_sum (f := c) (fun l hl => hc0 l hl) (append_mem hl hi)))
          _ = (B.card : ℝ) * ((words B k).card : ℝ) * T := by
              simp [sum_const, nsmul_eq_mul]; ring
      have hSum0 : 0 ≤ ∑ i ∈ B, S i := sum_nonneg hS0
      calc ‖ψ g‖ * Q g ^ (k + 1) ≤ (C * δ * ∑ i ∈ B, ci i) * Q g ^ (k + 1) :=
            mul_le_mul_of_nonneg_right hmain (pow_nonneg (hQ0 g) _)
        _ = C * (δ * Q g) * (P * ∑ i ∈ B, S i) := by
            rw [hsum]; field_simp; ring
        _ ≤ C * K * (P * ((B.card : ℝ) * ((words B k).card : ℝ) * T)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left hδQ hC0)
              (mul_le_mul_of_nonneg_left hSsum hP0) (mul_nonneg hP0 hSum0) (mul_nonneg hC0 hK0)
        _ = X2 * q g ^ A * T := by rw [hP]; ring

end GlobalTheory.IterGain

namespace GlobalTheory

open GlobalTheory.IterGain in

theorem iterated_gain_rapid_decay : ∀ (G ι : Type) (B : Finset ι) (q : G → ℝ) (𝓒 : Set (G → ℂ))
    (Dr : ι → (G → ℂ) → G → ℂ) (b : ℕ) (C δ₀ : ℝ), 0 < δ₀ → (∀ g, 1 ≤ q g) →
    (∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒) →
    (∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ b ≤ C ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C * q g ∧ q g ≤ C * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C * δ * ∑ i ∈ B, c i)) →
    ∀ A N : ℕ, ∃ (L : Finset (List ι)) (C' : ℝ), (∀ l ∈ L, ∀ i ∈ l, i ∈ B) ∧
      ∀ ψ ∈ 𝓒, ∀ c : List ι → ℝ, (∀ l ∈ L, ∀ g, ‖l.foldr Dr ψ g‖ ≤ c l * q g ^ A) →
        ∀ g, ‖ψ g‖ * q g ^ N ≤ C' * ∑ l ∈ L, c l := by
  intro G ι B q 𝓒 Dr b C δ₀ hδ₀ hq hcl hgain A N
  classical
  set m := b + 1 with hmdef
  have hm : m ≠ 0 := Nat.succ_ne_zero b
  set C1 := max C 1 with hC1
  have hC1 : 1 ≤ C1 := le_max_right _ _
  have hCC1 : C ≤ C1 := le_max_left _ _
  have hq0 : ∀ g, 0 ≤ q g := fun g => by linarith [hq g]
  have hgain' : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ q g * δ ^ m ≤ C1 ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set G,
      (∀ w ∈ Ω, q w ≤ C1 * q g ∧ q g ≤ C1 * q w) ∧ ∀ ψ ∈ 𝓒, ∀ c : ι → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ C1 * δ * ∑ i ∈ B, c i) := by
    intro g
    obtain ⟨δ, hδ, hδ1, hqδ, hcase⟩ := hgain g
    refine ⟨δ, hδ, hδ1, ?_, ?_⟩
    · have h1 : q g * δ ^ m ≤ q g * δ ^ b := by
        rw [hmdef, pow_succ, ← mul_assoc]
        exact mul_le_of_le_one_right (mul_nonneg (hq0 g) (pow_nonneg hδ.le _)) hδ1
      linarith
    · rcases hcase with h | ⟨Ω, hΩ, hbd⟩
      · exact Or.inl h
      · refine Or.inr ⟨Ω, fun w hw => ⟨?_, ?_⟩, ?_⟩
        · exact (hΩ w hw).1.trans (mul_le_mul_of_nonneg_right hCC1 (hq0 g))
        · exact (hΩ w hw).2.trans (mul_le_mul_of_nonneg_right hCC1 (hq0 w))
        · intro ψ hψ c hc
          have hs : 0 ≤ ∑ i ∈ B, c i := sum_nonneg (fun i hi => (hc i hi).1)
          exact (hbd ψ hψ c hc).trans
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC1 hδ.le) hs)
  set K : ℝ := C1 ^ ((m : ℝ)⁻¹) with hK
  set Q : G → ℝ := fun g => q g ^ ((m : ℝ)⁻¹) with hQ
  have hKm : K ^ m = C1 := Real.rpow_inv_natCast_pow (by linarith) hm
  have hK1 : 1 ≤ K := Real.one_le_rpow hC1 (by positivity)
  have hQm : ∀ g, Q g ^ m = q g := fun g => Real.rpow_inv_natCast_pow (hq0 g) hm
  have hQ1 : ∀ g, 1 ≤ Q g := fun g => Real.one_le_rpow (hq g) (by positivity)
  obtain ⟨Ck, _, hCk⟩ := step B q 𝓒 Dr m C1 δ₀ K Q A hm hδ₀ hC1 hK1 hKm hq hQ1 hQm hcl hgain'
    (m * (A + N))
  refine ⟨words B (m * (A + N)), Ck, mem_letters B _, ?_⟩
  intro ψ hψ c hc g
  have hqA : 0 < q g ^ A := pow_pos (by linarith [hq g]) _
  have hc0 : ∀ l ∈ words B (m * (A + N)), 0 ≤ c l := by
    intro l hl
    by_contra h
    push_neg at h
    have h1 := hc l hl g
    have h2 : c l * q g ^ A < 0 := mul_neg_of_neg_of_pos h hqA
    linarith [norm_nonneg (List.foldr Dr ψ l g)]
  have h := hCk ψ hψ c hc0 hc g
  rw [pow_mul, hQm, pow_add] at h
  have h' : q g ^ A * (‖ψ g‖ * q g ^ N) ≤ q g ^ A * (Ck * ∑ l ∈ words B (m * (A + N)), c l) := by
    linarith
  exact le_of_mul_le_mul_left h' hqA

end GlobalTheory
