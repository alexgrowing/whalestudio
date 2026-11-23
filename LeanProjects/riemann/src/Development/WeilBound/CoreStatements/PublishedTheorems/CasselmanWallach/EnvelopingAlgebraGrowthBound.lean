import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace IdentityFiltrationBound

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def W (n k : ℕ) : Finset (List (Fin n × Fin n)) := (List.finite_length_le (Fin n × Fin n) k).toFinset

lemma mem_W {k : ℕ} {l : List (Fin n × Fin n)} : l ∈ W n k ↔ l.length ≤ k := by
  simp [W]

def wd (E : Fin n → Fin n → Module.End ℂ V) (l : List (Fin n × Fin n)) : Module.End ℂ V :=
  (l.map fun p => E p.1 p.2).prod

def N (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) (v : V) : ℝ := ∑ l ∈ W n k, ‖wd E l v‖

lemma N_nonneg (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) (v : V) : 0 ≤ N E k v :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma le_N (E : Fin n → Fin n → Module.End ℂ V) {k : ℕ} {l : List (Fin n × Fin n)} (hl : l.length ≤ k)
    (v : V) : ‖wd E l v‖ ≤ N E k v :=
  Finset.single_le_sum (f := fun l => ‖wd E l v‖) (fun _ _ => norm_nonneg _) (mem_W.2 hl)

lemma U_bound (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) (u : Module.End ℂ V) (hu : u ∈ U E k) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ v, ‖u v‖ ≤ c * N E k v := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact ⟨1, zero_le_one, fun v => by simpa [wd] using le_N E hl v⟩
  | zero => exact ⟨0, le_rfl, fun v => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, h⟩ := hx
    obtain ⟨d, hd, h'⟩ := hy
    refine ⟨c + d, add_nonneg hc hd, fun v => ?_⟩
    calc ‖(x + y) v‖ ≤ ‖x v‖ + ‖y v‖ := by simpa using norm_add_le (x v) (y v)
      _ ≤ c * N E k v + d * N E k v := add_le_add (h v) (h' v)
      _ = (c + d) * N E k v := by ring
  | smul a x _ hx =>
    obtain ⟨c, hc, h⟩ := hx
    refine ⟨‖a‖ * c, mul_nonneg (norm_nonneg _) hc, fun v => ?_⟩
    calc ‖(a • x) v‖ = ‖a‖ * ‖x v‖ := by simp [norm_smul]
      _ ≤ ‖a‖ * (c * N E k v) := mul_le_mul_of_nonneg_left (h v) (norm_nonneg _)
      _ = ‖a‖ * c * N E k v := by ring

lemma quad {x y P Q : ℝ} (_hx : 0 ≤ x) (hy : 0 ≤ y) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h : x ^ 2 ≤ P * y ^ 2 + Q * x * y) : x ≤ (Q + Real.sqrt P) * y := by
  by_contra hc
  push Not at hc
  have hs := Real.sq_sqrt hP
  have hs0 := Real.sqrt_nonneg P
  have hxpos : 0 < x := lt_of_le_of_lt (mul_nonneg (add_nonneg hQ hs0) hy) hc
  have h1 : Real.sqrt P * y ≤ x := by nlinarith [mul_nonneg hQ hy]
  nlinarith [mul_pos hxpos (sub_pos.2 hc), mul_le_mul_of_nonneg_left h1 (mul_nonneg hs0 hy)]

lemma step (E : Fin n → Fin n → Module.End ℂ V) (ε : Fin n → Bool) (κ μ c : ℝ) (k : ℕ)
    (hcas : ∀ w : V, ∑ a, ∑ b, ‖E a b w‖ ^ 2 = 2 * (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2)
    (hc0 : 0 ≤ c)
    (hc : ∀ l : List (Fin n × Fin n), l.length ≤ k → ∀ v,
      ‖(casimirK ε E * wd E l - wd E l * casimirK ε E) v‖ ≤ c * N E (k + 1) v)
    (v : V) (hv : casimirK ε E v = (μ : ℂ) • v) (hμ : 0 ≤ μ) :
    N E (k + 1) v ≤ (2 * ((W n (k + 1)).card : ℝ) ^ 2 * c + ((W n (k + 1)).card : ℝ) * Real.sqrt (2 + |κ|)) *
      Real.sqrt (1 + μ) * N E k v := by
  have hx : 0 ≤ N E (k + 1) v := N_nonneg E _ v
  have hy : 0 ≤ N E k v := N_nonneg E _ v
  set x := N E (k + 1) v with hxdef
  set y := N E k v with hydef
  set M : ℝ := ((W n (k + 1)).card : ℝ) with hM
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hκ := abs_nonneg κ
  have key : ∀ l : List (Fin n × Fin n), l.length ≤ k + 1 →
      ‖wd E l v‖ ^ 2 ≤ (2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y := by
    intro l hl
    cases l with
    | nil =>
      have h1 : ‖wd E [] v‖ ≤ y := le_N E (l := []) (k := k) (Nat.zero_le _) v
      have h2 : 0 ≤ ‖wd E [] v‖ := norm_nonneg _
      nlinarith [mul_nonneg (mul_nonneg hc0 hx) hy,
        mul_nonneg (add_nonneg (mul_nonneg zero_le_two hμ) hκ) (sq_nonneg y)]
    | cons p l' =>
      have hl' : l'.length ≤ k := by simpa using hl
      have hwy : ‖wd E l' v‖ ≤ y := le_N E hl' v
      have hz := hc l' hl' v
      have hOw : casimirK ε E (wd E l' v) =
          (casimirK ε E * wd E l' - wd E l' * casimirK ε E) v + (μ : ℂ) • wd E l' v := by
        simp only [LinearMap.sub_apply, Module.End.mul_apply, hv, map_smul]
        abel
      have hsplit : wd E (p :: l') v = E p.1 p.2 (wd E l' v) := by
        simp [wd, Module.End.mul_apply]
      rw [hsplit]
      have hle : ‖E p.1 p.2 (wd E l' v)‖ ^ 2 ≤ ∑ a, ∑ b, ‖E a b (wd E l' v)‖ ^ 2 := by
        calc ‖E p.1 p.2 (wd E l' v)‖ ^ 2 ≤ ∑ b, ‖E p.1 b (wd E l' v)‖ ^ 2 :=
              Finset.single_le_sum (f := fun b => ‖E p.1 b (wd E l' v)‖ ^ 2) (fun _ _ => sq_nonneg _)
                (Finset.mem_univ _)
          _ ≤ ∑ a, ∑ b, ‖E a b (wd E l' v)‖ ^ 2 :=
              Finset.single_le_sum (f := fun a => ∑ b, ‖E a b (wd E l' v)‖ ^ 2)
                (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ _)
      have hin : (inner ℂ (wd E l' v) (casimirK ε E (wd E l' v))).re ≤
          ‖wd E l' v‖ * ‖(casimirK ε E * wd E l' - wd E l' * casimirK ε E) v‖ + μ * ‖wd E l' v‖ ^ 2 := by
        have hself : (inner ℂ (wd E l' v) (wd E l' v)).re = ‖wd E l' v‖ ^ 2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        rw [hOw, inner_add_right, Complex.add_re, inner_smul_right, Complex.re_ofReal_mul, hself]
        have := (Complex.re_le_norm (inner ℂ (wd E l' v)
          ((casimirK ε E * wd E l' - wd E l' * casimirK ε E) v))).trans (norm_inner_le_norm _ _)
        linarith
      rw [hcas] at hle
      have hw0 := norm_nonneg (wd E l' v)
      have hz0 := norm_nonneg ((casimirK ε E * wd E l' - wd E l' * casimirK ε E) v)
      have e1 := mul_le_mul hwy hz hz0 hy
      have e2 : ‖wd E l' v‖ ^ 2 ≤ y ^ 2 := by nlinarith
      have e3 := mul_le_mul_of_nonneg_left e2 hμ
      have e4 := mul_le_mul_of_nonneg_left e2 hκ
      have hk : -κ * ‖wd E l' v‖ ^ 2 ≤ |κ| * ‖wd E l' v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [neg_abs_le κ]) (sq_nonneg _)
      nlinarith [sq_nonneg y]
  have hR0 : 0 ≤ (2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y := by positivity
  have hsum : x ≤ M * Real.sqrt ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) := by
    calc x = ∑ l ∈ W n (k + 1), ‖wd E l v‖ := rfl
      _ ≤ ∑ l ∈ W n (k + 1), Real.sqrt ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) :=
          Finset.sum_le_sum fun l hl => (le_abs_self _).trans (Real.abs_le_sqrt (key l (mem_W.1 hl)))
      _ = M * Real.sqrt ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) := by simp [hM]
  have hsq : x ^ 2 ≤ M ^ 2 * ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) := by
    have := Real.sq_sqrt hR0
    have h0 := mul_nonneg hM0 (Real.sqrt_nonneg ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y))
    nlinarith
  have hA : 0 ≤ 2 * μ + |κ| + 1 := by positivity
  have hq := quad (P := M ^ 2 * (2 * μ + |κ| + 1)) (Q := 2 * M ^ 2 * c) hx hy (by positivity) (by positivity)
    (by linarith)
  rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0] at hq
  have ha : Real.sqrt (2 * μ + |κ| + 1) ≤ Real.sqrt (2 + |κ|) * Real.sqrt (1 + μ) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have ht : 1 ≤ Real.sqrt (1 + μ) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + μ by linarith)
    rwa [Real.sqrt_one] at this
  have h1 := mul_le_mul_of_nonneg_left ht (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * M ^ 2 * c) hy)
  have h2 := mul_le_mul_of_nonneg_left ha (mul_nonneg hM0 hy)
  nlinarith

end IdentityFiltrationBound

open IdentityFiltrationBound in
theorem SymmetricPowerMatrix : A0 → A1 → CasimirIsRealScalar → A6 := by
  intro h0 h1 h3 n ε V _ _ E hE
  obtain ⟨κ, hκ⟩ := h3 n ε V E hE
  obtain ⟨-, -, -, h0c⟩ := h0 n ε V E hE
  obtain ⟨hmono, -, -, -, hcomm, hK2, -⟩ := h1 n ε V E hE
  have hcas : ∀ w : V, ∑ a, ∑ b, ‖E a b w‖ ^ 2 = 2 * (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2 :=
    fun w => (h0c κ hκ w).1
  have grow : ∀ k : ℕ, ∃ G : ℝ, 0 ≤ G ∧ ∀ μ v, 0 ≤ μ → Eig ε E μ v →
      N E k v ≤ G * Real.sqrt (1 + μ) ^ k * ‖v‖ := by
    intro k
    induction k with
    | zero =>
      refine ⟨(W n 0).card, Nat.cast_nonneg _, fun μ v _ _ => ?_⟩
      simp only [pow_zero, mul_one]
      calc N E 0 v = ∑ l ∈ W n 0, ‖wd E l v‖ := rfl
        _ ≤ ∑ l ∈ W n 0, ‖v‖ := Finset.sum_le_sum fun l hl => by
            have := mem_W.1 hl
            cases l with
            | nil => simp [wd]
            | cons p l => simp at this
        _ = _ := by simp
    | succ k ih =>
      obtain ⟨G, hG, hG'⟩ := ih
      have hc : ∀ l : List (Fin n × Fin n), ∃ c : ℝ, 0 ≤ c ∧ (l.length ≤ k → ∀ v,
          ‖(casimirK ε E * wd E l - wd E l * casimirK ε E) v‖ ≤ c * N E (k + 1) v) := by
        intro l
        by_cases hl : l.length ≤ k
        · have hmem : wd E l ∈ U E k := hmono _ _ hl (Submodule.subset_span ⟨l, le_rfl, rfl⟩)
          have hin := hcomm 2 k _ hK2 _ hmem
          have h' : 2 + k - 1 = k + 1 := by omega
          rw [h'] at hin
          obtain ⟨c, hc, hc'⟩ := U_bound E (k + 1) _ hin
          exact ⟨c, hc, fun _ => hc'⟩
        · exact ⟨0, le_rfl, fun h => absurd h hl⟩
      choose c hc0 hc using hc
      have hC : ∀ l : List (Fin n × Fin n), l.length ≤ k → ∀ v,
          ‖(casimirK ε E * wd E l - wd E l * casimirK ε E) v‖ ≤ (∑ l ∈ W n k, c l) * N E (k + 1) v :=
        fun l hl v => (hc l hl v).trans (mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := c) (fun i _ => hc0 i) (mem_W.2 hl)) (N_nonneg _ _ _))
      have hC0 : 0 ≤ ∑ l ∈ W n k, c l := Finset.sum_nonneg fun i _ => hc0 i
      refine ⟨(2 * ((W n (k + 1)).card : ℝ) ^ 2 * (∑ l ∈ W n k, c l) +
        ((W n (k + 1)).card : ℝ) * Real.sqrt (2 + |κ|)) * G, by positivity, fun μ v hμ hv => ?_⟩
      have hst := step E ε κ μ _ k hcas hC0 hC v hv hμ
      calc N E (k + 1) v ≤ _ := hst
        _ ≤ (2 * ((W n (k + 1)).card : ℝ) ^ 2 * (∑ l ∈ W n k, c l) +
            ((W n (k + 1)).card : ℝ) * Real.sqrt (2 + |κ|)) * Real.sqrt (1 + μ) *
              (G * Real.sqrt (1 + μ) ^ k * ‖v‖) :=
          mul_le_mul_of_nonneg_left (hG' μ v hμ hv) (by positivity)
        _ = _ := by ring
  intro k u hu
  obtain ⟨c, hc, hc'⟩ := U_bound E k u hu
  obtain ⟨G, hG, hG'⟩ := grow k
  refine ⟨c * G, mul_nonneg hc hG, fun μ v hμ hv => ?_⟩
  calc ‖u v‖ ≤ c * N E k v := hc' v
    _ ≤ c * (G * Real.sqrt (1 + μ) ^ k * ‖v‖) := mul_le_mul_of_nonneg_left (hG' μ v hμ hv) hc
    _ = _ := by ring

end PositivityTheory.CW

end
