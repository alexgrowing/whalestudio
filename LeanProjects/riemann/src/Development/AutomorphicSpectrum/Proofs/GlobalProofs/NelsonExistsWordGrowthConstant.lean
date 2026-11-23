import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson

variable {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {d : ℕ}

private theorem list_bound_lemma (X : Fin d → Module.End ℂ M) (V : Submodule ℂ M)
    [FiniteDimensional ℂ V] (l : List (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ C * ‖u‖ :=
  ⟨‖LinearMap.toContinuousLinearMap (((l.map X).prod).comp V.subtype)‖,
    ContinuousLinearMap.opNorm_nonneg _,
    fun u hu => (LinearMap.toContinuousLinearMap (((l.map X).prod).comp V.subtype)).le_opNorm ⟨u, hu⟩⟩

theorem exists_word_bound (X : Fin d → Module.End ℂ M) (V : Submodule ℂ M)
    [FiniteDimensional ℂ V] (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ l : List (Fin d), l.length = k → ∀ u ∈ V,
      ‖(l.map X).prod u‖ ≤ B * ‖u‖ := by
  choose C hC0 hC using fun l : List (Fin d) => list_bound_lemma X V l
  have hfin : {l : List (Fin d) | l.length = k}.Finite :=
    (Set.finite_range (fun v : List.Vector (Fin d) k => v.1)).subset fun l hl => ⟨⟨l, hl⟩, rfl⟩
  refine ⟨∑ l ∈ hfin.toFinset, C l, Finset.sum_nonneg fun l _ => hC0 l, fun l hl u hu => ?_⟩
  refine (hC l u hu).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg u))
  exact Finset.single_le_sum (fun l _ => hC0 l) (hfin.mem_toFinset.2 hl)

theorem exists_least_word_bound (X : Fin d → Module.End ℂ M) (V : Submodule ℂ M)
    [FiniteDimensional ℂ V] (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ l : List (Fin d), l.length = k → ∀ u ∈ V,
      ‖(l.map X).prod u‖ ≤ B * ‖u‖) ∧
      ∀ B' : ℝ, 0 ≤ B' → (∀ l : List (Fin d), l.length = k → ∀ u ∈ V,
        ‖(l.map X).prod u‖ ≤ B' * ‖u‖) → B ≤ B' := by
  obtain ⟨B₀, hB₀0, hB₀⟩ := exists_word_bound X V k
  let S : Set ℝ := {B' | 0 ≤ B' ∧ ∀ l : List (Fin d), l.length = k → ∀ u ∈ V,
      ‖(l.map X).prod u‖ ≤ B' * ‖u‖}
  have hne : S.Nonempty := ⟨B₀, hB₀0, hB₀⟩
  have hbdd : BddBelow S := ⟨0, fun B' hB' => hB'.1⟩
  refine ⟨sInf S, le_csInf hne fun B' hB' => hB'.1, fun l hl u hu => ?_,
    fun B' hB'0 hB' => csInf_le hbdd ⟨hB'0, hB'⟩⟩
  rcases (norm_nonneg u).eq_or_lt with h0 | hpos
  · have hu0 : u = 0 := norm_eq_zero.1 h0.symm
    simp [hu0]
  · rw [← div_le_iff₀ hpos]
    exact le_csInf hne fun B' hB' => (div_le_iff₀ hpos).2 (hB'.2 l hl u hu)

theorem comm_sumSq (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (j : Fin d) :
    (∑ i, X i * X i) * X j - X j * (∑ i, X i * X i) =
      ∑ i, ∑ m, c i j m • (X i * X m + X m * X i) := by
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h : X i * X i * X j - X j * (X i * X i) =
      X i * (X i * X j - X j * X i) + (X i * X j - X j * X i) * X i := by noncomm_ring
  rw [h, hc i j, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc, smul_add]

theorem comm_word_bound (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (V : Submodule ℂ M)
    (k : ℕ) (B γ : ℝ) (hB0 : 0 ≤ B)
    (hγ : ∀ j, ∑ i, ∑ m, 2 * ‖c i j m‖ ≤ γ)
    (hB : ∀ l : List (Fin d), l.length = k + 1 → ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ B * ‖u‖) :
    ∀ (l p : List (Fin d)), p.length + l.length = k → ∀ u ∈ V,
      ‖((p.map X).prod * ((∑ i, X i * X i) * (l.map X).prod -
        (l.map X).prod * (∑ i, X i * X i))) u‖ ≤ l.length * γ * B * ‖u‖ := by
  intro l
  induction l with
  | nil =>
    intro p _ u _
    simp
  | cons j l ih =>
    intro p hpl u hu
    have hlen : (p ++ [j]).length + l.length = k := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hpl ⊢
      omega
    have hw : ∀ i m, ‖((p.map X).prod * (X i * X m) * (l.map X).prod) u‖ ≤ B * ‖u‖ := by
      intro i m
      have h := hB (p ++ i :: m :: l) (by
        simp only [List.length_append, List.length_cons] at hpl ⊢
        omega) u hu
      simpa [List.map_append, List.prod_append, mul_assoc] using h
    have hexp : ((p.map X).prod * ((∑ i, X i * X i) * X j - X j * (∑ i, X i * X i)) *
        (l.map X).prod) u =
        ∑ i, ∑ m, c i j m • (((p.map X).prod * (X i * X m) * (l.map X).prod) u +
          ((p.map X).prod * (X m * X i) * (l.map X).prod) u) := by
      rw [comm_sumSq X c hc j]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
        LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply]
    have h1 : ‖((p.map X).prod * ((∑ i, X i * X i) * X j - X j * (∑ i, X i * X i)) *
        (l.map X).prod) u‖ ≤ γ * B * ‖u‖ := by
      rw [hexp]
      calc _ ≤ ∑ i, ∑ m, ‖c i j m‖ * (B * ‖u‖ + B * ‖u‖) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left
              ((norm_add_le _ _).trans (add_le_add (hw i m) (hw m i))) (norm_nonneg _)
        _ = (∑ i, ∑ m, 2 * ‖c i j m‖) * (B * ‖u‖) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
        _ ≤ γ * (B * ‖u‖) := mul_le_mul_of_nonneg_right (hγ j) (mul_nonneg hB0 (norm_nonneg u))
        _ = γ * B * ‖u‖ := by ring
    have h2 := ih (p ++ [j]) hlen u hu
    have key : (p.map X).prod * ((∑ i, X i * X i) * ((j :: l).map X).prod -
        ((j :: l).map X).prod * (∑ i, X i * X i)) =
        (p.map X).prod * ((∑ i, X i * X i) * X j - X j * (∑ i, X i * X i)) * (l.map X).prod +
        ((p ++ [j]).map X).prod * ((∑ i, X i * X i) * (l.map X).prod -
          (l.map X).prod * (∑ i, X i * X i)) := by
      simp only [List.map_cons, List.prod_cons, List.map_append, List.prod_append, List.map_nil,
        List.prod_nil, mul_one]
      noncomm_ring
    rw [key, LinearMap.add_apply]
    calc _ ≤ γ * B * ‖u‖ + l.length * γ * B * ‖u‖ := (norm_add_le _ _).trans (add_le_add h1 h2)
      _ = ((j :: l).length : ℝ) * γ * B * ‖u‖ := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring

theorem energy_le (X : Fin d → Module.End ℂ M) (a : ℝ)
    (hs : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ a * ‖u‖ * ‖v‖) (x : M) :
    ∑ i, ‖X i x‖ ^ 2 ≤ ‖(∑ i, X i * X i) x‖ * ‖x‖ + a * (∑ i, ‖X i x‖) * ‖x‖ := by
  have hi : ∀ i, ‖X i x‖ ^ 2 ≤ -(⟪x, (X i * X i) x⟫_ℂ).re + a * ‖X i x‖ * ‖x‖ := by
    intro i
    have h := le_trans (le_abs_self _) (hs i x (X i x))
    have h1 : (⟪X i x, X i x⟫_ℂ).re = ‖X i x‖ ^ 2 := by
      rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]
    rw [Complex.add_re, h1] at h
    rw [Module.End.mul_apply]
    nlinarith [h]
  have hsum : -(⟪x, (∑ i, X i * X i) x⟫_ℂ).re = ∑ i, -(⟪x, (X i * X i) x⟫_ℂ).re := by
    rw [LinearMap.sum_apply, inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
  have hre : -(⟪x, (∑ i, X i * X i) x⟫_ℂ).re ≤ ‖(∑ i, X i * X i) x‖ * ‖x‖ := by
    have h := re_inner_le_norm (𝕜 := ℂ) (-x) ((∑ i, X i * X i) x)
    rw [inner_neg_left, map_neg, norm_neg, RCLike.re_to_complex] at h
    linarith [mul_comm ‖x‖ ‖(∑ i, X i * X i) x‖]
  calc ∑ i, ‖X i x‖ ^ 2 ≤ ∑ i, (-(⟪x, (X i * X i) x⟫_ℂ).re + a * ‖X i x‖ * ‖x‖) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = -(⟪x, (∑ i, X i * X i) x⟫_ℂ).re + a * (∑ i, ‖X i x‖) * ‖x‖ := by
      rw [Finset.sum_add_distrib, hsum, Finset.mul_sum, Finset.sum_mul]
    _ ≤ _ := by linarith [hre]

theorem step_sq (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (a : ℝ) (ha : 0 ≤ a)
    (hs : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ a * ‖u‖ * ‖v‖)
    (V : Submodule ℂ M) (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V)
    (k : ℕ) (A B γ s : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hγ0 : 0 ≤ γ)
    (hγ : ∀ j, ∑ i, ∑ m, 2 * ‖c i j m‖ ≤ γ)
    (hΔ : ∀ u ∈ V, ‖(∑ i, X i * X i) u‖ ≤ s ^ 2 * ‖u‖)
    (hA : ∀ l : List (Fin d), l.length = k → ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ A * ‖u‖)
    (hB : ∀ l : List (Fin d), l.length = k + 1 → ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ B * ‖u‖)
    (l : List (Fin d)) (hl : l.length = k) (i : Fin d) (u : M) (hu : u ∈ V) :
    ‖X i ((l.map X).prod u)‖ ^ 2 ≤
      (s ^ 2 * A ^ 2 + (k * γ + a * d) * A * B) * ‖u‖ ^ 2 := by
  have hu0 := norm_nonneg u
  have hx : ‖(l.map X).prod u‖ ≤ A * ‖u‖ := hA l hl u hu
  have hXi : ∀ j, ‖X j ((l.map X).prod u)‖ ≤ B * ‖u‖ := by
    intro j
    have h := hB (j :: l) (by simp [hl]) u hu
    simpa using h
  have hcomm : ‖((∑ i, X i * X i) * (l.map X).prod - (l.map X).prod * (∑ i, X i * X i)) u‖ ≤
      k * γ * B * ‖u‖ := by
    have h := comm_word_bound X c hc V k B γ hB0 hγ hB l [] (by simp [hl]) u hu
    simpa [hl] using h
  have hΔx : ‖(∑ i, X i * X i) ((l.map X).prod u)‖ ≤ (s ^ 2 * A + k * γ * B) * ‖u‖ := by
    have e : (∑ i, X i * X i) ((l.map X).prod u) = (l.map X).prod ((∑ i, X i * X i) u) +
        ((∑ i, X i * X i) * (l.map X).prod - (l.map X).prod * (∑ i, X i * X i)) u := by
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
      abel
    rw [e]
    have h1 : ‖(l.map X).prod ((∑ i, X i * X i) u)‖ ≤ A * (s ^ 2 * ‖u‖) :=
      (hA l hl _ (hV u hu)).trans (mul_le_mul_of_nonneg_left (hΔ u hu) hA0)
    calc _ ≤ A * (s ^ 2 * ‖u‖) + k * γ * B * ‖u‖ := (norm_add_le _ _).trans (add_le_add h1 hcomm)
      _ = (s ^ 2 * A + k * γ * B) * ‖u‖ := by ring
  have hE := energy_le X a hs ((l.map X).prod u)
  have hsumX : ∑ j, ‖X j ((l.map X).prod u)‖ ≤ d * (B * ‖u‖) := by
    calc ∑ j, ‖X j ((l.map X).prod u)‖ ≤ ∑ _j : Fin d, B * ‖u‖ :=
          Finset.sum_le_sum fun j _ => hXi j
      _ = d * (B * ‖u‖) := by simp
  have hsingle : ‖X i ((l.map X).prod u)‖ ^ 2 ≤ ∑ j, ‖X j ((l.map X).prod u)‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖X j ((l.map X).prod u)‖ ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have hLu0 := norm_nonneg ((l.map X).prod u)
  have hc1 : 0 ≤ (s ^ 2 * A + k * γ * B) * ‖u‖ :=
    mul_nonneg (add_nonneg (mul_nonneg (sq_nonneg s) hA0)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hγ0) hB0)) hu0
  have t1 := mul_le_mul hΔx hx hLu0 hc1
  have t2 : a * (∑ j, ‖X j ((l.map X).prod u)‖) * ‖(l.map X).prod u‖ ≤
      a * (d * (B * ‖u‖)) * (A * ‖u‖) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hsumX ha) hx hLu0
      (mul_nonneg ha (mul_nonneg (Nat.cast_nonneg d) (mul_nonneg hB0 hu0)))
  calc ‖X i ((l.map X).prod u)‖ ^ 2 ≤ ∑ j, ‖X j ((l.map X).prod u)‖ ^ 2 := hsingle
    _ ≤ _ := hE
    _ ≤ (s ^ 2 * A + k * γ * B) * ‖u‖ * (A * ‖u‖) + a * (d * (B * ‖u‖)) * (A * ‖u‖) :=
        add_le_add t1 t2
    _ = (s ^ 2 * A ^ 2 + (k * γ + a * d) * A * B) * ‖u‖ ^ 2 := by ring

theorem le_of_sq_le_quad (A B s E : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hs0 : 0 ≤ s) (hE0 : 0 ≤ E)
    (h : B ^ 2 ≤ s ^ 2 * A ^ 2 + E * A * B) : B ≤ (s + E) * A := by
  by_contra hc
  rw [not_le] at hc
  have hsA : s * A ≤ B := by nlinarith [mul_nonneg hE0 hA0]
  have hB : 0 < B := lt_of_le_of_lt (mul_nonneg (add_nonneg hs0 hE0) hA0) hc
  have h1 : (s + E) * A * B < B * B := mul_lt_mul_of_pos_right hc hB
  have h2 : s * A * (s * A) ≤ s * A * B := mul_le_mul_of_nonneg_left hsA (mul_nonneg hs0 hA0)
  nlinarith [h1, h2, h]

theorem next_word_bound (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (a : ℝ) (ha : 0 ≤ a)
    (hs : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ a * ‖u‖ * ‖v‖)
    (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V)
    (k : ℕ) (A γ s : ℝ) (hA0 : 0 ≤ A) (hs0 : 0 ≤ s) (hγ0 : 0 ≤ γ)
    (hγ : ∀ j, ∑ i, ∑ m, 2 * ‖c i j m‖ ≤ γ)
    (hΔ : ∀ u ∈ V, ‖(∑ i, X i * X i) u‖ ≤ s ^ 2 * ‖u‖)
    (hA : ∀ l : List (Fin d), l.length = k → ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ A * ‖u‖) :
    ∀ l : List (Fin d), l.length = k + 1 → ∀ u ∈ V,
      ‖(l.map X).prod u‖ ≤ (s + (k * γ + a * d)) * A * ‖u‖ := by
  have hE0 : 0 ≤ (k : ℝ) * γ + a * d :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg k) hγ0) (mul_nonneg ha (Nat.cast_nonneg d))
  obtain ⟨B, hB0, hBb, hBl⟩ := exists_least_word_bound X V (k + 1)
  have hQ0 : 0 ≤ s ^ 2 * A ^ 2 + ((k : ℝ) * γ + a * d) * A * B :=
    add_nonneg (mul_nonneg (sq_nonneg s) (sq_nonneg A)) (mul_nonneg (mul_nonneg hE0 hA0) hB0)
  have hsq : ∀ l : List (Fin d), l.length = k + 1 → ∀ u ∈ V,
      ‖(l.map X).prod u‖ ≤ Real.sqrt (s ^ 2 * A ^ 2 + ((k : ℝ) * γ + a * d) * A * B) * ‖u‖ := by
    intro l hl u hu
    cases l with
    | nil => simp at hl
    | cons i l =>
      have hl' : l.length = k := by simpa using hl
      have h := step_sq X c hc a ha hs V hV k A B γ s hA0 hB0 hγ0 hγ hΔ hA hBb l hl' i u hu
      have h2 := Real.sqrt_le_sqrt h
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hQ0, Real.sqrt_sq (norm_nonneg _)] at h2
      simpa using h2
  have hle : B ≤ Real.sqrt (s ^ 2 * A ^ 2 + ((k : ℝ) * γ + a * d) * A * B) :=
    hBl _ (Real.sqrt_nonneg _) hsq
  have hB2 : B ^ 2 ≤ s ^ 2 * A ^ 2 + ((k : ℝ) * γ + a * d) * A * B := by
    have h := mul_self_le_mul_self hB0 hle
    rw [Real.mul_self_sqrt hQ0] at h
    nlinarith [h]
  have hfin := le_of_sq_le_quad A B s _ hA0 hB0 hs0 hE0 hB2
  intro l hl u hu
  exact (hBb l hl u hu).trans (mul_le_mul_of_nonneg_right hfin (norm_nonneg u))

theorem nelson_word_growth_estimate (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ)
    (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (a : ℝ) (ha : 0 ≤ a)
    (hs : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ a * ‖u‖ * ‖v‖)
    (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V)
    (γ s : ℝ) (hs0 : 0 ≤ s) (hγ0 : 0 ≤ γ)
    (hγ : ∀ j, ∑ i, ∑ m, 2 * ‖c i j m‖ ≤ γ)
    (hΔ : ∀ u ∈ V, ‖(∑ i, X i * X i) u‖ ≤ s ^ 2 * ‖u‖) (k : ℕ) :
    ∀ l : List (Fin d), l.length = k → ∀ u ∈ V,
      ‖(l.map X).prod u‖ ≤ (s + γ + a * d + 1) ^ k * k.factorial * ‖u‖ := by
  have hd0 : (0 : ℝ) ≤ a * d := mul_nonneg ha (Nat.cast_nonneg d)
  have hC0 : (0 : ℝ) ≤ s + γ + a * d + 1 := by linarith
  induction k with
  | zero =>
    intro l hl u hu
    cases l with
    | nil => simp
    | cons _ _ => simp at hl
  | succ k ih =>
    intro l hl u hu
    have hA0 : 0 ≤ (s + γ + a * d + 1) ^ k * (k.factorial : ℝ) :=
      mul_nonneg (pow_nonneg hC0 k) (Nat.cast_nonneg _)
    have h := next_word_bound X c hc a ha hs V hV k _ γ s hA0 hs0 hγ0 hγ hΔ ih l hl u hu
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg u))
    have hk : s + ((k : ℝ) * γ + a * d) ≤ ((k : ℝ) + 1) * (s + γ + a * d + 1) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg k) hs0, mul_nonneg (Nat.cast_nonneg k) hd0,
        (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    calc (s + ((k : ℝ) * γ + a * d)) * ((s + γ + a * d + 1) ^ k * (k.factorial : ℝ))
        ≤ (((k : ℝ) + 1) * (s + γ + a * d + 1)) * ((s + γ + a * d + 1) ^ k * (k.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right hk hA0
      _ = (s + γ + a * d + 1) ^ (k + 1) * (((k + 1).factorial : ℕ) : ℝ) := by
          push_cast [Nat.factorial_succ]
          ring

theorem exists_sq_bound (T : Module.End ℂ M) (V : Submodule ℂ M) [FiniteDimensional ℂ V] :
    ∃ s : ℝ, 0 ≤ s ∧ ∀ u ∈ V, ‖T u‖ ≤ s ^ 2 * ‖u‖ := by
  refine ⟨Real.sqrt ‖LinearMap.toContinuousLinearMap (T.comp V.subtype)‖, Real.sqrt_nonneg _,
    fun u hu => ?_⟩
  rw [Real.sq_sqrt (ContinuousLinearMap.opNorm_nonneg _)]
  exact (LinearMap.toContinuousLinearMap (T.comp V.subtype)).le_opNorm ⟨u, hu⟩

theorem word_growth : ∀ {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {d : ℕ} (X : Fin d → Module.End ℂ M) (c : Fin d → Fin d → Fin d → ℂ) (hc : ∀ i j, X i * X j - X j * X i = ∑ l, c i j l • X l) (a : ℝ) (ha : 0 ≤ a) (hs : ∀ i u v, |(⟪X i u, v⟫_ℂ + ⟪u, X i v⟫_ℂ).re| ≤ a * ‖u‖ * ‖v‖) (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ u ∈ V, (∑ i, X i * X i) u ∈ V), ∃ C : ℝ, 0 < C ∧ ∀ (l : List (Fin d)), ∀ u ∈ V, ‖(l.map X).prod u‖ ≤ C ^ (l.length + 1) * l.length.factorial * ‖u‖ := by
  intro M _ _ d X c hc a ha hs V _ hV
  obtain ⟨s, hs0, hΔ⟩ := exists_sq_bound (∑ i, X i * X i) V
  obtain ⟨γ, hγ0, hγ⟩ : ∃ γ : ℝ, 0 ≤ γ ∧ ∀ j, ∑ i, ∑ m, 2 * ‖c i j m‖ ≤ γ :=
    ⟨∑ j, ∑ i, ∑ m, 2 * ‖c i j m‖,
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        mul_nonneg zero_le_two (norm_nonneg _),
      fun j => Finset.single_le_sum (f := fun j => ∑ i, ∑ m, 2 * ‖c i j m‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          mul_nonneg zero_le_two (norm_nonneg _)) (Finset.mem_univ j)⟩
  have hd0 : (0 : ℝ) ≤ a * d := mul_nonneg ha (Nat.cast_nonneg d)
  refine ⟨s + γ + a * d + 1, by linarith, fun l u hu => ?_⟩
  have h := nelson_word_growth_estimate X c hc a ha hs V hV γ s hs0 hγ0 hγ hΔ l.length l rfl u hu
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg u))
  have hC1 : 1 ≤ s + γ + a * d + 1 := by linarith
  rw [pow_succ]
  exact mul_le_mul_of_nonneg_right
    (le_mul_of_one_le_right (pow_nonneg (by linarith) _) hC1) (Nat.cast_nonneg _)

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Nelson
