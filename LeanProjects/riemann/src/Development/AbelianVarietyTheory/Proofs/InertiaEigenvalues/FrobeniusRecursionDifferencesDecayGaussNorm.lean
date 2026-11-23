import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot

open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK.FrobDecay

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def CoeffBd (ρ b : ℝ) (f : K⟦X⟧) : Prop := ∀ m, ‖coeff m f‖ * ρ ^ m ≤ b

theorem bd_mul {ρ a b : ℝ} {f g : K⟦X⟧} (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : CoeffBd ρ a f) (hg : CoeffBd ρ b g) : CoeffBd ρ (a * b) (f * g) := fun m =>
  norm_coeff_mul_le (w := fun m => ρ ^ m) (fun n => pow_nonneg hρ n)
    (fun i j => (pow_add ρ i j).le) ha hb hf hg m

theorem bd_add {ρ b : ℝ} {f g : K⟦X⟧} (hρ : 0 ≤ ρ) (hf : CoeffBd ρ b f) (hg : CoeffBd ρ b g) :
    CoeffBd ρ b (f + g) := fun m =>
  (norm_coeff_add_le (w := fun m => ρ ^ m) (fun n => pow_nonneg hρ n) f g m).trans
    (max_le (hf m) (hg m))

theorem bd_zero {ρ b : ℝ} (hb : 0 ≤ b) : CoeffBd ρ b (0 : K⟦X⟧) := fun m => by simp [hb]

theorem bd_sum {α : Type} (s : Finset α) (f : α → K⟦X⟧) {ρ b : ℝ} (hρ : 0 ≤ ρ) (hb : 0 ≤ b)
    (h : ∀ i ∈ s, CoeffBd ρ b (f i)) : CoeffBd ρ b (∑ i ∈ s, f i) :=
  Finset.sum_induction f (CoeffBd ρ b) (fun _ _ => bd_add hρ) (bd_zero hb) h

theorem bd_C {ρ : ℝ} (x : K) : CoeffBd ρ ‖x‖ (C x) := fun m => by
  rw [coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

theorem bd_le {ρ b b' : ℝ} {f : K⟦X⟧} (hbb : b ≤ b') (hf : CoeffBd ρ b f) : CoeffBd ρ b' f :=
  fun m => (hf m).trans hbb

theorem bd_mono {ρ ρ' b : ℝ} {f : K⟦X⟧} (hρ : 0 ≤ ρ') (h : ρ' ≤ ρ) (hf : CoeffBd ρ b f) :
    CoeffBd ρ' b f := fun m =>
  (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ h m) (norm_nonneg _)).trans (hf m)

theorem bd_frob (l : ℕ) [Fact l.Prime] {ρ b : ℝ} {f : K⟦X⟧} (hb : 0 ≤ b)
    (hf : CoeffBd (ρ ^ l) b f) : CoeffBd ρ b (frob K l f) := fun m => by
  rw [coeff_frob]
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Fact.out : l.Prime).pos, pow_mul]
    exact hf q
  · simpa using hb

theorem bd_of_coeff_zero {r ρ N : ℝ} {f : K⟦X⟧} (hr : 0 < r) (hρ : 0 ≤ ρ) (hρr : ρ ≤ r)
    (hf : CoeffBd r N f) (h0 : coeff 0 f = 0) : CoeffBd ρ (N / r * ρ) f := fun m => by
  have hN : 0 ≤ N := (mul_nonneg (norm_nonneg _) (pow_nonneg hr.le 0)).trans (hf 0)
  cases m with
  | zero => simpa [h0] using mul_nonneg (div_nonneg hN hr.le) hρ
  | succ m =>
    have key : ρ ^ (m + 1) * r ≤ r ^ (m + 1) * ρ := by
      have h1 := pow_le_pow_left₀ hρ hρr m
      calc ρ ^ (m + 1) * r = ρ ^ m * (ρ * r) := by ring
        _ ≤ r ^ m * (ρ * r) := mul_le_mul_of_nonneg_right h1 (mul_nonneg hρ hr.le)
        _ = r ^ (m + 1) * ρ := by ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    calc ‖coeff (m + 1) f‖ * ρ ^ (m + 1) * r = ‖coeff (m + 1) f‖ * (ρ ^ (m + 1) * r) := by ring
      _ ≤ ‖coeff (m + 1) f‖ * (r ^ (m + 1) * ρ) := mul_le_mul_of_nonneg_left key (norm_nonneg _)
      _ = (‖coeff (m + 1) f‖ * r ^ (m + 1)) * ρ := by ring
      _ ≤ N * ρ := mul_le_mul_of_nonneg_right (hf _) hρ

end GlobalTheory.BK.FrobDecay

open GlobalTheory.BK.FrobDecay

theorem GlobalTheory.BK.frob_recursion_decay : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l a : ℕ) [Fact l.Prime] [NeZero a] (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℝ), 0 < k → ∀ (B : ZMod a → Matrix ι ι K⟦X⟧) (c : ZMod a → Matrix ι ι K) (Z : ℕ → ZMod a → Matrix ι ι K⟦X⟧), (∀ τ i j, B τ i j ∈ R O K l k) → (∀ τ, Z 0 τ = (c τ).map C) → (∀ n τ, Z (n + 1) τ = B τ * (Z n (τ - 1)).map (frob K l) * (c τ).map C) → (∀ τ i j, (X : K⟦X⟧) ∣ Z 1 τ i j - Z 0 τ i j) → ∃ M β : ℝ, 0 ≤ β ∧ ∀ n τ i j, Z n τ i j ∈ R O K l k ∧ normR l k (Z (n + 1) τ i j - Z n τ i j) ≤ M * β ^ n * rad l k ^ (l ^ n) := by
  intro O K _ _ _ _ _ l a _ _ ι _ _ k hk B c Z hB h0 hrec hX
  have hr : 0 < rad l k := rad_pos l k
  have hr1 : rad l k ≤ 1 := rad_le_one l hk.le
  have hmem : ∀ n τ i j, Z n τ i j ∈ R O K l k := by
    intro n
    induction n with
    | zero =>
      intro τ i j
      rw [h0, Matrix.map_apply]
      exact HasK.C_mem _
    | succ n ih =>
      intro τ i j
      rw [hrec, Matrix.mul_apply]
      refine Subalgebra.sum_mem _ fun q _ => mul_mem ?_ (by rw [Matrix.map_apply]; exact HasK.C_mem _)
      rw [Matrix.mul_apply]
      exact Subalgebra.sum_mem _ fun p _ => mul_mem (hB _ _ _)
        (by rw [Matrix.map_apply]; exact frob_mem_R l hk.le (ih _ _ _))
  have hnn : ∀ f ∈ R O K l k, 0 ≤ normR l k f := fun f hf =>
    (mul_nonneg (norm_nonneg _) (pow_nonneg hr.le 0)).trans (le_normR hf 0)
  let D : ℕ → ZMod a → Matrix ι ι K⟦X⟧ := fun n τ => Z (n + 1) τ - Z n τ
  have hD : ∀ n τ i j, D (n + 1) τ i j =
      ∑ q, (∑ p, B τ i p * frob K l (D n (τ - 1) p q)) * C (c τ q j) := by
    intro n τ i j
    simp only [D, Matrix.sub_apply]
    rw [hrec (n + 1) τ, hrec n τ]
    simp only [Matrix.mul_apply, Matrix.map_apply, ← Finset.sum_sub_distrib, ← sub_mul, ← mul_sub,
      map_sub, Matrix.sub_apply]
  obtain ⟨β, hβ0, hBbd⟩ : ∃ β : ℝ, 0 ≤ β ∧ ∀ τ i j, CoeffBd (rad l k) β (B τ i j) :=
    ⟨∑ x : ZMod a × ι × ι, normR l k (B x.1 x.2.1 x.2.2),
      Finset.sum_nonneg fun x _ => hnn _ (hB _ _ _), fun τ i j m =>
      (le_normR (hB τ i j) m).trans (Finset.single_le_sum
        (f := fun x : ZMod a × ι × ι => normR l k (B x.1 x.2.1 x.2.2))
        (fun x _ => hnn _ (hB _ _ _)) (Finset.mem_univ (τ, i, j)))⟩
  obtain ⟨γ, hγ0, hcbd⟩ : ∃ γ : ℝ, 0 ≤ γ ∧ ∀ τ i j, ‖c τ i j‖ ≤ γ :=
    ⟨∑ x : ZMod a × ι × ι, ‖c x.1 x.2.1 x.2.2‖, Finset.sum_nonneg fun x _ => norm_nonneg _,
      fun τ i j => Finset.single_le_sum (f := fun x : ZMod a × ι × ι => ‖c x.1 x.2.1 x.2.2‖)
        (fun x _ => norm_nonneg _) (Finset.mem_univ (τ, i, j))⟩
  have hD0mem : ∀ τ i j, D 0 τ i j ∈ R O K l k := fun τ i j =>
    sub_mem (hmem 1 τ i j) (hmem 0 τ i j)
  obtain ⟨N, hN0, hNbd⟩ : ∃ N : ℝ, 0 ≤ N ∧ ∀ τ i j, CoeffBd (rad l k) N (D 0 τ i j) :=
    ⟨∑ x : ZMod a × ι × ι, normR l k (D 0 x.1 x.2.1 x.2.2),
      Finset.sum_nonneg fun x _ => hnn _ (hD0mem _ _ _), fun τ i j m =>
      (le_normR (hD0mem τ i j) m).trans (Finset.single_le_sum
        (f := fun x : ZMod a × ι × ι => normR l k (D 0 x.1 x.2.1 x.2.2))
        (fun x _ => hnn _ (hD0mem _ _ _)) (Finset.mem_univ (τ, i, j)))⟩
  have key : ∀ n, ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ rad l k → ∀ τ i j,
      CoeffBd ρ (N / rad l k * (β * γ) ^ n * ρ ^ (l ^ n)) (D n τ i j) := by
    intro n
    induction n with
    | zero =>
      intro ρ hρ hρr τ i j
      simp only [pow_zero, mul_one, pow_one]
      refine bd_of_coeff_zero hr hρ hρr (hNbd τ i j) ?_
      rw [coeff_zero_eq_constantCoeff_apply]
      exact X_dvd_iff.1 (hX τ i j)
    | succ n ih =>
      intro ρ hρ hρr τ i j
      rw [hD]
      have hρl : ρ ^ l ≤ rad l k :=
        (pow_le_of_le_one hρ (hρr.trans hr1) (Fact.out : l.Prime).ne_zero).trans hρr
      have hM0 : 0 ≤ N / rad l k * (β * γ) ^ n * (ρ ^ l) ^ (l ^ n) :=
        mul_nonneg (mul_nonneg (div_nonneg hN0 hr.le) (pow_nonneg (mul_nonneg hβ0 hγ0) _))
          (pow_nonneg (pow_nonneg hρ _) _)
      have bnd : N / rad l k * (β * γ) ^ (n + 1) * ρ ^ (l ^ (n + 1)) =
          (β * (N / rad l k * (β * γ) ^ n * (ρ ^ l) ^ (l ^ n))) * γ := by
        rw [← pow_mul, ← pow_succ']
        ring
      rw [bnd]
      refine bd_sum _ _ hρ (mul_nonneg (mul_nonneg hβ0 hM0) hγ0) fun q _ =>
        bd_mul hρ (mul_nonneg hβ0 hM0) hγ0 ?_ (bd_le (hcbd τ q j) (bd_C (c τ q j)))
      exact bd_sum _ _ hρ (mul_nonneg hβ0 hM0) fun p _ =>
        bd_mul hρ hβ0 hM0 (bd_mono hρ hρr (hBbd τ i p))
          (bd_frob l hM0 (ih (ρ ^ l) (pow_nonneg hρ _) hρl (τ - 1) p q))
  refine ⟨N / rad l k, β * γ, mul_nonneg hβ0 hγ0, fun n τ i j => ⟨hmem n τ i j, ?_⟩⟩
  exact ciSup_le fun m => key n (rad l k) hr.le le_rfl τ i j m
