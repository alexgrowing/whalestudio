import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL.Bruhat

variable {F : Type} [Field F] {n : ℕ}

theorem perm_eq_of_le (τ : Equiv.Perm (Fin n)) (h : ∀ b, τ b ≤ b) (b : Fin n) : τ b = b := by
  have hs : ∑ i : Fin n, (τ i : ℕ) = ∑ i : Fin n, (i : ℕ) := Equiv.sum_comp τ (fun i => (i : ℕ))
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun i : Fin n => (τ i : ℕ))
    (g := fun i : Fin n => (i : ℕ)) (fun i _ => h i)).1 hs b (Finset.mem_univ b)
  exact Fin.ext this

def mono (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun a c => if a = m.1 c then (m.2 c : F) else 0

theorem mul_mono (A : Matrix (Fin n) (Fin n) F) (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) (a c : Fin n) :
    (A * mono m) a c = A a (m.1 c) * m.2 c := by
  simp [mono, Matrix.mul_apply]

theorem mono_mul (A : Matrix (Fin n) (Fin n) F) (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) (a c : Fin n) :
    (mono m * A) a c = m.2 (m.1.symm a) * A (m.1.symm a) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (m.1.symm a)]
  · simp [mono]
  · intro k _ hk
    have : a ≠ m.1 k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
    simp [mono, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mono_unique {m m' : Equiv.Perm (Fin n) × (Fin n → Fˣ)} {u u' : GL (Fin n) F} (hu : u ∈ unip F n)
    (hu' : u' ∈ unip F n)
    (h : (u : Matrix (Fin n) (Fin n) F) * mono m = mono m' * (u' : Matrix (Fin n) (Fin n) F)) : m = m' := by
  have key : ∀ b, (m.2 b : F) = m'.2 (m'.1.symm (m.1 b)) *
      (u' : Matrix (Fin n) (Fin n) F) (m'.1.symm (m.1 b)) b := by
    intro b
    have h1 := congrFun (congrFun h (m.1 b)) b
    rwa [mul_mono, mono_mul, unip_diag hu, one_mul] at h1
  have hle : ∀ b, (m.1.trans m'.1.symm) b ≤ b := by
    intro b
    by_contra hlt
    have hlt' : b < m'.1.symm (m.1 b) := not_le.1 hlt
    apply (m.2 b).ne_zero
    rw [key b, unip_lower hu' hlt', mul_zero]
  have hfix : ∀ b, m'.1.symm (m.1 b) = b := fun b => perm_eq_of_le _ hle b
  refine Prod.ext (Equiv.ext fun b => ?_) (funext fun b => Units.ext ?_)
  · have := congrArg m'.1 (hfix b)
    rwa [Equiv.apply_symm_apply] at this
  · rw [key b, hfix b, unip_diag hu', mul_one]

theorem mem_unip_of {A : Matrix (Fin n) (Fin n) F} (hl : ∀ i j, j < i → A i j = 0) (hd : ∀ i, A i i = 1) :
    ∃ u ∈ unip F n, (u : Matrix (Fin n) (Fin n) F) = A := by
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hl i j hij)]
    simp [hd]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, ⟨fun i j hij => hl i j hij, hd⟩, rfl⟩

theorem exists_col_reduced (g : GL (Fin n) F) :
    ∃ u ∈ unip F n, ∃ σ : Equiv.Perm (Fin n),
      (∀ c, ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (σ c) c ≠ 0) ∧
      ∀ a c, σ c < a → ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0 := by
  classical
  let P : ℕ → Prop := fun N => ∃ u ∈ unip F n, ∃ f : Fin n → ℕ, ∑ c, f c = N ∧
    ∀ a c : Fin n, f c ≤ a.val → ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0
  have hex : ∃ N, P N := ⟨_, 1, Subgroup.one_mem _, fun _ => n, rfl,
    fun a c h => absurd a.2 (not_lt.2 h)⟩
  obtain ⟨u, hu, f, hf, hz⟩ := Nat.find_spec hex
  have hpos : ∀ c, 0 < f c := by
    intro c
    by_contra h0
    have h1 : (((g * u)⁻¹ * (g * u) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) c c = 1 := by
      rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      rw [hz k c (by omega), mul_zero]
  have hmin : ∀ v ∈ unip F n,
      (∀ a c : Fin n, f c ≤ a.val → ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0) →
      ∀ c, ∃ a : Fin n, a.val + 1 = f c ∧ ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c ≠ 0 := by
    intro v hv hzv c
    by_contra hcon
    push_neg at hcon
    have hlt : ∑ k, Function.update f c (f c - 1) k < Nat.find hex := by
      rw [← hf]
      refine Finset.sum_lt_sum (fun k _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩
      · by_cases hk : k = c
        · subst hk; simp
        · rw [Function.update_of_ne hk]
      · have := hpos c
        rw [Function.update_self]; omega
    refine Nat.find_min hex hlt ⟨v, hv, _, rfl, fun a k hk => ?_⟩
    by_cases hkc : k = c
    · subst hkc
      rw [Function.update_self] at hk
      by_cases h2 : f k ≤ a.val
      · exact hzv a k h2
      · exact hcon a (by omega)
    · rw [Function.update_of_ne hkc] at hk
      exact hzv a k hk
  choose s hs hsne using hmin u hu hz
  have hinj : ∀ k c, k < c → s k ≠ s c := by
    intro k c hkc he
    have hfe : f k = f c := by rw [← hs k, ← hs c, he]
    set H := ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hH
    obtain ⟨t, ht, htv⟩ := mem_unip_of (A := Matrix.transvection k c (-(H (s c) c / H (s c) k)))
      (fun i j hij => by
        have h1 : ¬ (k = i ∧ c = j) := by
          rintro ⟨rfl, rfl⟩; exact absurd hkc (not_lt.2 hij.le)
        simp [Matrix.transvection, Matrix.one_apply_ne (ne_of_gt hij), Matrix.single_apply, h1])
      (fun i => by
        have h1 : ¬ (k = i ∧ c = i) := by
          rintro ⟨rfl, h⟩; exact absurd h (ne_of_gt hkc)
        simp [Matrix.transvection, Matrix.single_apply, h1])
    have hval : ((g * (u * t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        H * Matrix.transvection k c (-(H (s c) c / H (s c) k)) := by
      rw [← mul_assoc, Units.val_mul, htv]
    obtain ⟨a, ha, hane⟩ := hmin (u * t) (Subgroup.mul_mem _ hu ht) (fun a j hj => by
      rw [hval]
      by_cases hjc : j = c
      · subst hjc
        rw [Matrix.mul_transvection_apply_same, hz a j hj, hz a k (hfe ▸ hj)]
        simp
      · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hjc]
        exact hz a j hj) c
    have hac : a = s c := Fin.ext (by have := hs c; omega)
    apply hane
    have hk0 : H (s c) k ≠ 0 := he ▸ hsne k
    rw [hval, Matrix.mul_transvection_apply_same, hac]
    field_simp
    ring
  have hinj' : Function.Injective s := by
    intro k c he
    rcases lt_trichotomy k c with h | h | h
    · exact absurd he (hinj k c h)
    · exact h
    · exact absurd he.symm (hinj c k h)
  refine ⟨u, hu, Equiv.ofBijective s (Finite.injective_iff_bijective.1 hinj'), hsne, fun a c h => hz a c ?_⟩
  have h1 : (s c).val < a.val := h
  have := hs c
  omega

theorem exists_decomp (g : GL (Fin n) F) : ∃ m : Equiv.Perm (Fin n) × (Fin n → Fˣ), ∃ u ∈ unip F n, ∃ u' ∈ unip F n,
    (g : Matrix (Fin n) (Fin n) F) = (u : Matrix (Fin n) (Fin n) F) * mono m * (u' : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨v, hv, σ, hne, hz⟩ := exists_col_reduced g
  set H := ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hH
  obtain ⟨u, hu, huv⟩ := mem_unip_of (A := Matrix.of fun a b => H a (σ.symm b) / H b (σ.symm b))
    (fun i j hij => by
      rw [Matrix.of_apply, hz i _ (by simpa using hij), zero_div])
    (fun i => by
      have := hne (σ.symm i)
      rw [Equiv.apply_symm_apply] at this
      rw [Matrix.of_apply, div_self this])
  refine ⟨(σ, fun c => Units.mk0 _ (hne c)), u, hu, v⁻¹, Subgroup.inv_mem _ hv, ?_⟩
  have h1 : (u : Matrix (Fin n) (Fin n) F) * mono (σ, fun c => Units.mk0 _ (hne c)) = H := by
    ext a c
    rw [mul_mono, huv]
    simp [div_mul_cancel₀ _ (hne c)]
  rw [h1, hH, ← Units.val_mul, mul_inv_cancel_right]

theorem bruhat : ∀ (F : Type) [Field F] (n : ℕ) (g : GL (Fin n) F), ∃! m : Equiv.Perm (Fin n) × (Fin n → Fˣ), ∃ u ∈ unip F n, ∃ u' ∈ unip F n, (g : Matrix (Fin n) (Fin n) F) = (u : Matrix (Fin n) (Fin n) F) * (Matrix.of fun a c => if a = m.1 c then (m.2 c : F) else 0) * (u' : Matrix (Fin n) (Fin n) F) := by
  intro F _ n g
  obtain ⟨m, u, hu, u', hu', h⟩ := exists_decomp g
  refine ⟨m, ⟨u, hu, u', hu', h⟩, ?_⟩
  rintro m' ⟨v, hv, v', hv', h'⟩
  have h2 : (v : Matrix (Fin n) (Fin n) F) * mono m' * v' = u * mono m * u' := h'.symm.trans h
  refine mono_unique (u := u⁻¹ * v) (u' := u' * v'⁻¹) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hv)
    (Subgroup.mul_mem _ hu' (Subgroup.inv_mem _ hv')) ?_
  have h3 := congrArg (fun X => ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X *
    ((v'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) h2
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.inv_mul_cancel_left] at h3
  simp only [Units.val_mul, Matrix.mul_assoc]
  exact h3

end GlobalTheory.FinGL.Bruhat
