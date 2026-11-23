import Mathlib

theorem UpperTheory.filtration_exponent_bound :
    ∀ {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module O D] [Module A D]
        [IsScalarTower O A D] (N : Submodule O D) (γ : D →ₗ[O] D) (ϖ : A) (l : O) (E e : ℕ → ℕ) (lam : ℕ → O),
        Monotone E → Monotone e → (∀ y, E y ≤ e y) →
        (∀ r : ℕ, ∃ u : Oˣ, lam (r + 1) = (u : O) * l ^ (E (r + 1) - E r)) →
        lam 0 = 0 → (∀ x ∈ N, ϖ • x ∈ N) →
        (∀ (r : ℕ), ∀ x ∈ N, ∃ x' ∈ N,
          γ (ϖ ^ r • x) - ϖ ^ r • x = lam r • (ϖ ^ r • x) + ϖ ^ (r + 1) • x') →
        ∀ w ∈ N, ∃ c : ℕ → D, c 0 = 0 ∧ (∀ y, c y ∈ N) ∧ ∀ K : ℕ, ∃ t ∈ N,
          l ^ e K • (γ w - w) - ∑ y ∈ Finset.range K, l ^ (e K - e y) •
            (γ (ϖ ^ y • (l ^ (e y - E y) • c y)) - ϖ ^ y • (l ^ (e y - E y) • c y)) = ϖ ^ K • t := by
  intro O A D _ _ _ _ _ _ _ N γ ϖ l E e lam hE he hEe hlam hlam0 hϖ hγ w hw
  choose u hu using hlam
  have hγ' : ∀ (r : ℕ) (x : N), ∃ x' : N,
      γ (ϖ ^ r • (x : D)) - ϖ ^ r • (x : D) = lam r • (ϖ ^ r • (x : D)) + ϖ ^ (r + 1) • (x' : D) := by
    intro r x
    obtain ⟨x', h1, h2⟩ := hγ r x x.2
    exact ⟨⟨x', h1⟩, h2⟩
  choose f hf using hγ'
  have h0 : γ w - w = ϖ • (f 0 ⟨w, hw⟩ : D) := by
    have := hf 0 ⟨w, hw⟩
    simpa [hlam0] using this
  let s : ℕ → N := fun K => Nat.rec (l ^ E 0 • f 0 ⟨w, hw⟩)
    (fun k sk => - f (k + 1) (((u k)⁻¹ : Oˣ).val • sk)) K
  have hs0 : s 0 = l ^ E 0 • f 0 ⟨w, hw⟩ := rfl
  have hsS : ∀ k, s (k + 1) = - f (k + 1) (((u k)⁻¹ : Oˣ).val • s k) := fun _ => rfl
  let c : ℕ → N := fun K => Nat.casesOn K 0 (fun k => ((u k)⁻¹ : Oˣ).val • s k)
  have hc0 : c 0 = 0 := rfl
  have hcS : ∀ k, c (k + 1) = ((u k)⁻¹ : Oˣ).val • s k := fun _ => rfl
  clear_value c s
  have key : ∀ K, l ^ E K • (γ w - w) - ∑ y ∈ Finset.range (K + 1), l ^ (E K - E y) •
      (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D)) = ϖ ^ (K + 1) • (s K : D) := by
    intro K
    induction K with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, hc0, hs0, h0, ZeroMemClass.coe_zero, smul_zero,
        map_zero, sub_zero, pow_one, Submodule.coe_smul]
      rw [smul_comm]
    | succ K ih =>
      have hK : E K ≤ E (K + 1) := hE (Nat.le_succ K)
      have hsum : ∑ y ∈ Finset.range (K + 1), l ^ (E (K + 1) - E y) •
          (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D)) =
          l ^ (E (K + 1) - E K) • ∑ y ∈ Finset.range (K + 1), l ^ (E K - E y) •
          (γ (ϖ ^ y • (c y : D)) - ϖ ^ y • (c y : D)) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        have hy' : E y ≤ E K := hE (Nat.lt_succ_iff.mp (Finset.mem_range.mp hy))
        rw [smul_smul, ← pow_add]
        congr 2
        omega
      have hp : l ^ E (K + 1) = l ^ (E (K + 1) - E K) * l ^ E K := by
        rw [← pow_add]
        congr 1
        omega
      have hl : lam (K + 1) • (ϖ ^ (K + 1) • (c (K + 1) : D)) =
          l ^ (E (K + 1) - E K) • (ϖ ^ (K + 1) • (s K : D)) := by
        rw [hcS, Submodule.coe_smul, smul_comm (ϖ ^ (K + 1)), smul_smul, hu]
        congr 1
        rw [mul_right_comm, Units.mul_inv, one_mul]
      rw [Finset.sum_range_succ _ (K + 1), hsum, hp, mul_smul, ← sub_sub, ← smul_sub, ih, hf, hl,
        hsS, ← hcS]
      simp
  refine ⟨fun y => (c y : D), by simp [hc0], fun y => (c y).2, fun K => ?_⟩
  cases K with
  | zero =>
    refine ⟨l ^ e 0 • (ϖ • (f 0 ⟨w, hw⟩ : D)), N.smul_mem _ (hϖ _ (f 0 ⟨w, hw⟩).2), ?_⟩
    simp [h0]
  | succ K =>
    have hK : E K ≤ e (K + 1) := (hEe K).trans (he (Nat.le_succ K))
    refine ⟨l ^ (e (K + 1) - E K) • (s K : D), N.smul_mem _ (s K).2, ?_⟩
    have hp : l ^ e (K + 1) = l ^ (e (K + 1) - E K) * l ^ E K := by
      rw [← pow_add]
      congr 1
      omega
    rw [smul_comm (ϖ ^ (K + 1)), ← key, smul_sub (l ^ (e (K + 1) - E K)), ← mul_smul, ← hp,
      Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    have hyK : y ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hy)
    have h1 : E y ≤ E K := hE hyK
    have h2 : e y ≤ e (K + 1) := he (hyK.trans (Nat.le_succ K))
    have h3 := hEe y
    rw [smul_comm (ϖ ^ y), map_smul, ← smul_sub, smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2
    omega
