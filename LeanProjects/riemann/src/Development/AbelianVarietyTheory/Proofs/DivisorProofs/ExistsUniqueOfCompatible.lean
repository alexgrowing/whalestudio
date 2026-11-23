import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Limits

theorem smod_pow_iff {R : Type} [CommRing R] (a x y : R) (m : ℕ) :
    x ≡ y [SMOD (Ideal.span {a} ^ m • ⊤ : Submodule R R)] ↔ a ^ m ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem eval_eq_of_le {O σ : Type} [CommRing O] (A : ℕ → Type) [∀ n, CommRing (A n)]
    [∀ n, Algebra O (A n)] (r : ∀ n, A (n + 1) →ₐ[O] A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n)
    (hr : ∀ n f, r n (E (n + 1) f) = E n f) {n k : ℕ} (hnk : n ≤ k) (x y : MvPowerSeries σ O)
    (h : E k x = E k y) : E n x = E n y := by
  induction k, hnk using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact ih (by rw [← hr k x, ← hr k y, h])

theorem exists_unique_of_compatible : ∀ (p : ℕ) (O σ : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] [Fintype σ] (A : ℕ → Type) [∀ n, CommRing (A n)] [∀ n, Algebra O (A n)] [∀ n, IsHausdorff (Ideal.span {(p : A n)}) (A n)] (r : ∀ n, A (n + 1) →ₐ[O] A n) (y : ∀ n, σ → A n) (E : ∀ n, MvPowerSeries σ O →ₐ[O] A n), (∀ n, IsEval p (y n) (E n)) → (∀ n f, r n (E (n + 1) f) = E n f) → (∀ m N : ℕ, ∃ n, ∀ f, E n f = 0 → ∀ α : σ →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f) → (∀ f, (∀ n, E n f = 0) → f = 0) ∧ ((∀ n, Function.Surjective (E n)) → ∀ a : ∀ n, A n, (∀ n, r n (a (n + 1)) = a n) → ∃ f, ∀ n, E n f = a n) := by
  intro p O σ _ _ _ A _ _ _ r y E hev hr hker
  have hausO : IsHausdorff (Ideal.span {(p : O)}) O := inferInstance
  have precO : IsPrecomplete (Ideal.span {(p : O)}) O := inferInstance
  have hle : ∀ {n k : ℕ}, n ≤ k → ∀ x y, E k x = E k y → E n x = E n y :=
    fun hnk => eval_eq_of_le A r E hr hnk
  refine ⟨fun f hf => ?_, fun hsurj a ha => ?_⟩
  · ext α
    refine hausO.haus _ fun m => (smod_pow_iff _ _ _ _).2 ?_
    obtain ⟨n, hn⟩ := hker m (α.degree + 1)
    simpa using hn f (hf n) α (Nat.lt_succ_self _)
  · choose nk hnk using fun m => hker m m
    choose g hg using fun n => hsurj n (a n)
    set ν : ℕ → ℕ := fun m => m + ∑ j ∈ Finset.range (m + 1), nk j with hν
    have hνmono : Monotone ν := fun m m' hmm' => by
      simp only [hν]
      exact Nat.add_le_add hmm' (Finset.sum_le_sum_of_subset
        (Finset.range_mono (Nat.succ_le_succ hmm')))
    have hνk : ∀ m, nk m ≤ ν m := fun m => by
      simp only [hν]
      exact le_add_left (Finset.single_le_sum (f := nk) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 (Nat.lt_succ_self m)))
    have hνm : ∀ m, m ≤ ν m := fun m => by simp only [hν]; exact Nat.le_add_right _ _

    have hga : ∀ n k, n ≤ k → E n (g k) = a n := by
      intro n k hnk
      induction k, hnk using Nat.le_induction with
      | base => exact hg n
      | succ k hk ih =>
        rw [← ih]
        refine hle hk _ _ ?_
        rw [← hr k, hg (k + 1), ha k, hg k]

    have hKν : ∀ m k, ν m ≤ k → ∀ x, E k x = 0 → ∀ α : σ →₀ ℕ, α.degree < m →
        (p : O) ^ m ∣ coeff α x := by
      intro m k hk x hx α hα
      refine hnk m x ?_ α hα
      have := hle ((hνk m).trans hk) x 0 (by rw [hx, map_zero])
      rwa [map_zero] at this
    set h : ℕ → MvPowerSeries σ O := fun m => g (ν m) with hh
    have hD : ∀ m m', m ≤ m' → ∀ α : σ →₀ ℕ, α.degree < m →
        (p : O) ^ m ∣ coeff α (h m') - coeff α (h m) := by
      intro m m' hmm' α hα
      rw [← map_sub]
      refine hKν m (ν m) le_rfl _ ?_ α hα
      rw [map_sub, hh, hga _ _ (hνmono hmm'), hga _ _ le_rfl, sub_self]
    have hL : ∀ α : σ →₀ ℕ, ∃ L : O, ∀ j, (p : O) ^ j ∣ coeff α (h (j + (α.degree + 1))) - L := by
      intro α
      obtain ⟨L, hL⟩ := precO.prec (f := fun j => coeff α (h (j + (α.degree + 1)))) (by
        intro j j' hjj'
        rw [smod_pow_iff]
        have := hD (j + (α.degree + 1)) (j' + (α.degree + 1)) (by omega) α (by omega)
        rw [← neg_sub, dvd_neg]
        exact (pow_dvd_pow _ (by omega)).trans this)
      exact ⟨L, fun j => (smod_pow_iff _ _ _ _).1 (hL j)⟩
    choose L hLs using hL
    let f : MvPowerSeries σ O := fun α => L α
    have hf : ∀ m M (α : σ →₀ ℕ), m ≤ M → α.degree < M →
        (p : O) ^ m ∣ coeff α f - coeff α (h M) := by
      intro m M α hmM hα
      have h1 := hLs α M
      have h2 := hD M (M + (α.degree + 1)) (by omega) α hα
      have : coeff α f - coeff α (h M) =
          (coeff α (h (M + (α.degree + 1))) - coeff α (h M)) -
            (coeff α (h (M + (α.degree + 1))) - L α) := by
        show L α - _ = _; ring
      rw [this]
      exact (pow_dvd_pow _ hmM).trans (dvd_sub h2 h1)
    refine ⟨f, fun n => ?_⟩
    rw [← sub_eq_zero]
    refine IsHausdorff.haus (I := Ideal.span {(p : A n)}) inferInstance _ fun m => ?_
    rw [smod_pow_iff, sub_zero]
    obtain ⟨N₀, hN₀⟩ := (hev n).2 m
    set M := max (max m N₀) n with hM
    have hEM : E n (h M) = a n := hga _ _ ((le_max_right _ _).trans (hνm M))
    have hdiv : ∀ α : σ →₀ ℕ, α.degree < N₀ → (p : O) ^ m ∣ coeff α (f - h M) := by
      intro α hα
      rw [map_sub]
      exact hf m M α (by omega) (by omega)
    let Q : MvPowerSeries σ O := fun α =>
      if hα : α.degree < N₀ then Classical.choose (hdiv α hα) else 0
    have hR : ∀ α : σ →₀ ℕ, α.degree < N₀ →
        coeff α (f - h M - (p : O) ^ m • Q) = 0 := by
      intro α hα
      rw [map_sub, coeff_smul]
      show coeff α (f - h M) - (p : O) ^ m * (if hα : α.degree < N₀ then _ else 0) = 0
      rw [dif_pos hα, ← Classical.choose_spec (hdiv α hα), sub_self]
    have hsplit : E n f - a n = (p : A n) ^ m * E n Q + E n (f - h M - (p : O) ^ m • Q) := by
      rw [map_sub, map_sub, map_smul, hEM, Algebra.smul_def, map_pow, map_natCast]
      ring
    rw [hsplit]
    exact dvd_add (dvd_mul_right _ _) (hN₀ _ hR)

end GlobalTheory.Limits
