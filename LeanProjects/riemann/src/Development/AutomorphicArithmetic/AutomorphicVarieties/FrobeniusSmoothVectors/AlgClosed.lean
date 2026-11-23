import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasicOpenEqZeroOfMemIInfPowSmul

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_closed :
    ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsNoetherianRing C] [IsAdicComplete (maximalIdeal C) C] {D : Type} [CommRing D] [Algebra C D] (𝔪 : Ideal D), IsVertexRing C 𝔪 → ∀ c : ℕ → C, (∀ N, algebraMap C D (c (N + 1) - c N) ∈ 𝔪 ^ (N + 1)) → ∃ x : C, ∀ N, algebraMap C D (x - c N) ∈ 𝔪 ^ (N + 1) := by
  intro C _ _ _ _ D _ _ 𝔪 h c hc
  let J : ℕ → Ideal C := fun n => (𝔪 ^ n).comap (algebraMap C D)
  have hJ : Antitone J := fun _ _ hab => Ideal.comap_mono (Ideal.pow_le_pow_right hab)
  have h0 : ⨅ n, J n = ⊥ := by
    simp only [J]
    rw [← Ideal.comap_iInf, h.sep, ← RingHom.ker_eq_comap_bot, ← RingHom.injective_iff_ker_eq_bot]
    exact h.inj
  choose s hs using GlobalTheory.exists_le_maximalIdeal_pow_of_iInf_eq_bot J hJ h0
  have hd : ∀ N d, c (N + d) - c N ∈ J (N + 1) := fun N d => by
    induction d with
    | zero => simp
    | succ d ih =>
      have h1 : c (N + d + 1) - c (N + d) ∈ J (N + 1) := hJ (show N + 1 ≤ N + d + 1 by omega) (hc (N + d))
      have := (J (N + 1)).add_mem h1 ih
      rwa [sub_add_sub_cancel] at this
  have hle : ∀ {a b}, a ≤ b → c b - c a ∈ J (a + 1) := fun {a b} hab => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    exact hd a d
  let t : ℕ → ℕ := fun k => k + ∑ i ∈ Finset.range (k + 1), s i
  have ht : ∀ k, s k ≤ t k := fun k => by
    simp only [t, Finset.sum_range_succ]
    omega
  have ht' : ∀ k, k ≤ t k := fun k => Nat.le_add_right _ _
  have htm : Monotone t := fun a b hab =>
    Nat.add_le_add hab (Finset.sum_le_sum_of_subset (Finset.range_mono (by omega)))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal C) (fun k => c (t k)) fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
    exact hs m (hJ (by have := ht m; omega) (hle (htm hmn)))
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL
  refine ⟨L, fun N => ?_⟩
  have h1 : c (t (N + 1)) - L ∈ J (N + 1) := by
    have := hL (N + 1)
    rw [← h.comap] at this
    exact Ideal.le_comap_pow _ (N + 1) this
  have h2 : c (t (N + 1)) - c N ∈ J (N + 1) := hle (by have := ht' (N + 1); omega)
  have h3 := (J (N + 1)).sub_mem h2 h1
  rwa [sub_sub_sub_cancel_left] at h3
