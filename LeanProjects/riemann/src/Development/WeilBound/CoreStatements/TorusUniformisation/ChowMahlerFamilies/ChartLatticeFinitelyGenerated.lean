import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensExist

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

theorem PositivityTheory.Xgn.chart_lattice_finitely_generated : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)) (c : ι), x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k := by
  intro O _ Ω _ _ ι x r B c hc
  obtain ⟨k, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  choose b _ _ hiff using hb
  have hgen : ∀ l q, ∃ n : ℕ, f l ^ n • b l q ∈ B.lat c := by
    intro l q
    refine (hiff l (b l q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases h : q' = q
      · subst h
        simp [Subalgebra.one_mem]
      · simp [Pi.single_apply, h, Subalgebra.zero_mem]
    · simp [Pi.single_apply, ite_smul]
  choose nn hnn using hgen
  obtain ⟨g, hg⟩ : ∃ g : Fin k × Fin r → Fin r → Ω, g = fun p => f p.1 ^ nn p.1 p.2 • b p.1 p.2 :=
    ⟨_, rfl⟩
  have hgmem : ∀ p, g p ∈ B.lat c := by
    intro p
    rw [hg]
    exact hnn _ _
  refine ⟨k * r, fun idx => g (finProdFinEquiv.symm idx), fun idx => hgmem _, ?_⟩
  intro e he
  have hloc : ∀ l, ∃ M : ℕ, ∃ a : Fin r → Ω, (∀ q, a q ∈ chartRing O x c) ∧
      f l ^ M • e = ∑ q, a q • g (l, q) := by
    intro l
    obtain ⟨a, ha, hea⟩ := (hiff l e).1 ⟨0, by simpa using he⟩
    choose N hN using ha
    have hle : ∀ q, N q + nn l q ≤ ∑ q', (N q' + nn l q') := fun q =>
      Finset.single_le_sum (f := fun q' => N q' + nn l q') (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ q)
    refine ⟨∑ q', (N q' + nn l q'), fun q => f l ^ (∑ q', (N q' + nn l q') - nn l q) * a q, ?_, ?_⟩
    · intro q
      have h1 : ∑ q', (N q' + nn l q') - nn l q = (∑ q', (N q' + nn l q') - nn l q - N q) + N q := by
        have := hle q
        omega
      beta_reduce
      rw [h1, pow_add, mul_assoc]
      exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (hf l) _) (hN q)
    · rw [hea, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp only [hg]
      rw [smul_smul, smul_smul]
      congr 1
      rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel (by have := hle q; omega)]
  choose M a ha hMa using hloc
  have hP : ∀ l, M l ≤ ∑ l', M l' := fun l =>
    Finset.single_le_sum (f := M) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  have hunit : ∃ d : Fin k → Ω, (∀ l, d l ∈ chartRing O x c) ∧
      ∑ l, d l * f l ^ (∑ l', M l') = 1 := by
    let F : Fin k → chartRing O x c := fun l => ⟨f l, hf l⟩
    have h1 : Ideal.span (Set.range F) = ⊤ := by
      rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
      refine ⟨fun l => ⟨cc l, hcc l⟩, ?_⟩
      apply Subtype.ext
      simpa [F] using hsum
    have h2 := Ideal.span_pow_eq_top _ h1 (∑ l', M l')
    rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at h2
    obtain ⟨d, hd⟩ := h2
    refine ⟨fun l => d l, fun l => (d l).2, ?_⟩
    have := congrArg Subtype.val hd
    simpa [F] using this
  obtain ⟨d, hd, hdsum⟩ := hunit
  have key : e = ∑ p : Fin k × Fin r,
      (d p.1 * f p.1 ^ (∑ l', M l' - M p.1) * a p.1 p.2) • g p := by
    rw [Fintype.sum_prod_type]
    calc e = (∑ l, d l * f l ^ (∑ l', M l')) • e := by rw [hdsum, one_smul]
      _ = ∑ l, d l • (f l ^ (∑ l', M l' - M l) • (f l ^ M l • e)) := by
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [smul_smul, smul_smul, mul_assoc, ← pow_add, Nat.sub_add_cancel (hP l)]
      _ = _ := by
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [hMa l, Finset.smul_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl (fun q _ => ?_)
          rw [smul_smul, smul_smul]
  refine ⟨fun idx => d (finProdFinEquiv.symm idx).1 *
      f (finProdFinEquiv.symm idx).1 ^ (∑ l', M l' - M (finProdFinEquiv.symm idx).1) *
      a (finProdFinEquiv.symm idx).1 (finProdFinEquiv.symm idx).2, ?_, ?_⟩
  · intro idx
    exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hd _) (Subalgebra.pow_mem _ (hf _) _)) (ha _ _)
  · exact key.trans (Equiv.sum_comp finProdFinEquiv.symm
      (fun p => (d p.1 * f p.1 ^ (∑ l', M l' - M p.1) * a p.1 p.2) • g p)).symm
