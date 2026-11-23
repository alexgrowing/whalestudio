import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TorsionTotientBound

open NumberField Matrix

namespace UpperTheory.Mu

variable {K : Type} [Field K] [NumberField K]

private theorem finrank_le_sum_sq_of_isIntegral {x : K} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    (Module.finrank ℚ K : ℝ) ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  refine le_trans ?_ (GlobalTheory.finrank_mul_abs_norm_rpow_le_sum_sq x)
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    exact_mod_cast GlobalTheory.one_le_abs_norm_of_isIntegral hx h0
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow h1 (by positivity))

private theorem exists_single_of_sum_star_mul {n : ℕ} [Star K]
    (hconj : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x))
    (z : Fin n → K) (hz : ∀ i, IsIntegral ℤ (z i)) (h1 : ∑ i, star (z i) * z i = 1) :
    ∃ i, ∀ j, j ≠ i → z j = 0 := by
  have hφ : ∀ φ : K →+* ℂ, ∑ i, ‖φ (z i)‖ ^ 2 = 1 := by
    intro φ
    have h := congrArg φ h1
    rw [map_sum, map_one] at h
    have h2 : ∀ i, φ (star (z i) * z i) = ((‖φ (z i)‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [map_mul, hconj, Complex.conj_mul']
      push_cast
      rfl
    simp_rw [h2] at h
    exact_mod_cast h
  have htot : ∑ i, ∑ φ : K →+* ℂ, ‖φ (z i)‖ ^ 2 = (Module.finrank ℚ K : ℝ) := by
    rw [Finset.sum_comm]
    simp [hφ, Embeddings.card]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra hall
    push_neg at hall
    simp [hall] at h1
  refine ⟨i, fun j hji => ?_⟩
  by_contra hj
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ ∑ φ : K →+* ℂ, ‖φ (z k)‖ ^ 2 :=
    fun k _ => Finset.sum_nonneg fun _ _ => by positivity
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {i, j})
    (fun k hk _ => hnn k hk)
  rw [Finset.sum_pair (Ne.symm hji), htot] at hsub
  have := finrank_le_sum_sq_of_isIntegral (hz i) hi
  have := finrank_le_sum_sq_of_isIntegral (hz j) hj
  linarith

theorem torsionOrder_le (K : Type) [Field K] [NumberField K] : Units.torsionOrder K ≤ 2 * Module.finrank ℚ K ^ 2 :=
  Formalism.L2.SG.NGCut.TorsionTotientBound.torsionOrder_le K

theorem pow_torsionOrder_eq_one {x : K} (hx : IsIntegral ℤ x) (h : ∀ φ : K →+* ℂ, ‖φ x‖ = 1) :
    x ^ Units.torsionOrder K = 1 := by
  obtain ⟨n, hn, hxn⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ hx h
  obtain ⟨y, rfl⟩ : ∃ y : 𝓞 K, (y : K) = x := ⟨⟨x, hx⟩, rfl⟩
  have hyn : y ^ n = 1 := by
    apply RingOfIntegers.coe_injective
    simpa using hxn
  have hmem : Units.ofPowEqOne y n hyn hn.ne' ∈ Units.torsion K := by
    rw [Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, hn, Units.ext (by simpa using hyn)⟩
  rw [← Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hmem
  have := congrArg (fun v : (𝓞 K)ˣ => ((v : 𝓞 K) : K)) hmem
  simpa using this

theorem norm_eq_one_of_star_mul [Star K] (hconj : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x))
    {z : K} (h1 : star z * z = 1) (φ : K →+* ℂ) : ‖φ z‖ = 1 := by
  have h3 := congrArg φ h1
  rw [map_mul, hconj, map_one, Complex.conj_mul'] at h3
  have h4 : ‖φ z‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4

theorem exists_monomial [StarRing K] (hconj : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x))
    (n : ℕ) (g : Matrix (Fin n) (Fin n) K) (hg : gᴴ * g = 1) (hint : ∀ a b, IsIntegral ℤ (g a b)) :
    ∃ (t : Fin n → K) (σ : Equiv.Perm (Fin n)), (∀ b, t b ^ Units.torsionOrder K = 1) ∧
      g = Matrix.of fun a b => if a = σ b then t b else 0 := by
  have hcol : ∀ b, ∑ a, star (g a b) * g a b = 1 := by
    intro b
    have h := congrFun (congrFun hg b) b
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  have horth : ∀ b b', b ≠ b' → ∑ a, star (g a b) * g a b' = 0 := by
    intro b b' hbb
    have h := congrFun (congrFun hg b) b'
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_ne hbb] using h
  choose f hf using fun b => exists_single_of_sum_star_mul hconj (fun a => g a b)
    (fun a => hint a b) (hcol b)
  have hdiag : ∀ b, star (g (f b) b) * g (f b) b = 1 := by
    intro b
    have h := hcol b
    rwa [Finset.sum_eq_single (f b) (fun j _ hj => by simp [hf b j hj]) (by simp)] at h
  have hne : ∀ b, g (f b) b ≠ 0 := by
    intro b h
    have h' := hdiag b
    simp [h] at h'
  have hinj : Function.Injective f := by
    intro b b' hbb
    by_contra hb
    have h := horth b b' hb
    rw [Finset.sum_eq_single (f b) (fun j _ hj => by simp [hf b j hj]) (by simp)] at h
    rcases mul_eq_zero.mp h with h | h
    · exact hne b (star_eq_zero.mp h)
    · rw [hbb] at h
      exact hne b' h
  refine ⟨fun b => g (f b) b, Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj),
    fun b => pow_torsionOrder_eq_one (hint _ _) (norm_eq_one_of_star_mul hconj (hdiag b)), ?_⟩
  ext a b
  simp only [Matrix.of_apply, Equiv.ofBijective_apply]
  split_ifs with h
  · rw [h]
  · exact hf b a h

theorem unitary_integral_finite_and_ncard_le [StarRing K]
    (hconj : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x)) (n : ℕ) :
    {g : Matrix (Fin n) (Fin n) K | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.Finite ∧
    {g : Matrix (Fin n) (Fin n) K | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.ncard
      ≤ Units.torsionOrder K ^ n * n.factorial := by
  classical
  have hT : 0 < Units.torsionOrder K := Units.torsionOrder_pos K
  let R : Finset K := (Polynomial.nthRoots (Units.torsionOrder K) (1 : K)).toFinset
  let P : Finset ((Fin n → K) × Equiv.Perm (Fin n)) :=
    Fintype.piFinset (fun _ => R) ×ˢ Finset.univ
  let Φ : (Fin n → K) × Equiv.Perm (Fin n) → Matrix (Fin n) (Fin n) K :=
    fun p => Matrix.of fun a b => if a = p.2 b then p.1 b else 0
  have hsub : {g : Matrix (Fin n) (Fin n) K | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} ⊆
      ↑(P.image Φ) := by
    rintro g ⟨hg, hint⟩
    obtain ⟨t, σ, ht, rfl⟩ := exists_monomial hconj n g hg hint
    rw [Finset.coe_image]
    refine ⟨(t, σ), ?_, rfl⟩
    simp [P, R, Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset, Multiset.mem_toFinset,
      Polynomial.mem_nthRoots hT, ht]
  refine ⟨(P.image Φ).finite_toSet.subset hsub, ?_⟩
  calc _ ≤ (↑(P.image Φ) : Set (Matrix (Fin n) (Fin n) K)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (P.image Φ).card := Set.ncard_coe_finset _
    _ ≤ P.card := Finset.card_image_le
    _ = R.card ^ n * n.factorial := by
        simp [P, Fintype.card_piFinset, Fintype.card_perm]
    _ ≤ Units.torsionOrder K ^ n * n.factorial := by
        gcongr
        exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

end UpperTheory.Mu
