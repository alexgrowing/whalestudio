import Mathlib
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem det_one_add_uniformizer_smul_ne_zero {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {r : ℕ} {ϖ : O} (hϖ : Irreducible ϖ)
    (a : Matrix (Fin r) (Fin r) O) : (1 + ϖ • a).det ≠ 0 := by
  intro h
  have hres : IsLocalRing.residue O ϖ = 0 :=
    (IsLocalRing.residue_eq_zero_iff ϖ).2 ((IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit)
  have hm : (IsLocalRing.residue O).mapMatrix (1 + ϖ • a) = 1 := by
    ext i j
    simp [Matrix.one_apply, hres, apply_ite (IsLocalRing.residue O)]
  have h1 : IsLocalRing.residue O ((1 + ϖ • a).det) = 1 := by
    rw [RingHom.map_det, hm, Matrix.det_one]
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem exists_inv_integral_of_not_mem {O K : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] {ϖ : O}
    (hϖ : Irreducible ϖ) (y : K) (hy : ¬ ∃ c : O, y = algebraMap O K ϖ * algebraMap O K c) :
    ∃ u : O, algebraMap O K u * y = 1 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy ⟨0, by simp⟩
  rcases ValuationRing.isInteger_or_isInteger O y with ⟨a, ha⟩ | ⟨u, hu⟩
  · have hau : IsUnit a := by
      by_contra hna
      have hmem : a ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal a).2 hna
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
      obtain ⟨c, rfl⟩ := hmem
      exact hy ⟨c, by rw [← ha, map_mul]⟩
    obtain ⟨v, rfl⟩ := hau
    refine ⟨(v⁻¹ : Oˣ), ?_⟩
    rw [← ha, ← map_mul]
    simp
  · exact ⟨u, by rw [hu]; exact inv_mul_cancel₀ hy0⟩

theorem coset_translate_mem_of_cover (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O)
    (hϖ : Irreducible ϖ) (N : ℕ) (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : GL (Fin r) K)
    (z₀ : Matrix (Fin r ⊕ Fin t) (Fin r) O)
    (hx : x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O)
      (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z₀).map (algebraMap O K))
    (hcov : ∀ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, ∃ (g' : GL (Fin r) K)
      (z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), (x + (ϖ ^ N • z).map (algebraMap O K)) *
      (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O)
      (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K))
    (z : Matrix (Fin r ⊕ Fin t) (Fin r) O) : ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O,
      (x + (ϖ ^ N • z).map (algebraMap O K)) * (g : Matrix (Fin r) (Fin r) K) =
      ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map
        (algebraMap O K) := by
  set ι := algebraMap O K with hι
  have hsmul : ∀ (c : O) {m n : Type} (A : Matrix m n O), (c • A).map ι = c • A.map ι := by
    intro c m n A
    exact Matrix.map_smul _ _ (fun a => by simp [hι, Algebra.smul_def]) A
  have hadd : ∀ {m n : Type} (A B : Matrix m n O), (A + B).map ι = A.map ι + B.map ι :=
    fun A B => Matrix.map_add _ (map_add ι) A B
  have hrow : ∀ (A : Matrix (Fin r ⊕ Fin t) (Fin r) K) (G : Matrix (Fin r) (Fin r) K),
      (A * G).toRows₁ = A.toRows₁ * G := fun A G => rfl
  set x₁ := x.toRows₁ with hx₁

  have hinv : ∀ w : Matrix (Fin r) (Fin r) O, (x₁ + (ϖ ^ N • w).map ι).det ≠ 0 := by
    intro w
    obtain ⟨g', z', h⟩ := hcov (Matrix.fromRows w 0)
    have h1 := congrArg Matrix.toRows₁ h
    rw [hrow] at h1
    have e1 : (x + (ϖ ^ N • Matrix.fromRows w (0 : Matrix (Fin t) (Fin r) O)).map ι).toRows₁ =
        x₁ + (ϖ ^ N • w).map ι := by
      ext i j; rfl
    have e2 : Matrix.toRows₁ (((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) +
        ϖ • z').map ι) = (1 + ϖ • Matrix.toRows₁ z').map ι := by
      ext i j; rfl
    rw [e1, e2] at h1
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, show ((1 + ϖ • Matrix.toRows₁ z').map ι).det = ι (1 + ϖ • Matrix.toRows₁ z').det from
      (RingHom.map_det ι _).symm] at h2
    intro h0
    rw [h0, zero_mul] at h2
    exact det_one_add_uniformizer_smul_ne_zero hϖ _
      ((injective_iff_map_eq_zero ι).1 (IsFractionRing.injective O K) _ h2.symm)

  have hdet : IsUnit x₁.det := by
    have := hinv 0
    rw [smul_zero, Matrix.map_zero _ (map_zero ι), add_zero] at this
    exact isUnit_iff_ne_zero.2 this
  set B := x₁⁻¹ with hB
  have hxB : x₁ * B = 1 := Matrix.mul_nonsing_inv _ hdet
  have hC : ∀ i j, ∃ c : O, ι (ϖ ^ N) * B i j = ι ϖ * ι c := by
    intro i j
    by_contra hne
    obtain ⟨u, hu⟩ := exists_inv_integral_of_not_mem hϖ (ι (ϖ ^ N) * B i j) hne
    apply hinv (Matrix.single j i (-u))
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun k => B k j, ?_, ?_⟩
    · intro h0
      have := congrFun h0 i
      simp only [Pi.zero_apply] at this
      rw [this, mul_zero, mul_zero] at hu
      exact zero_ne_one hu
    · funext k
      rw [Matrix.add_mulVec]
      have h1 : Matrix.mulVec x₁ (fun k => B k j) k = (1 : Matrix (Fin r) (Fin r) K) k j := by
        rw [← hxB]; rfl
      have h2 : Matrix.mulVec ((ϖ ^ N • Matrix.single j i (-u)).map ι) (fun k => B k j) k =
          if k = j then -(ι u * (ι (ϖ ^ N) * B i j)) else 0 := by
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply]
        by_cases hk : k = j
        · subst hk
          rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb])
            (fun h => absurd (Finset.mem_univ i) h)]
          simp [Algebra.smul_def]
          ring
        · simp [hk, Ne.symm hk]
      rw [Pi.add_apply, h1, h2, hu, Matrix.one_apply]
      split_ifs <;> simp

  choose C hC' using hC
  set Cm : Matrix (Fin r) (Fin r) O := Matrix.of C with hCmdef
  have hCm : ι (ϖ ^ N) • B = ι ϖ • Cm.map ι := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hCmdef, Matrix.of_apply]
    exact hC' i j
  have hx1 : x₁ * (g : Matrix (Fin r) (Fin r) K) = (1 + ϖ • Matrix.toRows₁ z₀).map ι := by
    have h1 := congrArg Matrix.toRows₁ hx
    rw [hrow] at h1
    rw [h1]
    ext i j; rfl
  have hg : (g : Matrix (Fin r) (Fin r) K) = B * (1 + ϖ • Matrix.toRows₁ z₀).map ι := by
    rw [← hx1, ← Matrix.mul_assoc, hB, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have key : ϖ ^ N • (g : Matrix (Fin r) (Fin r) K) =
      ϖ • (Cm * (1 + ϖ • Matrix.toRows₁ z₀)).map ι := by
    rw [hg, Matrix.map_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← algebraMap_smul K (ϖ ^ N) B,
      ← algebraMap_smul K ϖ (Cm.map ι), hCm]
  refine ⟨z₀ + z * (Cm * (1 + ϖ • Matrix.toRows₁ z₀)), ?_⟩
  rw [Matrix.add_mul, hx, hsmul, Matrix.smul_mul, ← Matrix.mul_smul, key]
  simp only [hadd, hsmul, Matrix.map_mul, smul_add, add_assoc, Matrix.mul_smul]

end GlobalTheory
