import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily

noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

theorem standardHermitian_gram_posDef (σ : K →+* ℂ) {m n : ℕ} (v : Fin n → Fin m → K)
    (hv : LinearIndependent K v) :
    (Matrix.of fun i j => ∑ k, starRingEnd ℂ (σ (v i k)) * σ (v j k)).PosDef := by
  classical

  let Vt : Matrix (Fin m) (Fin n) K := Matrix.of fun k j => v j k
  let B : Matrix (Fin m) (Fin n) ℂ := Vt.map σ
  have hker : LinearMap.ker (Matrix.toLin' Vt) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro g hg
    have h0 : ∑ j, g j • v j = 0 := by
      ext k
      have := congrFun hg k
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Vt, Matrix.of_apply,
        Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    funext j
    exact Fintype.linearIndependent_iff.1 hv g h0 j
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  have hW : LinearMap.toMatrix' g * Vt = 1 := by
    rw [← LinearMap.toMatrix'_toLin' Vt, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hB : (LinearMap.toMatrix' g).map σ * B = 1 := by
    simp only [B]
    rw [← Matrix.map_mul, hW, Matrix.map_one σ (map_zero σ) (map_one σ)]
  have hinj : Function.Injective B.mulVec := by
    intro x y hxy
    have := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
    simp only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] at this
    exact this
  convert Matrix.PosDef.conjTranspose_mul_self B hinj using 1
  ext i j
  simp [Matrix.mul_apply, B, Vt]

def stdHerm (m : ℕ) : HermFam K (Fin m → K) where
  form σ x y := ∑ k, starRingEnd ℂ (σ (x k)) * σ (y k)
  add_right σ x y z := by
    simp [mul_add, Finset.sum_add_distrib]
  smul_right σ a x y := by
    simp [Finset.mul_sum, mul_left_comm]
  conj_symm σ x y := by
    simp [mul_comm]
  posDef σ n v hv := standardHermitian_gram_posDef K σ v hv

def stdLat (m : ℕ) : Submodule (𝓞 K) (Fin m → K) :=
  Submodule.span (𝓞 K) (Set.range fun i : Fin m => (Pi.single i 1 : Fin m → K))

theorem deg_stdLat (m : ℕ) : deg (stdHerm K m) (stdLat K m) = 0 := by
  classical
  have hcoe : ⇑(Pi.basisFun K (Fin m)) = fun i : Fin m => (Pi.single i 1 : Fin m → K) := by
    funext i
    simp [Pi.basisFun_apply]
  have hli : LinearIndependent K (fun i : Fin m => (Pi.single i 1 : Fin m → K)) := by
    rw [← hcoe]
    exact (Pi.basisFun K (Fin m)).linearIndependent
  have hfr : IsFrame K (stdLat K m) (fun i : Fin m => (Pi.single i 1 : Fin m → K)) := by
    refine ⟨fun i => Submodule.subset_span ⟨i, rfl⟩, hli, ?_⟩
    intro x _
    have hsp : Submodule.span K (Set.range fun i : Fin m => (Pi.single i 1 : Fin m → K)) = ⊤ := by
      rw [← hcoe]
      exact (Pi.basisFun K (Fin m)).span_eq
    rw [hsp]
    exact Submodule.mem_top
  rw [arakelovDegree_eq_degreeOfFamily (E := stdLat K m) _ (Submodule.fg_span (Set.finite_range _)) hfr]
  have hg : ∀ σ : K →+* ℂ,
      (stdHerm K m).gram σ (fun i : Fin m => (Pi.single i 1 : Fin m → K)) = 1 := by
    intro σ
    ext i j
    simp only [HermFam.gram, stdHerm, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single i]
    · by_cases h : i = j
      · subst h
        simp
      · simp [h, Pi.single_apply, Ne.symm h]
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  unfold degreeOfFamily stdLat
  simp [hg, AddSubgroup.relIndex_self]

theorem prod_norm_embeddings (a : K) :
    ∏ σ : K →+* ℂ, ‖σ a‖ = |(Algebra.norm ℚ a : ℝ)| := by
  have h := congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ a)
  simp only [norm_prod] at h
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ : K →+* ℂ => ‖σ a‖)
    (fun σ : K →ₐ[ℚ] ℂ => ‖σ a‖) (fun σ => rfl), ← h]
  simp

theorem deg_span_singleton (a : K) (ha : a ≠ 0) :
    deg (stdHerm K 1) (Submodule.span (𝓞 K) {fun _ : Fin 1 => a}) =
      -Real.log |(Algebra.norm ℚ a : ℝ)| / finrank ℚ K := by
  classical
  set x : Fin 1 → K := fun _ => a with hx
  have hx0 : x ≠ 0 := fun h => ha (congrFun h 0)
  have hli : LinearIndependent K (fun _ : Fin 1 => x) := by
    rw [linearIndependent_unique_iff]
    exact hx0
  have hrange : Set.range (fun _ : Fin 1 => x) = {x} := Set.range_const
  have hfr : IsFrame K (Submodule.span (𝓞 K) {x}) (fun _ : Fin 1 => x) := by
    refine ⟨fun _ => Submodule.subset_span rfl, hli, ?_⟩
    intro y hy
    have hle : Submodule.span (𝓞 K) {x} ≤
        (Submodule.span K (Set.range fun _ : Fin 1 => x)).restrictScalars (𝓞 K) := by
      rw [Submodule.span_le]
      rintro _ rfl
      exact Submodule.subset_span ⟨0, rfl⟩
    exact hle hy
  rw [arakelovDegree_eq_degreeOfFamily _ (Submodule.fg_span_singleton x) hfr]
  have hg : ∀ σ : K →+* ℂ, ((stdHerm K 1).gram σ (fun _ : Fin 1 => x)).det.re = ‖σ a‖ ^ 2 := by
    intro σ
    simp only [Matrix.det_unique, HermFam.gram, stdHerm, Matrix.of_apply, hx,
      Finset.univ_unique, Finset.sum_singleton]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.conj_re, Complex.conj_im]
  have hpos : ∀ σ : K →+* ℂ, ‖σ a‖ ≠ 0 := fun σ => by
    simpa using ha
  have hsum : ∑ σ : K →+* ℂ, Real.log ((stdHerm K 1).gram σ (fun _ : Fin 1 => x)).det.re =
      2 * Real.log |(Algebra.norm ℚ a : ℝ)| := by
    simp only [hg, Real.log_pow, Nat.cast_ofNat]
    rw [← Finset.mul_sum, ← Real.log_prod (fun σ _ => hpos σ), prod_norm_embeddings]
  unfold degreeOfFamily
  rw [hsum, hrange, AddSubgroup.relIndex_self]
  simp

end ReciprocityTheory.GeometryOfNumbersTheory
