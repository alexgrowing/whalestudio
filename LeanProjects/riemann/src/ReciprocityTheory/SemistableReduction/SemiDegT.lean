import ReciprocityTheory.SemistableReduction.SemiDegG

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def matLin {K : Type} [Field K] [NumberField K] {r : ℕ} (Q : Matrix (Fin r) (Fin r) K) :
    (Fin r → K) →ₗ[𝓞 K] (Fin r → K) :=
  (Matrix.mulVecLin Q).restrictScalars (𝓞 K)

theorem matLin_apply {K : Type} [Field K] [NumberField K] {r : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (x : Fin r → K) : matLin Q x = Q *ᵥ x := rfl

theorem matLin_injective {K : Type} [Field K] [NumberField K] {r : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (hQ : Q.det ≠ 0) : Function.Injective (matLin Q) := by
  intro x y hxy
  rw [matLin_apply, matLin_apply] at hxy
  have hu : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).2 (isUnit_iff_ne_zero.2 hQ)
  exact (Matrix.mulVec_injective_iff_isUnit.2 hu) hxy

theorem span_mulVec {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (b : Fin k → Fin r → K) :
    Submodule.span (𝓞 K) (Set.range fun i => Q *ᵥ b i) =
      (Submodule.span (𝓞 K) (Set.range b)).map (matLin Q) := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem latDeg_transport {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (D : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (Q : Matrix (Fin r) (Fin r) K) (hQ : Q.det ≠ 0)
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) :
    latDeg (fun σ => (Q.map σ)ᴴ * D σ * Q.map σ) B b =
      latDeg D (B.map (matLin Q)) (fun i => Q *ᵥ b i) := by
  unfold latDeg
  have hinj : Function.Injective (matLin Q) := matLin_injective Q hQ
  have h1 : (Submodule.span (𝓞 K) (Set.range fun i => Q *ᵥ b i)).toAddSubgroup.relIndex
      (B.map (matLin Q)).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup := by
    rw [span_mulVec, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hemb : ∀ (σ : K →+* ℂ) (x : Fin r → K), embVec σ (Q *ᵥ x) = Q.map σ *ᵥ embVec σ x := by
    intro σ x
    funext a
    exact RingHom.map_mulVec σ Q x a
  have h2 : ∀ σ : K →+* ℂ, gramC ((Q.map σ)ᴴ * D σ * Q.map σ) σ b = gramC (D σ) σ (fun i => Q *ᵥ b i) := by
    intro σ
    ext i j
    simp only [gramC, Matrix.of_apply, hemb]
    simp only [← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]
  rw [h1]
  simp only [h2]

theorem kBasisIn_map {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (hQ : Q.det ≠ 0) (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) (hb : IsKBasisIn B b) :
    IsKBasisIn (B.map (matLin Q)) (fun i => Q *ᵥ b i) := by
  obtain ⟨h1, h2, h3⟩ := hb
  have hinj : Function.Injective (Matrix.mulVecLin Q) := fun x y h => matLin_injective Q hQ h
  refine ⟨fun i => ⟨b i, h1 i, rfl⟩, ?_, ?_⟩
  · have e : (fun i => Q *ᵥ b i) = (Matrix.mulVecLin Q) ∘ b := rfl
    rw [e]
    exact h2.map' _ (LinearMap.ker_eq_bot.2 hinj)
  · rintro x ⟨y, hy, rfl⟩
    have h4 := Submodule.mem_map_of_mem (f := Matrix.mulVecLin Q) (h3 y hy)
    rw [Submodule.map_span, ← Set.range_comp] at h4
    exact h4

def formM {K : Type} [Field K] {r : ℕ} (c : K →+* K) (M : Matrix (Fin r) (Fin r) K)
    (x y : Fin r → K) : K :=
  (fun a => c (x a)) ⬝ᵥ (M *ᵥ y)

theorem hermForm_h_eq {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.h x y = formM S.c S.G x y := by
  unfold HermForm.h formM
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem formM_change {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (x y : Fin r → K) :
    formM S.c ((P.map S.c)ᵀ * S.G * P) x y = S.h (P *ᵥ x) (P *ᵥ y) := by
  rw [hermForm_h_eq]
  unfold formM
  have e1 : (fun a => S.c ((P *ᵥ x) a)) = (P.map S.c) *ᵥ (fun a => S.c (x a)) := by
    funext a
    exact RingHom.map_mulVec S.c P x a
  rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem formM_witt {K : Type} [Field K] {r : ℕ} (c : K →+* K) (m : ℕ) (g : Fin r → K)
    (x y : Fin r → K) :
    formM c (wittMat r m g) x y = ∑ a, c (x a) * (wVal r m g a * y (wPart r m a)) := by
  unfold formM
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  have ha := a.isLt
  by_cases h : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m
  · have hw : wVal r m g a = 1 := if_pos h
    have hp : wPart r m a = Fin.rev a := if_pos h
    rw [hw, hp, one_mul, Finset.sum_eq_single (Fin.rev a)]
    · rw [wittMat, Matrix.of_apply, if_pos, one_mul]
      rw [Fin.val_rev]
      omega
    · intro j _ hj
      rw [wittMat, Matrix.of_apply, if_neg, if_neg, zero_mul]
      · rintro ⟨rfl, h2, h3⟩
        omega
      · rintro ⟨h1, -⟩
        apply hj
        ext
        rw [Fin.val_rev]
        omega
    · simp
  · have hw : wVal r m g a = g a := if_neg h
    have hp : wPart r m a = a := if_neg h
    rw [hw, hp, Finset.sum_eq_single a]
    · rw [wittMat, Matrix.of_apply, if_neg, if_pos ⟨rfl, by omega, by omega⟩]
      omega
    · intro j _ hj
      rw [wittMat, Matrix.of_apply, if_neg, if_neg, zero_mul]
      · rintro ⟨rfl, -⟩
        exact hj rfl
      · have hj' := j.isLt
        omega
    · simp

end ReciprocityTheory.MultiplicativeHeights.SemiPt
