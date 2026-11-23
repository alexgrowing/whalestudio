import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

namespace GlobalTheory

theorem matrix_exists_left_inverse_of_field {K : Type} [Field K] {m n : ℕ}
    (Q : Matrix (Fin m) (Fin n) K) (h : Function.Injective Q.mulVec) :
    ∃ Q' : Matrix (Fin n) (Fin m) K, Q' * Q = 1 := by
  have hk : LinearMap.ker (Matrix.toLin' Q) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    apply h
    simpa [Matrix.toLin'_apply] using hxy
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem matrix_exists_left_inverse_of_forall_field (R : Type) [CommRing R] (m n : ℕ)
    (Q : Matrix (Fin m) (Fin n) R)
    (h : ∀ (K : Type) [Field K] (φ : R →+* K), Function.Injective (Q.map φ).mulVec) :
    ∃ Q' : Matrix (Fin n) (Fin m) R, Q' * Q = 1 := by
  let I : Ideal R :=
    { carrier := {r | ∃ L : Matrix (Fin n) (Fin m) R, L * Q = r • (1 : Matrix (Fin n) (Fin n) R)}
      add_mem' := by
        rintro a b ⟨L, hL⟩ ⟨L', hL'⟩
        exact ⟨L + L', by rw [Matrix.add_mul, hL, hL', add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨L, hL⟩
        exact ⟨c • L, by rw [Matrix.smul_mul, hL, smul_smul, smul_eq_mul]⟩ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hne
    letI : Field (R ⧸ p) := Ideal.Quotient.field p
    obtain ⟨Lb, hLb⟩ := matrix_exists_left_inverse_of_field _ (h (R ⧸ p) (Ideal.Quotient.mk p))
    choose s hs using Ideal.Quotient.mk_surjective (I := p)
    let L : Matrix (Fin n) (Fin m) R := Lb.map s
    have hL : L.map (Ideal.Quotient.mk p) = Lb := by
      ext i j
      simp [L, hs]
    have hdet : Ideal.Quotient.mk p (L * Q).det = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, hL, hLb, Matrix.det_one]
    have hmem : (L * Q).det ∈ I :=
      ⟨(L * Q).adjugate * L, by rw [Matrix.mul_assoc, Matrix.adjugate_mul]⟩
    have h0 := Ideal.Quotient.eq_zero_iff_mem.2 (hIp hmem)
    rw [hdet] at h0
    exact one_ne_zero h0
  have h1 : (1 : R) ∈ I := by rw [hI]; trivial
  obtain ⟨L, hL⟩ := h1
  exact ⟨L, by rw [hL, one_smul]⟩

end GlobalTheory
