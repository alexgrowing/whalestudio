import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

noncomputable section

namespace UpperTheory.Gal.crystallineComparison

theorem normEx_of : MatRep → DetSplit → NormEx := by
  intro hMR hDS R S _ _ _ _ _ ι _ s
  obtain ⟨m, M, hM⟩ := hMR R S
  let φ : R →+* Polynomial (MvPolynomial ι R) := Polynomial.C.comp MvPolynomial.C
  refine ⟨(1 - (M 1).map φ + (Polynomial.X : Polynomial (MvPolynomial ι R)) • (M 1).map φ
    - ∑ k, (Polynomial.C (MvPolynomial.X (R := R) k) : Polynomial (MvPolynomial ι R)) • (M (s k)).map φ).det, ?_⟩
  intro B _ _ I _ z hz
  classical
  obtain ⟨P, Q, hPQ, hQ⟩ := hM B I z hz
  let ψ : B →+* Polynomial (MvPolynomial ι B) := Polynomial.C.comp MvPolynomial.C
  let F : Polynomial (MvPolynomial ι R) →+* Polynomial (MvPolynomial ι B) :=
    Polynomial.mapRingHom (MvPolynomial.map (algebraMap R B))
  have hPQ' : P.map ψ * Q.map ψ = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one ψ (map_zero _) (map_one _)]
  have key := hDS (Polynomial (MvPolynomial ι B)) m I (P.map ψ) (Q.map ψ) hPQ'
    (fun i => form fun k => z i (s k))
  rw [← key]
  have hmap : ∀ t : S, ((M t).map φ).map F = Q.map ψ * (Matrix.diagonal fun i => z i t).map ψ * P.map ψ := by
    intro t
    have : ((M t).map φ).map F = ((M t).map (algebraMap R B)).map ψ := by
      rw [Matrix.map_map, Matrix.map_map]
      congr 1
      funext r
      simp [φ, ψ, F]
    rw [this, hQ t, Matrix.map_mul, Matrix.map_mul]
  have hd : Matrix.diagonal (fun i => form fun k => z i (s k))
      = (Polynomial.X : Polynomial (MvPolynomial ι B)) • (1 : Matrix I I _)
        - ∑ k, (Polynomial.C (MvPolynomial.X (R := B) k) : Polynomial (MvPolynomial ι B))
          • (Matrix.diagonal fun i => z i (s k)).map ψ := by
    ext i j
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · subst h
      simp [form, ψ, map_sum, mul_comm]
    · simp
  have hs : ∀ (c : Polynomial (MvPolynomial ι R)) (A : Matrix (Fin m) (Fin m) (Polynomial (MvPolynomial ι R))),
      F.mapMatrix (c • A) = F c • F.mapMatrix A := by
    intro c A
    ext i j
    simp
  have h1 : (Matrix.diagonal fun i => z i 1).map ψ = 1 := by
    simp
  change F _ = _
  rw [RingHom.map_det]
  congr 1
  rw [map_sub, map_add, map_sub, map_one, map_sum]
  simp only [hs, RingHom.mapMatrix_apply, hmap, h1, Matrix.mul_one]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_sum,
    Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  simp [F]
  abel

end UpperTheory.Gal.crystallineComparison
