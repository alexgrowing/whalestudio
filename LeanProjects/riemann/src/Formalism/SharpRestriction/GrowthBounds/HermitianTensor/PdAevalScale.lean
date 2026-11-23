import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsPAlt

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

variable (A : Type) [CommRing A] (r : ℕ)

def pdW : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) A) := fun i j => if i = j.rev then 1 else 0

def pdZ : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) A) := fun i j => (genY A r).adjugate j.rev i

theorem mul_pdW_apply_eq_apply_rev (M : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin r) A)) (i j : Fin r) :
    (M * pdW A r) i j = M i j.rev := by
  simp [pdW, Matrix.mul_apply]

theorem pdZ_eq : pdZ A r = (genY A r).adjugate.transpose * pdW A r := by
  ext i j
  rw [mul_pdW_apply_eq_apply_rev]
  rfl

theorem pdW_transpose : (pdW A r).transpose = pdW A r := by
  ext i j
  simp only [Matrix.transpose_apply, pdW]
  by_cases h : i = j.rev
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    rw [h', Fin.rev_rev]

theorem pdW_sq : pdW A r * pdW A r = 1 := by
  ext i j
  rw [mul_pdW_apply_eq_apply_rev]
  simp [pdW, Matrix.one_apply]

theorem pdW_det_sq : (pdW A r).det * (pdW A r).det = 1 := by
  rw [← Matrix.det_mul, pdW_sq, Matrix.det_one]

theorem cofY_mapMatrix : (cofY A r).mapMatrix (genY A r) = pdZ A r := by
  ext i j
  simp [cofY, genY, pdZ, AlgHom.mapMatrix_apply, aeval_X]

theorem detY_eq : detY A r = (genY A r).det := rfl

theorem pd_cof_det : cofY A r (detY A r) = (pdW A r).det * detY A r ^ (r - 1) := by
  rw [detY_eq]
  have h1 : cofY A r (genY A r).det = ((cofY A r).mapMatrix (genY A r)).det :=
    RingHom.map_det (cofY A r).toRingHom (genY A r)
  rw [h1, cofY_mapMatrix, pdZ_eq, Matrix.det_mul, Matrix.det_transpose, Matrix.det_adjugate,
    Fintype.card_fin]
  ring

theorem pd_ZZ : (genY A r).det • (cofY A r).mapMatrix (pdZ A r) =
    ((pdW A r).det * (genY A r).det ^ (r - 1)) • genY A r := by
  have hWW := pdW_sq A r
  have hWT := pdW_transpose A r
  have hadjW : (pdW A r).adjugate = (pdW A r).det • pdW A r := by
    calc (pdW A r).adjugate = (pdW A r).adjugate * (pdW A r * pdW A r) := by
          rw [hWW, Matrix.mul_one]
      _ = ((pdW A r).adjugate * pdW A r) * pdW A r := by rw [Matrix.mul_assoc]
      _ = (pdW A r).det • pdW A r := by rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hmapW : (pdW A r).map (cofY A r) = pdW A r := by
    ext i j
    simp only [Matrix.map_apply, pdW]
    split_ifs <;> simp
  have hmap : (cofY A r).mapMatrix (pdZ A r) = (pdZ A r).adjugate.transpose * pdW A r := by
    conv_lhs => rw [pdZ_eq]
    rw [AlgHom.mapMatrix_apply, Matrix.map_mul, hmapW, Matrix.transpose_map]
    have h1 : (genY A r).adjugate.map (cofY A r) = ((genY A r).map (cofY A r)).adjugate :=
      RingHom.map_adjugate (cofY A r).toRingHom (genY A r)
    rw [h1, ← AlgHom.mapMatrix_apply, cofY_mapMatrix]
  rw [hmap]
  rcases Nat.lt_or_ge r 2 with hr | hr
  · interval_cases r
    · ext i
      exact Fin.elim0 i
    · ext i j
      fin_cases i
      fin_cases j
      simp [pdZ, pdW, genY, Matrix.adjugate_fin_one, Matrix.det_fin_one, Matrix.mul_apply]
  · have hadjadj : (genY A r).adjugate.adjugate = (genY A r).det ^ (r - 2) • genY A r := by
      rw [Matrix.adjugate_adjugate _ (by rw [Fintype.card_fin]; omega), Fintype.card_fin]
    have hZ : (pdZ A r).adjugate =
        ((pdW A r).det * (genY A r).det ^ (r - 2)) • (pdW A r * (genY A r).transpose) := by
      rw [pdZ_eq, Matrix.adjugate_mul_distrib, hadjW, ← Matrix.adjugate_transpose, hadjadj,
        Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hZ, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, hWT,
      Matrix.smul_mul, Matrix.mul_assoc, hWW, Matrix.mul_one, smul_smul]
    congr 1
    rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]
    ring

theorem pd_aeval_scale {σ B : Type} [Fintype σ] [CommRing B] [Algebra A B] (c : B) (z : σ → B) (d : ℕ)
    (g : MvPolynomial σ A) (hg : g.IsHomogeneous d) : aeval (fun i => c * z i) g = c ^ d * aeval z g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := hg (mem_support_iff.1 hs)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at hd
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [show ∑ i ∈ s.support, s i = d from by rw [← hd]; rfl]
  ring

theorem pd_cofcof (d : ℕ) (g : MvPolynomial (Fin r × Fin r) A) (hg : g.IsHomogeneous d) :
    detY A r ^ d * cofY A r (cofY A r g) = ((pdW A r).det * detY A r ^ (r - 1)) ^ d * g := by
  have hcomp : cofY A r (cofY A r g) = aeval (fun v => cofY A r (pdZ A r v.1 v.2)) g := by
    rw [← AlgHom.comp_apply]
    unfold cofY
    rw [MvPolynomial.comp_aeval]
    rfl
  have hz : (fun v : Fin r × Fin r => detY A r * cofY A r (pdZ A r v.1 v.2)) =
      fun v => ((pdW A r).det * detY A r ^ (r - 1)) * X v := by
    funext v
    have h1 := congrFun (congrFun (pd_ZZ A r) v.1) v.2
    simp only [Matrix.smul_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, genY,
      Matrix.of_apply] at h1
    rw [detY_eq]
    exact h1
  rw [hcomp, ← pd_aeval_scale A (detY A r) _ d g hg, hz, pd_aeval_scale A _ X d g hg,
    aeval_X_left_apply]

end Formalism.MainNotions.flipOneThree.Pf

end
