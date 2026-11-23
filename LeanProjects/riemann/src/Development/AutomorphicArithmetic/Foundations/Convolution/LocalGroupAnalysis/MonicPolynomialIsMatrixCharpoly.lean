import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ConjSep

open PositivityTheory.Rg.Tf.Geo PositivityTheory.Rg.Tf.Loc Polynomial

private theorem exists_matrix_charpoly {k : Type} [Field k] (P : k[X]) (hP : P.Monic) (n : ℕ)
    (hn : P.natDegree = n) : ∃ M : Matrix (Fin n) (Fin n) k, M.charpoly = P := by
  subst hn
  have hP0 : P ≠ 0 := hP.ne_zero
  have hdim : (AdjoinRoot.powerBasis hP0).dim = P.natDegree := AdjoinRoot.powerBasis_dim hP0
  refine ⟨Matrix.reindex (finCongr hdim) (finCongr hdim)
    (Algebra.leftMulMatrix (AdjoinRoot.powerBasis hP0).basis (AdjoinRoot.powerBasis hP0).gen), ?_⟩
  rw [Matrix.charpoly_reindex, charpoly_leftMulMatrix, AdjoinRoot.minpoly_powerBasis_gen hP0]
  simp [hP.leadingCoeff]

theorem UpperTheory.ConvolutionTheory.G.monic_polynomial_is_matrix_charpoly :
    N1 := by
  intro k E _ _ _ _ _ _ σ hgen n δ hreg
  obtain ⟨P, hP⟩ := charpoly_normGL_lifts σ hgen δ
  have hPm : P.Monic := Polynomial.monic_of_injective (algebraMap k E).injective
    (by rw [hP]; exact Matrix.charpoly_monic _)
  have hdeg : P.natDegree = n := by
    rw [← Polynomial.natDegree_map (f := algebraMap k E), hP, Matrix.charpoly_natDegree_eq_dim]
    simp
  obtain ⟨M, hM⟩ := exists_matrix_charpoly P hPm n hdeg
  have hMc : (M.map (algebraMap k E)).charpoly = ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly := by
    rw [Matrix.charpoly_map, hM, hP]
  have hdetE : (M.map (algebraMap k E)).det = ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det := by
    rw [Matrix.det_eq_sign_charpoly_coeff, Matrix.det_eq_sign_charpoly_coeff, hMc]
  have hNu : IsUnit ((normGL σ δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (normGL σ δ).isUnit
  have hdet : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [← hdetE] at hNu
    have e : (M.map (algebraMap k E)).det = algebraMap k E M.det := ((algebraMap k E).map_det M).symm
    rw [e, h0, map_zero] at hNu
    exact not_isUnit_zero hNu
  let γ : GL (Fin n) k := Matrix.nonsingInvUnit M hdet
  have hγ : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = M.map (algebraMap k E) := rfl
  obtain ⟨x, hx⟩ := (UpperTheory.ConvolutionTheory.D.conjSep E E n _ hreg).1 ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
    (by rw [hγ]; exact hMc)
  have hx' : normGL σ δ * x = x * incl γ := Units.ext hx
  refine ⟨x, γ, ?_⟩
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have h := twNorm_twConj_of_pow_eq_one (sigmaGL σ) hθ x δ
  change twNorm (sigmaGL σ) (Module.finrank k E) (twConj (sigmaGL σ) x δ) = incl γ
  rw [h]
  change x⁻¹ * normGL σ δ * x = incl γ
  rw [mul_assoc, hx', inv_mul_cancel_left]
