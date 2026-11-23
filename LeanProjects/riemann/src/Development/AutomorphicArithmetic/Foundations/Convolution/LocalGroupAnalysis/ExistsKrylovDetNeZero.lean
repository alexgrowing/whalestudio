import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.AutomorphicForms.StableConjCyclic
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjectiveLineOf
open PositivityTheory.Rg.Tf.Geo

private theorem exists_krylov_det_ne_zero {k : Type*} [Field k] [Infinite k] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) k) (h : M.charpoly.Separable) :
    ∃ v : Fin n → k, (GroundTheory.Automorphic.krylov M v).det ≠ 0 := by
  have hs : (Matrix.toLin' M).charpoly.Separable := by rwa [Matrix.charpoly_toLin']
  obtain ⟨w, hw⟩ := GroundTheory.Automorphic.exists_linearIndependent_pow_apply _ hs
  rw [Module.finrank_fin_fun] at hw
  refine ⟨w, ?_⟩
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_cols_iff_isUnit]
  have hcol : (GroundTheory.Automorphic.krylov M w).col =
      fun j : Fin n => (Matrix.toLin' M ^ (j : ℕ)) w := by
    ext1 j
    rw [GroundTheory.Automorphic.krylov_col, ← Matrix.toLin'_pow, Matrix.toLin'_apply]
  rw [hcol]
  exact hw

private theorem isClosed_charpoly_eq {k : Type*} [NontriviallyNormedField k] [Infinite k] {n : ℕ}
    (P : Polynomial k) : IsClosed {g : GL (Fin n) k | (g : Matrix (Fin n) (Fin n) k).charpoly = P} := by
  have : {g : GL (Fin n) k | (g : Matrix (Fin n) (Fin n) k).charpoly = P} =
      ⋂ a : k, {g : GL (Fin n) k | (Matrix.scalar (Fin n) a - (g : Matrix (Fin n) (Fin n) k)).det = P.eval a} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro rfl a
      rw [Matrix.eval_charpoly]
    · intro h
      apply Polynomial.funext
      intro a
      rw [Matrix.eval_charpoly]
      exact h a
  rw [this]
  refine isClosed_iInter fun a => isClosed_eq ?_ continuous_const
  exact (continuous_const.sub Units.continuous_val).matrix_det

private theorem continuous_krylov {k : Type*} [NontriviallyNormedField k] {n : ℕ} (v : Fin n → k) :
    Continuous fun g : GL (Fin n) k => GroundTheory.Automorphic.krylov (g : Matrix (Fin n) (Fin n) k) v := by
  refine continuous_matrix fun i j => ?_
  simp only [GroundTheory.Automorphic.krylov, Matrix.of_apply]
  exact (continuous_apply i).comp (((Units.continuous_val.pow _)).matrix_mulVec continuous_const)

private theorem conj_of_compM {k : Type*} [Field k] {n : ℕ} (γ g B U : GL (Fin n) k)
    (T : Matrix (Fin n) (Fin n) k)
    (hB : (γ : Matrix (Fin n) (Fin n) k) * B = B * T)
    (hU : (g : Matrix (Fin n) (Fin n) k) * U = U * T) :
    g = (B * U⁻¹)⁻¹ * γ * (B * U⁻¹) := by
  have hT : ((B⁻¹ * γ * B : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = T := by
    rw [Units.val_mul, Units.val_mul, mul_assoc, hB, ← mul_assoc]
    simp
  have h1 : g * U = U * (B⁻¹ * γ * B) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hT, hU]
  calc g = U * (B⁻¹ * γ * B) * U⁻¹ := by rw [← h1]; group
    _ = (B * U⁻¹)⁻¹ * γ * (B * U⁻¹) := by group

theorem UpperTheory.ConvolutionTheory.G.p1_holds :
    P1 :=
  _root_.UpperTheory.Reformulated.B.ProjectiveLineOf.p1_holds
