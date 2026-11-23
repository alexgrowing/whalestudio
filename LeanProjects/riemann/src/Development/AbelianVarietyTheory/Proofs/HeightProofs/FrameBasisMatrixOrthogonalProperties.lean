import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix GlobalTheory.FockCompare GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition
open scoped TensorProduct ContDiff ComplexOrder

namespace GlobalTheory.FockBasisMatrix

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem exists_basis (S : HSpace E) (Q : Matrix (Fin S.rank) (Fin S.rank) E) (hQ : IsUnit Q.det) :
    ∃ b : Module.Basis (Fin S.rank) E S.V, Q = S.frame.toMatrix b := by
  refine ⟨S.frame.map (Matrix.toLinearEquiv S.frame Q hQ), ?_⟩
  ext i j
  simp [Module.Basis.toMatrix_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self, Finsupp.single_apply]

theorem isUnit_det (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) : IsUnit (S.frame.toMatrix b).det := by
  letI := Module.Basis.invertibleToMatrix S.frame b
  exact Matrix.isUnit_det_of_invertible _

theorem gram_change (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) (i j : Fin S.rank) :
    (((S.frame.toMatrix b).map star)ᵀ * S.gram * S.frame.toMatrix b) i j = S.hT (b i) (b j) := by
  conv_rhs => rw [← S.frame.sum_repr (b i), ← S.frame.sum_repr (b j)]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, HSpace.gram,
    map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem diag_ne_zero (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V)
    (ho : ∀ i j, i ≠ j → S.hT (b i) (b j) = 0) (i : Fin S.rank) : S.hT (b i) (b i) ≠ 0 := by
  intro h0
  refine b.ne_zero i (S.nondeg.2 _ fun x => ?_)
  rw [← b.sum_repr x, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
  by_cases hk : k = i
  · rw [hk, h0, smul_zero]
  · rw [ho k i hk, smul_zero]

theorem diag_real (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ x, τ (star x) = starRingEnd ℂ (τ x)) (x : S.V) :
    (((τ (S.hT x x)).re : ℝ) : ℂ) = τ (S.hT x x) := by
  rw [← Complex.conj_eq_iff_re, ← hτ]
  exact congrArg τ (S.herm.eq x x)

theorem toMatrix_mul_diag (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V) (s : Module.End E S.V)
    (c : Fin S.rank → E) (hs : ∀ i, s (b i) = c i • b i) :
    LinearMap.toMatrix S.frame S.frame s * S.frame.toMatrix b = S.frame.toMatrix b * Matrix.diagonal c := by
  rw [linearMap_toMatrix_mul_basis_toMatrix]
  ext i j
  rw [Matrix.mul_diagonal, LinearMap.toMatrix_apply, hs, Module.Basis.toMatrix_apply, map_smul, Finsupp.smul_apply,
    smul_eq_mul, mul_comm]

theorem orthogonal_basis (S : HSpace E) (b : Module.Basis (Fin S.rank) E S.V)
    (ho : ∀ i j, i ≠ j → S.hT (b i) (b j) = 0) (τ : E →+* ℂ) (hτ : ∀ x, τ (star x) = starRingEnd ℂ (τ x)) :
    (∀ i, (τ (S.hT (b i) (b i))).re ≠ 0) ∧
    ((S.frame.toMatrix b).map τ)ᴴ * S.gram.map τ * (S.frame.toMatrix b).map τ =
      Matrix.diagonal (fun i => (((τ (S.hT (b i) (b i))).re : ℝ) : ℂ)) ∧
    ∀ s : Module.End E S.V, (∀ i, s (b i) = if 0 < (τ (S.hT (b i) (b i))).re then b i else -b i) →
      (LinearMap.toMatrix S.frame S.frame s).map τ * (S.frame.toMatrix b).map τ =
        (S.frame.toMatrix b).map τ * Matrix.diagonal (fun i => if 0 < (τ (S.hT (b i) (b i))).re then (1 : ℂ) else -1) := by
  refine ⟨fun i h => ?_, ?_, fun s hs => ?_⟩
  · have := diag_real S τ hτ (b i)
    rw [h, Complex.ofReal_zero] at this
    exact diag_ne_zero S b ho i ((map_eq_zero τ).1 this.symm)
  · have e : ((S.frame.toMatrix b).map τ)ᴴ = (((S.frame.toMatrix b).map star)ᵀ).map τ := by
      ext i j
      simp [Matrix.conjTranspose_apply, hτ]
    rw [e, ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    rw [Matrix.map_apply, gram_change]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, diag_real S τ hτ]
    · rw [Matrix.diagonal_apply_ne _ hij, ho i j hij, map_zero]
  · have h := toMatrix_mul_diag S b s (fun i => if 0 < (τ (S.hT (b i) (b i))).re then (1 : E) else -1)
      (fun i => by rw [hs i]; split_ifs <;> simp)
    rw [← Matrix.map_mul, h, Matrix.map_mul, Matrix.diagonal_map (map_zero τ)]
    congr 2
    funext i
    split_ifs <;> simp

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem basis_matrix : ∀ (D : D7) (V : HSp D), (∀ Q : Matrix (Fin V.rank) (Fin V.rank) D.host.E, IsUnit Q.det → ∃ b : Module.Basis (Fin V.rank) D.host.E V.V, Q = V.frame.toMatrix b) ∧ ∀ b : Module.Basis (Fin V.rank) D.host.E V.V, IsUnit (V.frame.toMatrix b).det ∧ (∀ i j, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (V.frame.toMatrix b) * V.gram * V.frame.toMatrix b) i j = V.hT (b i) (b j)) ∧ ((∀ i j, i ≠ j → V.hT (b i) (b j) = 0) → ∀ τ : D.what₂.Tau, (∀ i, (tauE D τ (V.hT (b i) (b i))).re ≠ 0) ∧ ((V.frame.toMatrix b).map (tauE D τ))ᴴ * gramAt D V τ * (V.frame.toMatrix b).map (tauE D τ) = Matrix.diagonal (fun i => (((tauE D τ (V.hT (b i) (b i))).re : ℝ) : ℂ)) ∧ ∀ s : Module.End D.host.E V.V, (∀ i, s (b i) = if 0 < (tauE D τ (V.hT (b i) (b i))).re then b i else -b i) → thAt V τ s * (V.frame.toMatrix b).map (tauE D τ) = (V.frame.toMatrix b).map (tauE D τ) * Matrix.diagonal (fun i => if 0 < (tauE D τ (V.hT (b i) (b i))).re then (1 : ℂ) else -1)) := by
  intro D V
  exact ⟨exists_basis V, fun b => ⟨isUnit_det V b, gram_change V b,
    fun ho τ => orthogonal_basis V b ho (tauE D τ) (tauE_star τ)⟩⟩

end GlobalTheory.FockBasisMatrix
