import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualOfAnisotropicOrthogonal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryOrthogonalEmbeddingStabilizerStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

theorem star_dot_Jm {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = (qEps ε x : ℂ) := by
  unfold qEps Formalism.REAL.Jm
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (starRingEnd ℂ) (x i) * x i = ((‖x i‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' (x i)
  split_ifs
  · simp [hi]
  · simp [hi]

theorem realUJ_eq {n : ℕ} (ε : Fin n → Bool) :
    Formalism.UG.UJ (starRingEnd ℂ) (Formalism.REAL.Jm ε) = Formalism.REAL.UJ ε := by
  unfold Formalism.REAL.UJ Formalism.UG.UJ Formalism.REAL.inUJ
  have hc : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
    intro M
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, Complex.star_def]
  ext g
  change Formalism.UG.cT (starRingEnd ℂ) (g : Matrix (Fin n) (Fin n) ℂ) * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε ↔
    (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
  rw [hc]

theorem exists_closedEmbedding_unitary_orthogonal (n m : ℕ) (ε : Fin n → Bool) (ε' : Fin m → Bool) (s : Bool)
    (x₀ : Fin n → ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (hn : m + 1 = n) (hq : qEps ε x₀ = sgn ℝ s)
    (hx : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0) (hB : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') :
    ∃ j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε, Topology.IsClosedEmbedding j ∧
      ∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g := by
  unfold uMat
  have hJh : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    unfold Formalism.REAL.Jm
    rw [diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a <;> simp [h]
  have hdet : (Formalism.REAL.Jm ε').det ≠ 0 := by
    unfold Formalism.REAL.Jm
    rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => by by_cases h : ε' a <;> simp [h]
  have hβ : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x₀) ≠ 0 := by
    rw [star_dot_Jm, hq]
    cases s <;> simp [sgn]
  obtain ⟨u, A', hA'B, hA'x, huB, hux, hres, hBJx⟩ :=
    exists_dual_of_anisotropic_orthogonal ℂ n m (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε') x₀ B hn hJh hdet hβ hx hB
  have hcT : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℂ), Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
    intro p q M
    ext i k
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, Complex.star_def]
  have hstar : (fun i => starRingEnd ℂ (x₀ i)) = star x₀ := by
    funext i
    simp [Complex.star_def]
  obtain ⟨j, hjmat, hjrange⟩ := GlobalTheory.T.exists_unitary_orthogonal_embedding_stabilizer ℂ (starRingEnd ℂ) n m (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε') x₀ u B A'
    (by rw [hstar]; exact isUnit_iff_ne_zero.mpr hβ) (by rw [hstar]; exact hx) (by rw [hcT]; exact hBJx)
    (by rw [hcT]; exact hB) hA'B hA'x huB hux hres
  obtain ⟨jj, hjj, hrange⟩ : ∃ jj : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε,
      (∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        vecMulVec x₀ u + B * ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * A') ∧
      ∀ h : Formalism.REAL.UJ ε, ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀ → ∃ g, jj g = h := by
    refine ⟨(MulEquiv.subgroupCongr (realUJ_eq ε)).toMonoidHom.comp
      (j.comp (MulEquiv.subgroupCongr (realUJ_eq ε')).symm.toMonoidHom), fun g => hjmat _, ?_⟩
    intro h hh
    obtain ⟨g', hg'⟩ := hjrange ((MulEquiv.subgroupCongr (realUJ_eq ε)).symm h) hh
    refine ⟨MulEquiv.subgroupCongr (realUJ_eq ε') g', ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hg'
  have h0 : vecMulVec x₀ u * B = 0 := by
    ext i k
    have hk := congrFun huB k
    simp only [vecMul, dotProduct, Pi.zero_apply] at hk
    simp only [mul_apply, vecMulVec_apply, Matrix.zero_apply, mul_assoc, ← Finset.mul_sum, hk, mul_zero]
  have hv : vecMulVec x₀ u *ᵥ x₀ = x₀ := by
    ext i
    simp only [mulVec, dotProduct, vecMulVec_apply, mul_assoc, ← Finset.mul_sum]
    rw [show ∑ k, u k * x₀ k = 1 from hux, mul_one]
  have hfix : ∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀ := by
    intro g
    rw [hjj, add_mulVec, hv, ← mulVec_mulVec, hA'x, mulVec_zero, add_zero]
  have hcomm : ∀ g, ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B =
      B * ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) := by
    intro g
    rw [hjj, Matrix.add_mul, h0, zero_add, Matrix.mul_assoc (B * _), hA'B, Matrix.mul_one]
  have hback : ∀ M : Matrix (Fin m) (Fin m) ℂ, A' * (vecMulVec x₀ u + B * M * A') * B = M := by
    intro M
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc A' (vecMulVec x₀ u), h0, Matrix.mul_zero, zero_add,
      Matrix.mul_assoc, Matrix.mul_assoc, hA'B, Matrix.mul_one, ← Matrix.mul_assoc, hA'B, Matrix.one_mul]
  have hval' : Continuous fun g : Formalism.REAL.UJ ε' => ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
    Units.continuous_val.comp continuous_subtype_val
  have hinv' : Continuous fun g : Formalism.REAL.UJ ε' => (((g : GL (Fin m) ℂ)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  have hjinv : ∀ g, ((((jj g : GL (Fin n) ℂ))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      vecMulVec x₀ u + B * (((g : GL (Fin m) ℂ)⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) * A' := by
    intro g
    have h1 := hjj g⁻¹
    rw [map_inv] at h1
    exact h1
  have hcont : Continuous jj := by
    refine continuous_induced_rng.2 ?_
    rw [Units.continuous_iff]
    constructor
    · exact Continuous.congr (continuous_const.add ((continuous_const.matrix_mul hval').matrix_mul continuous_const))
        fun g => (hjj g).symm
    · exact Continuous.congr (continuous_const.add ((continuous_const.matrix_mul hinv').matrix_mul continuous_const))
        fun g => (hjinv g).symm
  let ψ : Formalism.REAL.UJ ε → Matrix (Fin m) (Fin m) ℂ × (Matrix (Fin m) (Fin m) ℂ)ᵐᵒᵖ := fun h =>
    (A' * ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B,
      MulOpposite.op (A' * (((h : GL (Fin n) ℂ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B))
  have hψc : Continuous ψ := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul
        continuous_const
    · exact MulOpposite.continuous_op.comp ((continuous_const.matrix_mul
        (Units.continuous_coe_inv.comp continuous_subtype_val)).matrix_mul continuous_const)
  have hψ : ∀ g, ψ (jj g) = Units.embedProduct _ (g : GL (Fin m) ℂ) := by
    intro g
    refine Prod.ext ?_ ?_
    · show A' * ((jj g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B = ((g : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)
      rw [hjj, hback]
    · show MulOpposite.op (A' * ((((jj g : GL (Fin n) ℂ))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * B) =
        MulOpposite.op ((((g : GL (Fin m) ℂ))⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)
      rw [hjinv, hback]
  have hind : Topology.IsInducing jj := by
    refine Topology.IsInducing.of_comp hcont hψc ?_
    have he : ψ ∘ jj = fun g : Formalism.REAL.UJ ε' => Units.embedProduct _ (g : GL (Fin m) ℂ) := funext hψ
    rw [he]
    exact Units.isInducing_embedProduct.comp Topology.IsInducing.subtypeVal
  have hinj : Function.Injective jj := by
    intro a b hab
    have hc := congrArg ψ hab
    rw [hψ, hψ] at hc
    exact Subtype.ext (Units.ext (congrArg Prod.fst hc))
  have hrng : Set.range jj = {h : Formalism.REAL.UJ ε | ((h : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *ᵥ x₀ = x₀} := by
    ext h
    constructor
    · rintro ⟨g, rfl⟩
      exact hfix g
    · intro hh
      exact hrange h hh
  have hclosed : IsClosed (Set.range jj) := by
    rw [hrng]
    exact isClosed_eq ((Units.continuous_val.comp continuous_subtype_val).matrix_mulVec continuous_const)
      continuous_const
  exact ⟨jj, ⟨⟨hind, hinj⟩, hclosed⟩, fun g => ⟨hfix g, hcomm g⟩⟩

end GlobalTheory.StabUnfold
