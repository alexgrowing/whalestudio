import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActWOneApply
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

theorem linearIndependent_mulVec_unit {E : Type} [Field E] {M n : ℕ} (A : GL (Fin M) E)
    {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (fun a => (A : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  have hinj : Function.Injective (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) := by
    intro x y hxy
    have h : ∀ z : Fin M → E,
        ((A⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ ((A : Matrix (Fin M) (Fin M) E) *ᵥ z) = z := by
      intro z
      rw [Matrix.mulVec_mulVec, ← Units.val_mul]
      simp
    have hxy' : (A : Matrix (Fin M) (Fin M) E) *ᵥ x = (A : Matrix (Fin M) (Fin M) E) *ᵥ y := hxy
    rw [← h x, ← h y, hxy']
  exact hX.map' (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) (LinearMap.ker_eq_bot.2 hinj)

theorem linearIndependent_gact_unitary {F E : Type} [Field F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (g : UJ (σ : E →+* E) J) {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (gact σ g X) :=
  linearIndependent_mulVec_unit (g : GL (Fin M) E) hX

theorem gact_inv_e0 {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) : gact σ w⁻¹ (e0 E M) = e0 E M := by
  conv_lhs => rw [← hw]
  exact gact_inv_gact σ w _

theorem gact_zero_of_first {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (w : UJ (σ : E →+* E) (hypOne J))
    {X : Fin (n + 1) → Fin (M + 2) → E} (hX : X 0 = e0 E M 0) :
    gact σ w X 0 = gact σ w (e0 E M) 0 := by
  change ((w : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E) *ᵥ X 0 =
    ((w : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E) *ᵥ e0 E M 0
  rw [hX]

theorem gact_mem_framesOne {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) {X : Fin (n + 1) → Fin (M + 2) → E}
    (hX : X ∈ framesOne σ J n) : gact σ w X ∈ framesOne σ J n := by
  refine ⟨⟨linearIndependent_gact_unitary σ w hX.1.1, ?_⟩, ?_⟩
  · rw [gramE_gact]; exact hX.1.2
  · rw [gact_zero_of_first σ w hX.2, hw]

def framesOneEquiv {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (n : ℕ) {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) : framesOne σ J n ≃ framesOne σ J n where
  toFun X := ⟨gact σ w X.1, gact_mem_framesOne σ hw X.2⟩
  invFun X := ⟨gact σ w⁻¹ X.1, gact_mem_framesOne σ (gact_inv_e0 σ hw) X.2⟩
  left_inv X := Subtype.ext (gact_inv_gact σ w X.1)
  right_inv X := Subtype.ext (gact_gact_inv σ w X.1)

theorem tsum_gact_framesOne (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (w : UJ (σ : E →+* E) (hypOne J))
    (hw : gact σ w (e0 E M) = e0 E M) (f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞) :
    ∑' X : framesOne σ J n, f (gact σ w X.1) = ∑' X : framesOne σ J n, f X.1 :=
  (framesOneEquiv σ n hw).tsum_eq (fun X => f X.1)

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
