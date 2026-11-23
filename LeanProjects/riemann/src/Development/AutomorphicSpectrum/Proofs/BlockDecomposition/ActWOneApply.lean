import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

variable {F E : Type} [Field F] [Field E] [Algebra F E]

section Stab

variable (R : Type) [CommRing R] [Algebra F R]

theorem actW_mul_apply (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (g h : HA R σ J)
    (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ J (g * h) X = actW R σ J g (actW R σ J h X) := by
  funext a
  change ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
      (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E))) *ᵥ X a =
    (HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ
      ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ X a)
  rw [Matrix.mulVec_mulVec]

theorem actW_one_apply (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) : actW R σ J 1 X = X := by
  funext a
  change (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ X a = X a
  exact Matrix.one_mulVec _

def stabilizer₂ (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA R σ (hypOne J)) where
  carrier := {h | actW R σ (hypOne J) h (e0 _ M) = e0 _ M}
  one_mem' := actW_one_apply R σ (hypOne J) _
  mul_mem' := by
    intro g h hg hh
    change actW R σ (hypOne J) (g * h) (e0 _ M) = e0 _ M
    rw [actW_mul_apply, show actW R σ (hypOne J) h (e0 _ M) = e0 _ M from hh]
    exact hg
  inv_mem' := by
    intro g hg
    change actW R σ (hypOne J) g⁻¹ (e0 _ M) = e0 _ M
    have hg' : actW R σ (hypOne J) g (e0 _ M) = e0 _ M := hg
    conv_lhs => rw [← hg']
    rw [← actW_mul_apply, inv_mul_cancel, actW_one_apply]

def ratP (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (stabilizer₂ R σ J) :=
  Subgroup.comap (stabilizer₂ R σ J).subtype
    (show Subgroup (HA R σ (hypOne J)) from HFinIn R σ (hypOne J))

end Stab

def framesOne (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (n : ℕ) :
    Set (Fin (n + 1) → Fin (M + 2) → E) :=
  {X | X ∈ framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E) ∧ X 0 = e0 E M 0}

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
