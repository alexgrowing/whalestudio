import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementJacquetMinusOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhdEqPhk
import GroundTheory.HeightsAndTheta.Theta.WeilBox

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GroundTheory.Heights₂.Theta
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.BigCell.PhdSupp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def flat (Φ : Matrix (Fin 2) (Fin 2) F → ℂ) : (Fin 2 × Fin 2 → F) → ℂ :=
  fun X => Φ (Matrix.of fun i j => X (i, j))

def ent4 (r v : Fin 2 → F) : Fin 2 × Fin 2 → F :=
  fun ij => (![r, v] : Fin 2 → Fin 2 → F) ij.1 ij.2

def entHomeo : (Fin 2 × Fin 2 → F) ≃ₜ Matrix (Fin 2) (Fin 2) F where
  toFun X := Matrix.of fun i j => X (i, j)
  invFun A := fun ij => A ij.1 ij.2
  left_inv X := rfl
  right_inv A := rfl
  continuous_toFun := by
    refine continuous_matrix fun i j => ?_
    exact continuous_apply (i, j)
  continuous_invFun := by
    refine continuous_pi fun ij => ?_
    exact (continuous_apply ij.2).comp (continuous_apply ij.1)

theorem flat_mem {Φ : Matrix (Fin 2) (Fin 2) F → ℂ} (h : SB2 Φ) :
    flat Φ ∈ schwartzBruhatPi F (Fin 2 × Fin 2) :=
  ⟨h.1.comp_continuous entHomeo.continuous, h.2.comp_homeomorph entHomeo⟩

variable [MeasurableSpace F] [BorelSpace F]

end GlobalTheory.CompanionTheory.BigCell.PhdSupp

namespace GlobalTheory.CompanionTheory.BigCell

end GlobalTheory.CompanionTheory.BigCell
