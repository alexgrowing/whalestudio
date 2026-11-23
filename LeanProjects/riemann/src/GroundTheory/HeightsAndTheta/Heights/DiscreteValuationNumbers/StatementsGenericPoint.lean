import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.TrivBundleIsTwistedForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def GenericPointTransfer.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
    (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
    IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (pt : MRing ι F →ₐ[F] Ω')
      (E' : Type) (_ : AddCommGroup E') (_ : Module Ω' E')
      (B' : ChartBundle F (IndefiniteRowSideFullHecke.NumbersDVR.segreVec pt) N E') (u : Module.Basis (Fin N) Ω' E')
      (ω : Fin N → Ω') (φ' : Fin M → E' →ₗ[Ω'] Ω'),
      RingHom.ker pt = pointIdeal F y ∧ IndefiniteRowSideFullHecke.NumbersDVR.IsFlagGrading pt B' u b ω ∧
        IndefiniteRowSideFullHecke.NumbersDVR.IsTwistedForms pt B' φ' a ∧
        IndefiniteRowSideFullHecke.NumbersDVR.projBundleIdeal pt u φ' = IndefiniteRowSideFullHecke.NumbersDVR.projBundleIdeal (aeval y) w φ

end

end GroundTheory.Heights₂.Heights.NumbersDVR
