import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearModelFourierTransformExchange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearModel_fourier_transform_exchange : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n r : ℕ), ∃ τ : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] GlobalTheory.SplitWeil.SB (Matrix (Fin r) (Fin n) k), Function.Surjective τ ∧ ∀ (μ : kˣ →* ℂˣ) (gk : GL (Fin n) k) (hk : GL (Fin r) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) k)), Φ'.1 = GlobalTheory.SplitWeil.om μ hk gk Φ.1 → (τ Φ').1 = GlobalTheory.SplitWeil.om μ⁻¹ gk hk (τ Φ).1 := by
  first | exact @GlobalTheory.linearModel_fourier | exact GlobalTheory.linearModel_fourier | (intros; apply GlobalTheory.linearModel_fourier <;> assumption)
