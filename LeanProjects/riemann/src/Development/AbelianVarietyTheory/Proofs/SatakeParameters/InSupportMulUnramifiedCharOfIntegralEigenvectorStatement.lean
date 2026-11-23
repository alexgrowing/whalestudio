import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InSupportMulUnramifiedCharOfIntegralEigenvector
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inSupport_mul_unramifiedChar_of_integralEigenvector : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin m) k) V) (χ : kˣ →* ℂˣ) (y : V), IsSmooth σ → σ.IsIrreducible → IsSmoothChar χ → 0 < m → y ≠ 0 → (∀ g ∈ KO k (Fin m), σ g y = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • y) → ∃ α : ℂˣ, InSupport σ (χ * unrChar k α) := by
  first | exact @GlobalTheory.SphSupport.inSupport_mul_unrChar_of_KO_eigen | exact GlobalTheory.SphSupport.inSupport_mul_unrChar_of_KO_eigen | (intros; apply GlobalTheory.SphSupport.inSupport_mul_unrChar_of_KO_eigen <;> assumption)
