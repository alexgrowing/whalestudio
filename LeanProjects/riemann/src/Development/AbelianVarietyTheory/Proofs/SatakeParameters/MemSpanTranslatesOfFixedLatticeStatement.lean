import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSpanTranslatesOfFixedLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalPlaceLocalModelsLinearSubspace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceMatrixCoordinateOnHalf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_translates_of_fixed_lattice : ∀ {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] (χ : G → G → ℂ), GlobalTheory.PlaceModel.IsBichar χ → ∀ (ρ : G → V →ₗ[ℂ] V) (X Yh L L' K : AddSubgroup G), L ≤ L' → L' ≤ X → K ≤ Yh → (∀ v, ρ 0 v = v) → (∀ x ∈ X, ∀ x' ∈ X, ∀ v, ρ x (ρ x' v) = ρ (x + x') v) → (∀ y ∈ Yh, ∀ y' ∈ Yh, ∀ v, ρ y (ρ y' v) = ρ (y + y') v) → (∀ x ∈ X, ∀ y ∈ Yh, ∀ v, ρ x (ρ y v) = χ x y • ρ y (ρ x v)) → (∃ R : Finset G, ∀ t ∈ L', ∃ r ∈ R, t - r ∈ L) → (∀ x ∈ L', ∀ y ∈ K, χ x y = 1) → (∀ y ∈ Yh, (∀ x ∈ L', χ x y = 1) → y ∈ K) → ∀ (W : Submodule ℂ V), (∀ v ∈ W, ∀ x ∈ X, ρ x v ∈ W) → (∀ v ∈ W, ∀ y ∈ Yh, ρ y v ∈ W) → ∀ f ∈ W, (∀ x ∈ L, ρ x f = f) → (∀ y ∈ K, ρ y f = f) → f ∈ Submodule.span ℂ {v | ∃ r ∈ X, ∃ g ∈ W, (∀ x ∈ L, ρ x g = g) ∧ (∀ y ∈ Yh, (∀ x ∈ L, χ x y = 1) → ρ y g = g) ∧ v = ρ r g} := by
  first | exact @GlobalTheory.FourierSpan.mem_span_translates_of_fixed | exact GlobalTheory.FourierSpan.mem_span_translates_of_fixed | (intros; apply GlobalTheory.FourierSpan.mem_span_translates_of_fixed <;> assumption)
