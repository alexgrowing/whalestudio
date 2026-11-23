import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicSubspaceInvariantSchwartz
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_subspace_invariant_schwartz : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    [Invertible (2 : k)] {κ : Type} [Fintype κ] (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ U : Submodule k ((κ → k) × (κ → k)), (∀ u ∈ U, ∀ u' ∈ U, u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2 = 0) →
    ∀ S : Submodule ℂ ((κ → k) → ℂ), S ≤ GlobalTheory.WeilM.SB (κ → k) →
    (∀ u ∈ U, ∀ φ ∈ GlobalTheory.WeilM.SB (κ → k), GlobalTheory.WeilM.schr ψ0 u φ - φ ∈ S) →
    (∀ w : (κ → k) × (κ → k), (∀ u ∈ U, u.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ u.2 = 0) → ∀ φ ∈ S, GlobalTheory.WeilM.schr ψ0 w φ ∈ S) →
    ∀ φ₀ ∈ S, φ₀ ∉ Submodule.span ℂ {f | ∃ u ∈ U, ∃ φ ∈ GlobalTheory.WeilM.SB (κ → k), f = GlobalTheory.WeilM.schr ψ0 u φ - φ} →
    S = GlobalTheory.WeilM.SB (κ → k) := by
  first | exact @GlobalTheory.CoinvIrr.coinvariants_irreducible | exact GlobalTheory.CoinvIrr.coinvariants_irreducible | (intros; apply GlobalTheory.CoinvIrr.coinvariants_irreducible <;> assumption)
