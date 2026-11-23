import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.ExistsTwoTorsionOffKernels
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls

noncomputable section

namespace Formalism.L2.Th1.F2

open NumberField
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory Formalism.MainNotions
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5 (latI UniqInv CMConjSet)

def IsLatClosure : Prop :=
  ∀ a b : ℂ, ((starRingEnd ℂ) a * b).im ≠ 0 → IsLat (AddSubgroup.closure {a, b})

def IsLatSmul : Prop := ∀ (Λ : AddSubgroup ℂ) (c : ℂ), c ≠ 0 → IsLat Λ → IsLat (c • Λ)

def HasCMSmul : Prop := ∀ (d : ℕ) (Λ : AddSubgroup ℂ) (c : ℂ), HasCM d Λ → HasCM d (c • Λ)

def LatILat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime], d % 4 = 3 → ∀ x : K, x ^ 2 = -(d : K) →
    Module.finrank ℚ K = 2 → ∀ (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K)) (δ : ℂ), 𝔞 ≠ ⊥ → δ ≠ 0 →
      IsLat (latI φ 𝔞 δ) ∧ HasCM d (latI φ 𝔞 δ)

def LamConjLat : Prop :=
  ∀ (D : D7), UniqInv → CMConjSet D → ∀ (cc : Ideal (𝓞 D.host.K)), TaylorLogMetric.IsCurveIdeal D cc → ∀ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) [NumberField M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc δ) M → ∀ ρ : M →ₐ[ℚ] ℂ,
      IsLat (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc δ)) ∧ HasCM D.host.d (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc δ))

def LamConjTheta : Prop :=
  ∀ (D : D7), UniqInv → CMConjSet D → ∀ (cc : Ideal (𝓞 D.host.K)), TaylorLogMetric.IsCurveIdeal D cc → ∀ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (M : IntermediateField ℚ ℂ) [NumberField M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc δ) M → ∀ ρ : M →ₐ[ℚ] ℂ,
      ∃ G, IsTheta0 D.host.d (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc δ)) G ∧
        (∀ G', IsTheta0 D.host.d (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc δ)) G' → G' = G) ∧
        0 < normSq1 (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D cc δ)) G

end Formalism.L2.Th1.F2
