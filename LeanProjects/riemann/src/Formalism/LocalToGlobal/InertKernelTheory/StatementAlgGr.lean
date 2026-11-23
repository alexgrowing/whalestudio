import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Classical
open Formalism.L2.Th1.H (taylorMv)

def ThMMBdd : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Ker.Base D cc δ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → jacobiSym (-(D.host.d : ℤ)) l = -1 →
    ∀ (t : D.what₂.Tau → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ B.lamM →
    ∀ α : D.what₂.Tau →₀ ℕ, ∃ M : ℝ, ∀ ι : ℂ ≃+* ℂ_[l],
      ‖ι (MvPowerSeries.coeff α (taylorMv (trM B t B.thMM)))‖ ≤ M

def ThMMTransAlgPrime : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Ker.Base D cc δ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → jacobiSym (-(D.host.d : ℤ)) l = -1 →
    ∀ (t : D.what₂.Tau → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ B.lamM →
      CoefInMv (trM B t B.thMM) Formalism.MainNotions.TaylorLogMetric.Qbar

end Formalism.L2.KerInert
