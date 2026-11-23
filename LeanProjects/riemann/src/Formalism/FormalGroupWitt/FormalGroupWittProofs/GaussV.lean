import Formalism.FormalGroupWitt.FormalGroupWittProofs.SolveV

noncomputable section

universe u

namespace Formalism.FG.BernoulliBounds

open MvPowerSeries Formalism.G Formalism.FG.SolveVAux

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

def BndLe {ι : Type*} (c : ℝ) (M : ℕ) (f : MvPowerSeries ι K) (B : ℝ) : Prop :=
  ∀ t : ι →₀ ℕ, t.degree ≤ M → ‖coeff t f‖ * c ^ t.degree ≤ B

variable [CharZero K]

def shiftPoly (K : Type u) [Field K] (l m : ℕ) (j : ZMod m) (N : ℕ) : MvPowerSeries (ZMod m) K :=
  ∑ e ∈ Finset.range (N + 1), ((l : K) ^ e)⁻¹ • (X (j - (e : ZMod m)) ^ ((l ^ 2) ^ e))

end Formalism.FG.BernoulliBounds

namespace Formalism.FG

end Formalism.FG
