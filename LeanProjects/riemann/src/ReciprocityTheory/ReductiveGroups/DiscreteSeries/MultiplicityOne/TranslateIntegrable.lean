import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.ZeroOfOrbit

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def ph (X : SigData k r) (d : ℝ) (y : Mat k r) : ℂ := (d : ℂ) * star (mc X X.w X.w y)

def tst (X : SigData k r) (B : X.Hs →ₗ[ℂ] Wp) (η : Mat k r → Wp) (v : X.Hs) (g : Mt k r) : ℂ :=
  (wr g : ℂ) * ⟪η (Matrix.of g), B (X.σ (Matrix.of g) v)⟫_ℂ

end ReciprocityTheory.ChartRestriction.DS.Mult1.SquareIntegrabilityOnOrbit
