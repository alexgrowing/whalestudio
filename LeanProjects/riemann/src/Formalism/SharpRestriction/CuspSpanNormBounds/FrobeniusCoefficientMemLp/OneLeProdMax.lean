import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.LeadingMinorEmbeddingBound

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.S.Pv.HH

open Finset NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_le_prod_max {ι : Type*} (s : Finset ι) (g : ι → ℝ) : 1 ≤ ∏ i ∈ s, max 1 (g i) := by
  have := Finset.prod_le_prod (s := s) (f := fun _ => (1 : ℝ)) (g := fun i => max 1 (g i))
    (fun i _ => zero_le_one) (fun i _ => le_max_left _ _)
  simpa using this

variable (D : D7)

def Bmin (b C : ℝ) (Z : GramM D) : ℝ :=
  R0 D ^ D.R.f * K1 D ^ D.R.f *
    ((R1 D * b ^ (C * (D.R.m : ℝ) ^ 2)) ^ ((D.R.rS + 1) * D.R.f) * sizeZ D b C Z) ^ 2

end Formalism.MainNotions.S.Pv.HH

end
