import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.DeterminantNaturalAnisotropic
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PartnerThetaInclusion

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def FrameVectorsMemLattice : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → (∀ b, frame (lf D F0) b ∈ Λ) ∧
    ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → ∀ b, frame F' b ∈ Λ

def GenericTermDetProductBound (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ Z : GramM D, RelZ D Z →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' → ZEquiv (ZhatL (lf D F0) F') Z →
    G0 Λ (gS D) (lf D F0) F' = localGramProduct D u u' Z ∧
    1 ≤ localGramProduct D u u' Z ∧ localGramProduct D u u' Z ≤ HHZ D large₂.sc.b C Z

end Gen

section Det

variable (D : D7) (u : D.what₂.Word)

def InertPrimesSquareNorm' : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 D.host.E), Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal →
    IsSquare (Ideal.absNorm P.asIdeal)

end Det

end Formalism.MainNotions.BridgeLemma₂

end
