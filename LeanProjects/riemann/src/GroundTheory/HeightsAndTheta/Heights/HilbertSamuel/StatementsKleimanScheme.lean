import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def KleimanScheme.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (V : Ideal (MRingOver F ι))
    (α : K → ℤ) (b a : ℕ),
    IsFieldIntersection I → IsMultiHomogIdeal V → KH.NefOnF I V α → 1 ≤ b → 1 ≤ a →
    KH.AmpleV F V (b • α + fun _ => (a : ℤ))

section Inhabitants

abbrev lineIdx : Unit → Type := fun _ => Fin 2

def doublePointForm : MRingOver (ZMod 2) lineIdx :=
  monomial (Finsupp.single ⟨(), 0⟩ 2 + Finsupp.single ⟨(), 1⟩ 1) 1

end Inhabitants

section Ample

def KleimanSchemeAmple.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (V : Ideal (MRingOver F ι))
    (α : K → ℤ) (b a : ℕ),
    IsFieldIntersection I → IsMultiHomogIdeal V → KH.NefOnF I V α → 1 ≤ b → 1 ≤ a →
    KH.AmpleV F V (b • α + fun _ => (a : ℤ)) ∧
      ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → KH.GeneratedV F V (e + c • (b • α + fun _ => (a : ℤ)))

end Ample

section InhabitantCurve

abbrev planeIdx : Unit → Type := fun _ => Fin 3

def doubledLinesForm : MRingOver (ZMod 2) planeIdx :=
  monomial (Finsupp.single ⟨(), 0⟩ 2 + Finsupp.single ⟨(), 1⟩ 1) 1

def planeLineX0 : Ideal (MRingOver (ZMod 2) planeIdx) := Ideal.span {X ⟨(), 0⟩}

end InhabitantCurve

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
