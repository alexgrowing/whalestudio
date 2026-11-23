import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.SuccessiveMinima.StatementMink

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions

def MinkowskiFinGL : Prop :=
  ∀ (n : ℕ) (G : Subgroup (GL (Fin n) ℤ)), Finite G →
    Nat.card G ∣ ∏ p ∈ (Finset.range (n + 2)).filter Nat.Prime,
      p ^ (∑ i ∈ Finset.range (n + 1), n / (p ^ i * (p - 1)))

def Transference : Prop :=
  ∀ (r : ℕ) (L Ld : Submodule ℤ (EuclideanSpace ℝ (Fin r))) [DiscreteTopology L] [IsZLattice ℝ L],
    (∀ x, x ∈ Ld ↔ ∀ y ∈ L, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) →
    ∀ i : ℕ, 1 ≤ i → i ≤ r →
      Formalism.FN.succMinBall L i * Formalism.FN.succMinBall Ld (r + 1 - i) ≤ (r : ℝ)

def SecondTheoremImpliesFirst : Prop := Formalism.MainNotions.flipTwoThree.HookLengthFactorialBound

def LinkSup : Prop := ∀ D : D7, Formalism.MainNotions.flipTwoThree.ThetaSupremumBound D

def LinkSupF : Prop := ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), Formalism.MainNotions.flipTwoThree.FamilySupremumBound Fm

def Link3 : Prop := ∀ D : D7, Formalism.MainNotions.flipTwoThree.PointsLemma D

def Link3F : Prop := ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), Formalism.MainNotions.flipTwoThree.ConclusionF3 Fm

def LinkPF : Prop := ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), Formalism.MainNotions.flipTwoThree.admF6 Fm → Formalism.MainNotions.flipTwoThree.FamilyProjectionEstimate Fm

def ClassCompatibilityOfRowCompatibility : Prop :=
  ∀ D : D7, Formalism.L2.Herm.FullTied D → ∀ u : D.what₂.Word, Formalism.MainNotions.flipTwoThree.ClsTie D u

def ColumnValuationOfRowCompatibility : Prop :=
  ∀ D : D7, Formalism.L2.Herm.FullTied D → (∀ u, Formalism.L2.Forms.FormsTied D u) → Formalism.MainNotions.flipTwoThree.adm3 D →
    ∀ u : D.what₂.Word, Nonempty (Formalism.MainNotions.flipTwoThree.ColVal D u)

def SignHypothesisOfCompatibleFrame : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps),
    (∀ (x : ℝ) (i : Fm.Ix x) u, Formalism.L2.Forms.FormsTied (Fm.D x i) u) →
    ∃ Cn x0 : ℝ, ∀ x : ℝ, x0 ≤ x → Fm.x1 < x → ∀ (i : Fm.Ix x) u,
      Formalism.MainNotions.flipTwoThree.SgHyp (Fm.D x i) u Cn (Fm.L x i).Sc (Fm.L x i).etaSz

def Link1F : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), (∀ (x : ℝ) (i : Fm.Ix x), Formalism.L2.Herm.FullTied (Fm.D x i)) →
    Transference → Formalism.MainNotions.flipTwoThree.ConclusionF1 Fm

def Link2F : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), (∀ (x : ℝ) (i : Fm.Ix x), Formalism.L2.Herm.FullTied (Fm.D x i)) →
    (∀ (x : ℝ) (i : Fm.Ix x) u, Formalism.L2.Forms.FormsTied (Fm.D x i) u) →
    MinkowskiFinGL → Transference → Formalism.MainNotions.flipTwoThree.admF2 Fm → Formalism.MainNotions.flipTwoThree.ConclusionF2 Fm

def Link4F : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), (∀ (x : ℝ) (i : Fm.Ix x), Formalism.L2.Herm.FullTied (Fm.D x i)) →
    (∀ (x : ℝ) (i : Fm.Ix x) u, Formalism.L2.Forms.FormsTied (Fm.D x i) u) →
    MinkowskiFinGL → Transference → Formalism.MainNotions.flipTwoThree.admF1 Fm → Formalism.MainNotions.flipTwoThree.admF2 Fm → Formalism.MainNotions.flipTwoThree.admF6 Fm →
    Formalism.MainNotions.flipTwoThree.FamilyEstimateFour Fm

def Link5F : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), (∀ (x : ℝ) (i : Fm.Ix x), Formalism.L2.Herm.FullTied (Fm.D x i)) →
    (∀ (x : ℝ) (i : Fm.Ix x) u, Formalism.L2.Forms.FormsTied (Fm.D x i) u) →
    Formalism.GradedWeylDivisibility.NablaEqDualWeyl → Formalism.MainNotions.flipTwoThree.ConclusionF5 Fm

def Link6F : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), (∀ (x : ℝ) (i : Fm.Ix x), Formalism.L2.Herm.FullTied (Fm.D x i)) →
    (∀ (x : ℝ) (i : Fm.Ix x) u, Formalism.L2.Forms.FormsTied (Fm.D x i) u) →
    Transference → Formalism.MainNotions.flipTwoThree.ConclusionF6 Fm

def KudlaFamilyOfMinkowskiTransference : Prop :=
  ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), (∀ (x : ℝ) (i : Fm.Ix x), Formalism.L2.Herm.FullTied (Fm.D x i)) →
    (∀ (x : ℝ) (i : Fm.Ix x) u, Formalism.L2.Forms.FormsTied (Fm.D x i) u) →
    MinkowskiFinGL → Transference → Formalism.GradedWeylDivisibility.NablaEqDualWeyl → Formalism.MainNotions.flipTwoThree.KudlaFamilyStatement Fm

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
