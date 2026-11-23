import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.LevelLetterCocycles.SmallTwists.RowSmall

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace UpperTheory.N

def costC {D : D7} (L : SizeData₂ D) (A B : ℝ) (l : ℕ) : ℝ :=
  A * D.R.f * D.R.m * RowSmall.hB L * (RowSmall.sl D l : ℝ) +
    B * (D.R.f : ℝ) ^ 2 * (D.R.t : ℝ) ^ 2 * D.R.nV * RowSmall.abelian₂ L l

def BoundSmall : Prop := ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
    (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
    (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
    Setup (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ →
      RowSmall.RowSplitAt (Fm.L x i) (fun k => (Fm.D x i).nd.l k ∈ (Fm.D x i).host.small)
        (fun k π => (Br.sPi (Fm.D x i).loc (Fm.D x i).nbr k (X.ρ k) π : ℝ))

def RowAt {D : D7} (L : SizeData₂ D) (ρ : FamilyRepresentationConstants.RhoFam D) (A B : ℝ) : Prop :=
  ∀ k, TwistedPlaces.TwLoc D k → D.nd.l k ∈ D.host.small → D.nd.l k ≠ 2 → ∀ π ∈ D.nd.Zgood k, Bd ρ k π (costC L A B (D.nd.l k))

def RowC (A B : ℝ) : Prop := ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
    (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
    (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
    Setup (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ →
      RowAt (Fm.L x i) X.ρ A B

def StarSF : Prop := ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
    (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
    (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
    Setup (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ →
      StarS (Fm.L x i) X.ρ C

end UpperTheory.N

end
