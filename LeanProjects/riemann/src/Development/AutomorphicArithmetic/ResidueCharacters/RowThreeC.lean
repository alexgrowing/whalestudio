import Development.AutomorphicArithmetic.ResidueCharacters.RowDef

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace UpperTheory.N

def RowOnAt {D : D7} (L : SizeData₂ D) (ρ : FamilyRepresentationConstants.RhoFam D) (Q : ℕ → Prop) (A B : ℝ) : Prop :=
  ∀ k, TwistedPlaces.TwLoc D k → Q (D.nd.l k) → ∀ π ∈ D.nd.Zgood k, Bd ρ k π (costC L A B (D.nd.l k))

def RowOn (Q : D7 → ℕ → Prop) (A B : ℝ) : Prop := ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0,
    ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
    (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
    (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
    Setup (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ →
      RowOnAt (Fm.L x i) X.ρ (Q (Fm.D x i)) A B

def RowTwoC (A B : ℝ) : Prop := RowOn (fun _ l => l = 2) A B

def RowThreeC (A B : ℝ) : Prop := RowOn (fun D l => l = 3 ∧ l ∉ D.host.small) A B

end UpperTheory.N

end
