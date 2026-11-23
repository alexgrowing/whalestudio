import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory

namespace CompanionTheory.Affgl

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def Cofin (J : Set (Module.End ℂ (Sm E a))) : Prop :=
  J ⊆ Zalg E a ∧ ∃ V : Submodule ℂ (Module.End ℂ (Sm E a)), FiniteDimensional ℂ V ∧
    ∀ z ∈ Zalg E a, z ∈ V ⊔ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j}

def genSpace (L : Subgroup (GL (Fin a) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))) : Set (Sm E a) :=
  {φ | IsAutForm φ ∧ (∀ k ∈ L, finRep E a k φ = φ) ∧
    (∀ g : GA E a, (fun k : Kinf E a => (cptRep E a k φ).1 g) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧ ∀ z ∈ J, z φ = 0}

variable (E a) in

def GenFin : Prop :=
  ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W),
    GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J →
    FiniteDimensional ℂ (Submodule.span ℂ (genSpace L ρ J))

variable (E a) in

def CuspFin : Prop :=
  ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W),
    GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J →
    FiniteDimensional ℂ (Submodule.span ℂ {φ | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1})

variable (E a) in

def CTFin (r : ℕ) : Prop :=
  ∀ (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W),
    GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J →
    ∃ V : Submodule ℂ (GA E a → ℂ), FiniteDimensional ℂ V ∧
      ∀ φ ∈ genSpace L ρ J, ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
        (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratN E a r) 𝓕 μ → (fun g => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) ∈ V

end CompanionTheory.Affgl

end
