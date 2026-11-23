import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.AnalyticForms.RegularLocalRings.LogResStC

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.ResK

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

variable {K : Type} [Field K]

def preRed {X X' : Scheme.{0}} (f : X' ⟶ X) (T : Set X) (hT : IsClosed T) : X'.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨f.base ⁻¹' T, IsClosed.preimage f.base.hom.continuous hT⟩

@[instance_reducible]
def secAlgebra {Y : Scheme.{0}} (g : Y ⟶ Sp K) (V : Y.Opens) : Algebra K Γ(Y, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appLE ⊤ V (fun _ _ => trivial)).hom.toAlgebra

def IsCoords {Y : Scheme.{0}} (g : Y ⟶ Sp K) (V : Y.Opens) {D : ℕ} (z : Fin D → Γ(Y, V)) : Prop :=
  letI := secAlgebra g V
  LinearIndependent Γ(Y, V) (fun i => KaehlerDifferential.D K Γ(Y, V) (z i)) ∧
    Submodule.span Γ(Y, V) (Set.range fun i => KaehlerDifferential.D K Γ(Y, V) (z i)) = ⊤

def HasSncCoords {Y : Scheme.{0}} (g : Y ⟶ Sp K) (D : ℕ) (T : Set Y) : Prop :=
  ∃ (n : ℕ) (V : Fin n → Y.affineOpens), (∀ y : Y, ∃ j, y ∈ (V j : Y.Opens)) ∧
    ∀ j, ∃ (z : Fin D → Γ(Y, (V j : Y.Opens))) (k : ℕ), k ≤ D ∧ IsCoords g (V j) z ∧
      ((V j : Y.Opens) : Set Y) ∩ T =
        {y | y ∈ (V j : Y.Opens) ∧ ∃ i : Fin D, (i : ℕ) < k ∧ y ∉ Y.basicOpen (z i)}

def BlowupResStatement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (X : Scheme.{0}) (g : X ⟶ Sp K) (U : X.Opens),
    LocallyOfFiniteType g → QuasiCompact g → IsSeparated g → IsReduced X → Dense (U : Set X) →
    Smooth (U.ι ≫ g) →
    ∃ (J : X.IdealSheafData) (X' : Scheme.{0}) (f : X' ⟶ X),
      (J.support : Set X) ⊆ (U : Set X)ᶜ ∧ FinalTheorems.Blowup f J ∧ FinalTheorems.ReesCharts f J ∧
        Smooth (f ≫ g) ∧ IsProper f ∧ IsIso (f ∣_ U) ∧ Dense ((f ⁻¹ᵁ U : X'.Opens) : Set X') ∧
        FinalTheorems.Snc (preRed f (U : Set X)ᶜ U.isOpen.isClosed_compl)

def BlowupProjStatement : Prop :=
  ∀ (K : Type) [Field K] (M : ℕ) (X : Scheme.{0}) (i : X ⟶ PSpace K M), IsClosedImmersion i →
    ∀ (J : X.IdealSheafData) (X' : Scheme.{0}) (f : X' ⟶ X), FinalTheorems.Blowup f J →
      ∃ (r : ℕ) (j : X' ⟶ pullback (PSpace.str K M) (PSpace.str K r)),
        IsClosedImmersion j ∧ f ≫ i = j ≫ pullback.fst _ _

def CoordsStatement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K) (W : Y.Opens)
    (T : Set Y) (hT : IsClosed T),
    CompactSpace Y → Smooth g → Dense (W : Set Y) → SmoothOfRelativeDimension D (W.ι ≫ g) →
    FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩) →
    SmoothOfRelativeDimension D g ∧ HasSncCoords g D T

def IsResInput {X : Scheme.{0}} (M : ℕ) (i : X ⟶ PSpace K M) (U : X.Opens) (D : ℕ) : Prop :=
  IsClosedImmersion i ∧ IsReduced X ∧ Dense (U : Set X) ∧
    SmoothOfRelativeDimension D (U.ι ≫ i ≫ PSpace.str K M)

def IsResWithCoords {X X' : Scheme.{0}} (g : X ⟶ Sp K) (U : X.Opens) (D : ℕ) (f : X' ⟶ X) : Prop :=
  SmoothOfRelativeDimension D (f ≫ g) ∧ IsIso (f ∣_ U) ∧
    Dense ((f ⁻¹ᵁ U : X'.Opens) : Set X') ∧ HasSncCoords (f ≫ g) D (f.base ⁻¹' (U : Set X)ᶜ)

def ResKPropStatement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (M D : ℕ) (X : Scheme.{0}) (i : X ⟶ PSpace K M) (U : X.Opens),
    IsResInput M i U D →
    ∃ (X' : Scheme.{0}) (f : X' ⟶ X),
      IsProper f ∧ IsProper (f ≫ i ≫ PSpace.str K M) ∧ IsResWithCoords (i ≫ PSpace.str K M) U D f

def ResKStatement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (M D : ℕ) (X : Scheme.{0}) (i : X ⟶ PSpace K M) (U : X.Opens),
    IsResInput M i U D →
    ∃ (r : ℕ) (X' : Scheme.{0}) (j : X' ⟶ pullback (PSpace.str K M) (PSpace.str K r)) (f : X' ⟶ X),
      IsClosedImmersion j ∧ f ≫ i = j ≫ pullback.fst _ _ ∧ IsResWithCoords (i ≫ PSpace.str K M) U D f

end ReciprocityTheory.ChartRestriction.G.Geo.ResK
