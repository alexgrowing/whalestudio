import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.IsPullbackH2Structure
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge

def FlatBCSt : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R)
    (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s →
    QuasiCompact s → ∃ e : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s', ∀ c, IsPullO h.w c (e (1 ⊗ₜ c))

def FewEqSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (n : ℕ),
    Smooth s → IsProper s →
    (∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp (IsLocalRing.ResidueField R)) (φ : X' ⟶ X),
      IsPullback φ s' s (spMap (algebraMap R (IsLocalRing.ResidueField R))) →
      Module.Finite (IsLocalRing.ResidueField R) (HO1 s') ∧
        Module.finrank (IsLocalRing.ResidueField R) (HO1 s') ≤ n) →
    ∀ M : LB X, M.IsLB → ∀ I : Ideal R, I ≠ ⊤ →
    (∀ J : Ideal R, Triv (M.pull (pullback.fst s (spMap (Ideal.Quotient.mk J)))) ↔ I ≤ J) →
    ∃ f : Fin n → R, Ideal.span (Set.range f) = I

def StalkDimSt : Prop :=
  ∀ (k : Type) [Field k] (X : Scheme.{0}) (s : X ⟶ Sp k) (e : Sp k ⟶ X) (g : ℕ), e ≫ s = 𝟙 _ →
    SmoothOfRelativeDimension g s → ∀ p : Sp k, ringKrullDim (X.presheaf.stalk (e.base p)) = g

def H1DimGeAbelianDim : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → Module.Finite k (HO1 A.hom) → g ≤ Module.finrank k (HO1 A.hom)

end MainStatements.Hodge
