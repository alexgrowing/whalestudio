import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

def LieModel.IsHTFormOver (M : LieModel G ξ E) (N : ℕ) {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ X)
    (k : R →+* Ω) (w : Module.Dual Ω E) : Prop :=
  ∃ (_ : IsDomain R) (T : Type) (_ : CommGroup T) (Γ : BT.QFGroup R T)
    (i : Γ.G.left ⟶ G.left) (L : Type) (_ : AddCommGroup L) (_ : Module R L)
    (M₀ : LieModel G x L) (j : L → E) (χ : T →* Rˣ) (w₀ : Module.Dual R L),
    Γ.IsTorsionAlong G x N i ∧ (∀ e, (M.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left) ∧
      Γ.IsHT i M₀ N χ w₀ ∧ ∀ e, w (j e) = k (w₀ e)

def LieModel.IsHTFormAt (M : LieModel G ξ E) (N : ℕ) (p : Cpt ξ) (w : Module.Dual Ω E) : Prop :=
  M.IsHTFormOver N (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) (genMap ξ p) w

def LieModel.htLat (M : LieModel G ξ E) (N : ℕ) : Lat ξ (Module.Dual Ω E) := fun p =>
  Submodule.span (regAt ξ p) {w | M.IsHTFormAt N p w}

end GlobalTheory.CompanionTheory.Ar
