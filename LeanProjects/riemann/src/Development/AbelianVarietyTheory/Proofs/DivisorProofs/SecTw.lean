import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def SecTw {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Sp (FractionRing R))} {N : ℕ}
    (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) : Prop :=
  ∀ (Z : Scheme.{0}) (p p' : Z ⟶ (TFK (R := R) (Kb R) ⊗ A.A).left),
    p' ≫ (snd (TFK (R := R) (Kb R)) A.A).left = p ≫ (snd (TFK (R := R) (Kb R)) A.A).left →
    p' ≫ (fst (TFK (R := R) (Kb R)) A.A).left = p ≫ (fst (TFK (R := R) (Kb R)) A.A).left ≫ spMap σ.toRingHom →
    ∀ z J, Good A.L z J → sval t' p z J = sval t p' z J
end GlobalTheory.Mum
