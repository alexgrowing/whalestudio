import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def IsPow8 {S : Scheme.{0}} (P P₈ : PolAV S) (d : ℕ) (pr : Fin 8 → (P₈.A ⟶ P.A)) (inc : P.A ⟶ P₈.A) : Prop :=
  (∀ u, IsMonHom (pr u)) ∧ IsMonHom inc ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ P.A)), ∃! x : T ⟶ P₈.A, ∀ u, x ≫ pr u = y u) ∧
    (∀ u, inc ≫ pr u = if u = 0 then 𝟙 P.A else 1) ∧ LBIso (P₈.L.pull inc.left) (lbPow P.L d)

def IsPow8F {K : Type} [Field K] [NumberField K] (F F₈ : SemiFib K) (d : ℕ) (e : Fin 8 × Fin F.P₀.g ≃ Fin F₈.P₀.g) : Prop :=
  ∃ (pr : Fin 8 → (F₈.P₀.A ⟶ F.P₀.A)) (inc : F.P₀.A ⟶ F₈.P₀.A) (prG : Fin 8 → (F₈.G ⟶ F.G)),
    IsPow8 F.P₀ F₈.P₀ d pr inc ∧ (∀ u, IsMonHom (prG u)) ∧
    (∀ (T : Over (Sp (𝓞 K))) (y : Fin 8 → (T ⟶ F.G)), ∃! x : T ⟶ F₈.G, ∀ u, x ≫ prG u = y u) ∧
    (∀ u, F₈.φ ≫ (prG u).left = (pr u).left ≫ F.φ) ∧
    ∀ u i u', F₈.v (e (u, i)) ≫ pr u' = if u = u' then F.v i else toUnit _ ≫ η[F.P₀.A]

end GlobalTheory.MBLow

end
