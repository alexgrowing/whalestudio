import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.familyUniformisation_fibre_theta : ThetaUnifAV → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)),
  IsPeriod (FU.Di i) ty Pe → ∀ (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ Xo.univ.t.G.left),
  IsGrpPullback P.A Xo.univ.t.G (FU.u i Pe) φ → LBIso P.L (Xo.univ.t.PP.L.pull φ) →
  ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ)),
    u.IsAH Hm χ ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
    (∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) ∧
    (∀ z, (u.ex (F z)).left ≫ φ = (FU.ex i Pe z).left) ∧ (∀ z, F z ∈ u.Λ ↔ z ∈ Pe.range) ∧
    ∀ a b, (hermForm Hm (F (Pe a)) (F (Pe b))).im = (FU.Di i).EF a b := by
  first | exact @GlobalTheory.familyUnif_fibre_theta | exact GlobalTheory.familyUnif_fibre_theta | (intros; apply GlobalTheory.familyUnif_fibre_theta <;> assumption)
