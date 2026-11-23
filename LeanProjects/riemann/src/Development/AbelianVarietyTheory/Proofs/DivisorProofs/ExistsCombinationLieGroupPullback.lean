import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BLieLieComb

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

namespace GlobalTheory.FlatModel.TieComb

open GlobalTheory.HTLat.OmegaRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] {P : PtP E p}

theorem corr_lieComb : ∀ {g : ℕ} (U : Fin g → 𝓞_ℂ_[p]) (xb : Fin g → LieG P.Gt) (xG : Fin g → LieG P.G),
    (∀ b, Corr P (xb b).1 (xG b).1) → Corr P (lieComb P.Gt U xb).1 (lieComb P.G U xG).1
  | 0, _, _, _, _ => Corr.one
  | g + 1, U, xb, xG, h => by
    rw [lieComb_succ, lieComb_succ]
    exact Corr.mul (Corr.comp (dualScale (U 0)) (h 0))
      (corr_lieComb (Fin.tail U) (Fin.tail xb) (Fin.tail xG) fun b => h b.succ)

variable {yb : Sp 𝓞_ℂ_[p] ⟶ X} {π : P.G.left ⟶ t.G.left}

theorem prod_push (hP : IsGrpPullback P.G t.G yb π) :
    ∀ {g : ℕ} (U : Fin g → 𝓞_ℂ_[p]) (xG : Fin g → LieG P.G),
    (List.ofFn fun i => pushPt hP.1.w (AvDefs.lieScale P.G (U i) (xG i)).1).prod.left =
      (lieComb P.G U xG).1.left ≫ π
  | 0, U, xG => by
    rw [List.ofFn_zero, List.prod_nil, lieComb_zero]
    exact grpPull_one hP _
  | g + 1, U, xG => by
    rw [List.ofFn_succ, List.prod_cons, lieComb_succ]
    exact hP.2 _ _ _ _ _ rfl (prod_push hP (Fin.tail U) (Fin.tail xG))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0})
    (t : SAB H X) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (yb : Sp 𝓞_ℂ_[p] ⟶ X) (π : P.G.left ⟶ t.G.left),
    IsGrpPullback P.G t.G yb π → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left)) (xb : Fin g → LieG P.Gt),
    (∀ b, ITie P π (xb b) (e b)) → ∀ U : Fin g → 𝓞_ℂ_[p],
    ∃ u0 : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left, IsCombAtG t yb e U u0 ∧ ITie P π (lieComb P.Gt U xb) u0 := by
  intro E _ _ _ H X t p _ _ P yb π hP g e xb hT U
  choose xG hc he using hT
  refine ⟨(lieComb P.G U xG).1.left ≫ π, ⟨fun i => pushPt hP.1.w (AvDefs.lieScale P.G (U i) (xG i)).1, fun i => ?_,
    prod_push hP U xG⟩, lieComb P.G U xG, corr_lieComb U xb xG hc, rfl⟩
  rw [← he i]
  rfl

end GlobalTheory.FlatModel.TieComb
