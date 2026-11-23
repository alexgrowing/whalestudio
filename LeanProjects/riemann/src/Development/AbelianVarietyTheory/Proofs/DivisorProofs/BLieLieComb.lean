import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparisonStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel

noncomputable def lieComb {O : Type} [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G] :
    ∀ {m : ℕ}, (Fin m → O) → (Fin m → LieG G) → LieG G
  | 0, _, _ => lieZero G
  | _ + 1, a, x => lieAdd (AvDefs.lieScale G (a 0) (x 0)) (lieComb G (Fin.tail a) (Fin.tail x))

theorem lieComb_zero {O : Type} [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G]
    (a : Fin 0 → O) (x : Fin 0 → LieG G) : lieComb G a x = lieZero G := rfl

theorem lieComb_succ {O : Type} [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G]
    {m : ℕ} (a : Fin (m + 1) → O) (x : Fin (m + 1) → LieG G) :
    lieComb G a x = lieAdd (AvDefs.lieScale G (a 0) (x 0)) (lieComb G (Fin.tail a) (Fin.tail x)) := rfl

theorem bLie_lieComb {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p)
    {m : ℕ} (a : Fin m → 𝓞_ℂ_[p])
    (x : Fin m → LieG P.Gt) : P.bLie (lieComb P.Gt a x) = ∑ i, a i • P.bLie (x i) := by
  induction m with
  | zero => simp [lieComb_zero, P.bLie_zero]
  | succ m ih =>
    rw [lieComb_succ, P.bLie_add, P.bLie_scale, ih, Fin.sum_univ_succ]
    rfl

end GlobalTheory.FlatModel

end
