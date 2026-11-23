import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleDenseOpenAnalytic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_free_affine_open : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [IsSeparated G.hom]
    (N : ℕ) (q : PrimeSpectrum R) (r : R), r ∉ q.asIdeal → ∀ (C : Type) [CommRing C] [Algebra R C]
    [Algebra (Localization.Away r) C] [IsScalarTower R (Localization.Away r) C] [Module.Finite (Localization.Away r) C]
    [Module.Free (Localization.Away r) C] (U : (pullback ((𝟙 G) ^ N : G ⟶ G).left η[G].left).Opens)
    (e : Sp C ≅ U.toScheme),
    e.hom ≫ U.ι ≫ pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom = spMap (algebraMap R C) →
    (∀ t, (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom) t = q → t ∈ U) →
    Nonempty (PreChart G N q) := by
  first | exact @GlobalTheory.GroupBplus.Aff.preChart_of_open | exact GlobalTheory.GroupBplus.Aff.preChart_of_open | (intros; apply GlobalTheory.GroupBplus.Aff.preChart_of_open <;> assumption)
