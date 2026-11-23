import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyClosedAnalyticNonempty
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
theorem _root_.GlobalTheory.T.torsion_kernel_finite_presentation : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 →
    IsSeparated (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom) ∧
      LocallyOfFinitePresentation (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom) ∧
      QuasiCompact (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom) ∧
      QuasiSeparated (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom) ∧
      LocallyQuasiFinite (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom) ∧
      Flat (pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom) := by
  first | exact @GlobalTheory.SemiAbKer.kernel_props | exact GlobalTheory.SemiAbKer.kernel_props | (intros; apply GlobalTheory.SemiAbKer.kernel_props <;> assumption)
