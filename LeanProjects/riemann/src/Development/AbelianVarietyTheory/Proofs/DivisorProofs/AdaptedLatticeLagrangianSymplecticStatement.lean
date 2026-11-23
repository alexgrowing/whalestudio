import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedLatticeLagrangianSymplectic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_lattice_lagrangian_symplectic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (H : Type 1) [AddCommGroup H] [Module K H] [Module R H] [IsScalarTower R K H] [Module.Finite K H] (β : LinearMap.BilinForm K H) (F C : Submodule K H) (Λ : Submodule R H), Function.Injective β → (∀ s w, β s w = - β w s) → IsLagr β F → IsLagr β C → Λ.FG → IsAdapted β F (Λ ⊓ F.restrictScalars R) Λ → Λ ≤ β.dualSubmodule (Λ ⊓ C.restrictScalars R) → IsAdapted β C (Λ ⊓ C.restrictScalars R) Λ := by
  first | exact @GlobalTheory.BadPt.isAdapted_of_le_dualSubmodule | exact GlobalTheory.BadPt.isAdapted_of_le_dualSubmodule | (intros; apply GlobalTheory.BadPt.isAdapted_of_le_dualSubmodule <;> assumption)
