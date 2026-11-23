import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionChartSpreadsToFiniteFree
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
theorem _root_.GlobalTheory.T.torsion_chart_spreads_to_finite_free : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (q : PrimeSpectrum R) (c : PreChart G N q), c.IsGrp → ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F) (_ : Module (Localization.Away c.r) F) (_ : IsScalarTower R (Localization.Away c.r) F) (_ : Module.Finite (Localization.Away c.r) F) (_ : Module.Free (Localization.Away c.r) F) (ϕ : ord G N K →ₗ[R] F), IsLocalizedModule (Submonoid.powers c.r) ϕ := by
  first | exact @GlobalTheory.OrdLocProd.ord_isLocalizedModule | exact GlobalTheory.OrdLocProd.ord_isLocalizedModule | (intros; apply GlobalTheory.OrdLocProd.ord_isLocalizedModule <;> assumption)
