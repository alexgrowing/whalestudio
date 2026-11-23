import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrechartTranslationMap
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
theorem _root_.GlobalTheory.T.prechart_translation_map : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ∀ (N : ℕ) (q : PrimeSpectrum R) (c : PreChart G N q), c.IsGrp → ∀ ψ₀ : c.C →ₐ[R] K, ∃ T : c.C →ₐ[R] c.C, ∀ ψ : c.C →ₐ[R] K, torsMap (ψ.comp T) c.j = torsMap ψ₀ c.j * torsMap ψ c.j := by
  first | exact @GlobalTheory.GroupBplus.Aff.PreChart.exists_translation | exact GlobalTheory.GroupBplus.Aff.PreChart.exists_translation | (intros; apply GlobalTheory.GroupBplus.Aff.PreChart.exists_translation <;> assumption)
