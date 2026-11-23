import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrOverHeightOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_over_height_one : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A] [CharZero A] (𝔭 : PrimeSpectrum A), 𝔭.asIdeal.height = 1 → ∃ (T : CDVR) (iT : Localization.AtPrime 𝔭.asIdeal →+* T.V), Function.Injective iT ∧ IsLocalHom iT := by
  first | exact @GlobalTheory.HeightOneCompletion.exists_cdvr_of_height_eq_one | exact GlobalTheory.HeightOneCompletion.exists_cdvr_of_height_eq_one | (intros; apply GlobalTheory.HeightOneCompletion.exists_cdvr_of_height_eq_one <;> assumption)
