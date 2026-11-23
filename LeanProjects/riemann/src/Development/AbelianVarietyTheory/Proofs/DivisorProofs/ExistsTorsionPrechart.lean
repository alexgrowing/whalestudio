import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyClosedAnalyticNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDoubledDarbouxCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOpenLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleDenseOpenAnalyticStatement
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem nonempty_preChart : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ q : PrimeSpectrum R, Nonempty (PreChart G N q) := by
  intro R K _ _ _ _ _ _ _ _ G _ _ hG N hN q
  haveI := henselianLocalRing_atPrime R K q.asIdeal
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.torsion_kernel_finite_presentation R G hG N hN
  set π := pullback.fst ((𝟙 G) ^ N : G ⟶ G).left η[G].left ≫ G.hom with hπ
  obtain ⟨C', _, _, _, _, U', e', he', hcl⟩ := GlobalTheory.T.exists_finite_free_neighbourhood (Localization.AtPrime q.asIdeal)
    (pullback π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))))
    (pullback.snd π (spMap (algebraMap R (Localization.AtPrime q.asIdeal))))
  obtain ⟨r, hr, C, _, _, _, _, _, _, U, e, he, hq⟩ := GlobalTheory.T.finite_free_local_chart R q _ π C' U' e' he' hcl
  haveI : IsSeparated G.hom := hG.separated
  exact GlobalTheory.T.finite_free_affine_open R G N q r hr C U e (by simpa [hπ] using he) hq

end GlobalTheory.GroupBplus.Aff
