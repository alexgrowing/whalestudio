import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisiblePolarizationLiftGenericFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pdivisible_polarization_lift_generic_fibre : GlobalTheory.Published.BarsottiTateDieudonne.WittModule → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (hR : (p : R) = 0) (hK : (p : K) = 0) (Γ' : PDivGroup p R) (𝒜 : PDivGroup p K) (κ : Γ'.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt], Function.Bijective (omegaMap _ _ κ) → Function.Bijective (vecExtMap w) → ∀ h : Γ' ⟶ Γ'.dual, PDivGroup.baseChangeMap K h = κ ≫ weilProj κ w → (lattice κ w).FG ∧ lattice κ w ⊓ (LinearMap.range 𝒜.rigOfOmega).restrictScalars R = latOmega κ := by
  first | exact @GlobalTheory.BadPt.lattice_fg_and_inf_range | exact GlobalTheory.BadPt.lattice_fg_and_inf_range | (intros; apply GlobalTheory.BadPt.lattice_fg_and_inf_range <;> assumption)
