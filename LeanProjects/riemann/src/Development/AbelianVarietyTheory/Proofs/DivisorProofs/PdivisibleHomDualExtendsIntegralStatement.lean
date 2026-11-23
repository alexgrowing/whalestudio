import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleHomDualExtendsIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pdivisible_hom_dual_extends_integral : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (hR : (p : R) = 0) (hK : (p : K) = 0) (Γ' : PDivGroup p R) (𝒜 : PDivGroup p K) (κ : Γ'.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt], Function.Bijective (omegaMap _ _ κ) → Function.Bijective (vecExtMap w) → ∀ h : Γ' ⟶ Γ'.dual, PDivGroup.baseChangeMap K h = κ ≫ weilProj κ w → ∀ x ∈ lattice κ w, ∃ (n : ℕ) (r : Fin n → R) (y : Fin n → 𝒜.RigExt), (∀ i, y i ∈ latOmega κ) ∧ rigExtMap (verschiebung hK 𝒜) x = ∑ i, algebraMap R K (r i) • (frobProj hK 𝒜).rig (y i) := by
  first | exact @GlobalTheory.BadPt.rigExtMap_verschiebung_lattice | exact GlobalTheory.BadPt.rigExtMap_verschiebung_lattice | (intros; apply GlobalTheory.BadPt.rigExtMap_verschiebung_lattice <;> assumption)
