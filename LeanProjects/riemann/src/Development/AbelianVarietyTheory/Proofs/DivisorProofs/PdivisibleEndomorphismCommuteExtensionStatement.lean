import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleEndomorphismCommuteExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pdivisible_endomorphism_commute_extension : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (hR : (p : R) = 0) (hK : (p : K) = 0) (Γ' : PDivGroup p R) (𝒜 : PDivGroup p K) (κ : Γ'.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt] (f f' : 𝒜 ⟶ 𝒜) (g g' : Γ' ⟶ Γ'), PDivGroup.baseChangeMap K g ≫ κ = κ ≫ f → PDivGroup.baseChangeMap K g' ≫ κ = κ ≫ f' → f ≫ w = w ≫ dualHom _ _ f' → ∀ x ∈ lattice κ w, rigExtMap f x ∈ lattice κ w := by
  first | exact @GlobalTheory.BadPt.lattice_stable | exact GlobalTheory.BadPt.lattice_stable | (intros; apply GlobalTheory.BadPt.lattice_stable <;> assumption)
