import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleInclusionCompatibleTowers
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pdivisible_inclusion_compatible_towers : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G (spMap (algebraMap R K)) φ → ∀ (Γ' : PDivGroup p R) (s : FinTower Γ' G) (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A) (κ : Γ'.baseChange K ⟶ 𝒜), s.IsIncl t φ κ → ∀ (f : G ⟶ G) (f' : A ⟶ A) [IsMonHom f] [IsMonHom f'], f'.left ≫ φ = φ ≫ f.left → ∃ g : Γ' ⟶ Γ', PDivGroup.baseChangeMap K g ≫ κ = κ ≫ t.map t f' := by
  first | exact @GlobalTheory.BadPt.exists_finTower_endo | exact GlobalTheory.BadPt.exists_finTower_endo | (intros; apply GlobalTheory.BadPt.exists_finTower_endo <;> assumption)
