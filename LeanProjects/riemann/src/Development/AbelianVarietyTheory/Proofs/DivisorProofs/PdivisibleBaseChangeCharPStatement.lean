import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleBaseChangeCharP
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pdivisible_base_change_char_p : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A] (φ : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G (spMap (algebraMap R K)) φ → ∀ (Γ' : PDivGroup p R) (s : FinTower Γ' G) (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A) (κ : Γ'.baseChange K ⟶ 𝒜), (p : R) = 0 → s.IsIncl t φ κ → ∀ (hA : IsAbelianScheme A) (e : GlobalTheory.Published.DeRhamVectorExtension.Family p), e.Filtered → e.Tangent → ∀ (hn : IsNilpotent (p : K)) [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt] [Module R (primDR A)] [IsScalarTower R K (primDR A)] (c : primDR A), c ∈ intForms G A φ ↔ e hn hA t c ∈ latOmega κ := by
  first | exact @GlobalTheory.BadPt.mem_intForms_iff | exact GlobalTheory.BadPt.mem_intForms_iff | (intros; apply GlobalTheory.BadPt.mem_intForms_iff <;> assumption)
