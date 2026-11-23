import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingAntisymmetricOfSymmetric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pairing_antisymmetric_of_symmetric : GlobalTheory.Published.CubeTheorem → ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (P : LB (A ⊗ A).left), IsDual A A P → LBIso (swap P) P → ∀ (𝒜 : PDivGroup p K) (t : 𝒜.TorsionTower A) (w : 𝒜 ⟶ 𝒜.dual), IsWeilHom t t P w → 𝒜.bidual.hom ≫ dualHom _ _ w = -w := by
  first | exact @GlobalTheory.WeilAntisymm.bidual_dualHom_eq_neg | exact GlobalTheory.WeilAntisymm.bidual_dualHom_eq_neg | (intros; apply GlobalTheory.WeilAntisymm.bidual_dualHom_eq_neg <;> assumption)
