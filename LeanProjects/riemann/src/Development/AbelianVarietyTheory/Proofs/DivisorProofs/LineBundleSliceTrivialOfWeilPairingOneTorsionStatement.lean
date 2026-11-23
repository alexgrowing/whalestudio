import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSliceTrivialOfWeilPairingOneTorsion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_slice_trivial_of_weilPairing_one_torsion : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), (n : k) ≠ 0 → ∀ a : Over.mk x ⟶ A, a ^ n = 1 → (∀ b : Over.mk x ⟶ A, b ^ n = 1 → Out.WeilIs (G2 A) P (n : ℤ) (lift a 1) (lift 1 b) 1) → (∃ t : (P.pull (lift (snd A (Over.mk x) ≫ a) (fst A (Over.mk x))).left).Gen, t.IsGen) := by
  first | (exact @GlobalTheory.WeilKernel.triv_slice_of_forall_weilIs_one) | (exact GlobalTheory.WeilKernel.triv_slice_of_forall_weilIs_one) | (intros; apply GlobalTheory.WeilKernel.triv_slice_of_forall_weilIs_one  <;> assumption)
