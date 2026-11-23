import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsDehomogenisationTwistedChart
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dehomogenisation_twisted_chart : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∀ (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (i : Fin (m + 1)) (r : Fin (m + 1) → Γ(Y, nonzeroLocus (s i))), (∀ j k, rs Y (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) = rs Y (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r j) * rs Y (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k)) → r i = 1 ∧ ∃ ε : GrSum (hx ⊤) →ₛₗ[MvPolynomial.eval₂Hom (cst f (nonzeroLocus (s i))) r] SecOn (tw M H 0) (nonzeroLocus (s i)), Function.Surjective ε ∧ (∀ n, ∀ y ∈ GrSum.grading (hx ⊤) n, ε y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k • y = 0) ∧ ∀ a : SecOn (tw M H 0) ⊤, ε (GrSum.of (hx ⊤) 0 (SecOnR.of f _ ⊤ a)) = SecOn.restrict _ le_top a := by
  first | exact @GlobalTheory.AbLaw.exists_dehom_chart | exact GlobalTheory.AbLaw.exists_dehom_chart | (intros; apply GlobalTheory.AbLaw.exists_dehom_chart <;> assumption)
