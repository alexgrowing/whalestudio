import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionNonemptyNonvanishing
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarisation_section_nonempty_nonvanishing : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S), IsIntegral (Over.mk t ⊗ P.A).left → ∃ θ : LB.Sec (LB.LinComb P.L (K := Fin 1) ![(snd (Over.mk t) P.A).left] ![1]), (nonzeroLocus θ : Set (Over.mk t ⊗ P.A).left).Nonempty := by
  first | exact @GlobalTheory.FibreTheta.exists_sec_nonempty | exact GlobalTheory.FibreTheta.exists_sec_nonempty | (intros; apply GlobalTheory.FibreTheta.exists_sec_nonempty <;> assumption)
