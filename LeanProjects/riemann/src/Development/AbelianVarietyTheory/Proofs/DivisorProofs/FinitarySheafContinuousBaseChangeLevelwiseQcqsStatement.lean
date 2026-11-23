import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitarySheafContinuousBaseChangeLevelwiseQcqs
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitarySheaf_continuous_baseChange_levelwiseQcqs : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S), QcqsOver p → (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F ((bc p).mapCone c)) := by
  first
  | exact @GlobalTheory.EtC.contCone_bc_qcqsOver
  | exact GlobalTheory.EtC.contCone_bc_qcqsOver
  | (intros; apply GlobalTheory.EtC.contCone_bc_qcqsOver <;> assumption)
