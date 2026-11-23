import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldingSchurOrthogonalityDefiniteCoefficients
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_schur_orthogonality_definite_coefficients : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (t : T) (h h' : (R.HX t).H) (a a' : R.cX.W), IntegrableOn (fun g => star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ) (R.fdX t) (R.νX t) ∧ (Module.finrank ℂ R.cX.W : ℂ) * ∫ g in R.fdX t, star ⟪a, R.cX.ext ((R.HX t).e h) g⟫_ℂ * ⟪a', R.cX.ext ((R.HX t).e h') g⟫_ℂ ∂(R.νX t) = ⟪a', a⟫_ℂ * ⟪h, h'⟫_ℂ := by
  first | exact @GlobalTheory.Mem.SchurW.schurW | exact GlobalTheory.Mem.SchurW.schurW | (intros; apply GlobalTheory.Mem.SchurW.schurW <;> assumption)
