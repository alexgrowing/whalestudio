import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFockVectorHeisenbergAverageIsotropicEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFockVector_heisenbergAverage_isotropic_eq_zero : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m om BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m om BW f₀ f c io → ∀ Q h g ξ, IsoVec (Wc D i) ξ → ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → Fin (Vc D i).rank → AE D, ∑ k, heisO R.ψ (Vc D i) (Wc D i) (along (Vc D i) (Wc D i) ξ (a k)) (om (h, g) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ BW f Q)) = 0 := by
  first | exact @GlobalTheory.LevelSupport.sum_heisO_along_eq_zero_level | exact GlobalTheory.LevelSupport.sum_heisO_along_eq_zero_level | (intros; apply GlobalTheory.LevelSupport.sum_heisO_along_eq_zero_level <;> assumption)
