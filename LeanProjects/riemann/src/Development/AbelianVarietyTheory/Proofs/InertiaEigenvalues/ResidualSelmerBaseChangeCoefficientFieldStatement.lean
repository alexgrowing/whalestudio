import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBaseChangeCoefficientField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFCocIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residualSelmer_baseChange_coefficientField : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (k : Type) [Field k] [Algebra (X.O0 i) k] [TopologicalSpace k] [DiscreteTopology k] (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i k → Function.Surjective (algebraMap (X.O0 i) k) → IsRes i K → ∀ Q : Finset (PlE D.host), Module.Finite k (selOn bkP i ρ (1 : GE N →* kˣ) k Q) → Module.Finite K (selOn bkP i ρ (1 : GE N →* Kˣ) K Q) ∧ Module.finrank K (selOn bkP i ρ (1 : GE N →* Kˣ) K Q) = Module.finrank k (selOn bkP i ρ (1 : GE N →* kˣ) k Q) := by
  first | exact @GlobalTheory.ResSel.BaseChange.selOn_baseChange | exact GlobalTheory.ResSel.BaseChange.selOn_baseChange | (intros; apply GlobalTheory.ResSel.BaseChange.selOn_baseChange <;> assumption)
