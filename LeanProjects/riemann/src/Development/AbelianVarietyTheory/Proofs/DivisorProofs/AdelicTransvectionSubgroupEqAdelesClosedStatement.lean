import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTransvectionSubgroupEqAdelesClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicTransvectionSubgroup_eq_adeles_closed : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ ξ, IsoVec V ξ → (∃ e : Multiplicative (AF D.host.F) ≃ₜ* ZI V ξ, (∀ a, ((e a : ZI V ξ) : GA D V) ∈ GQ V ↔ Multiplicative.toAdd a ∈ Set.range (algebraMap D.host.F (AF D.host.F)))) ∧ IsClosed (ZI V ξ : Set (GA D V)) ∧ (∀ z ∈ ZI V ξ, ∀ τ, InZe (gramAt D V τ) (fun i => tauE D τ (ξ i)) (archM V (θ τ) z)) ∧ (∀ m : D.what₂.Tau → Mt V.rank, (∀ τ, InZe (gramAt D V τ) (fun i => tauE D τ (ξ i)) (m τ)) → ∃ z ∈ ZI V ξ, z ∈ GinfC V ∧ ∀ τ, archM V (θ τ) z = m τ) ∧ ∀ z ∈ ZI V ξ, (matHom V z).1.mulVec (fun i => incA D (ξ i)) = fun i => incA D (ξ i) := by
  first | exact @GlobalTheory.HolDict.TransvGroup.transvection_group | exact GlobalTheory.HolDict.TransvGroup.transvection_group | (intros; apply GlobalTheory.HolDict.TransvGroup.transvection_group <;> assumption)
