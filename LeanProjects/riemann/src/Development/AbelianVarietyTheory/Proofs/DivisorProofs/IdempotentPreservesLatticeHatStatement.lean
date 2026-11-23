import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentPreservesLatticeHat
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_preserves_lattice_hat : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (PP : Pl D.host.E) (e : Formalism.L2.Theta.AE D), IsBaseFrame V β Λ N → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → Formalism.L2.NTheta.IsIdemAt e PP → ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, (y ∈ Formalism.L2.NTheta.LamHat V → (fun a => finPart D e * y a) ∈ Formalism.L2.NTheta.LamHat V) ∧ ((fun a => finPart D e * y a) ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ i, (β⁻¹).val.mulVec (fun a => swapAE D (finPart D e * y a)) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) := by
  first | exact @GlobalTheory.LatLoc.lamHat_loc | exact GlobalTheory.LatLoc.lamHat_loc | (intros; apply GlobalTheory.LatLoc.lamHat_loc <;> assumption)
