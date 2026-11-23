import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TwoSplitIdem
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem dRhoStable (D : D7) : DRhoStable D := by
  intro ψ θ hψ hθ S T τ z f hf
  exact (Formalism.IndefR.Fock.DRho.thetaDRho D ψ θ hψ hθ (Formalism.IndefR.Eqv.lineAtExists_holds D) S T τ z f hf).1

section Pt

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

lemma theta_sub {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (f - g) := by
  have := Formalism.IndefR.Fock.CCR.theta_add_smul hf hg (-1)
  simpa [sub_eq_add_neg] using this

lemma theta_finsetSum {ι : Type*} (s : Finset ι) (g : ι → WO S T → ℂ) (hg : ∀ i ∈ s, IsThetaFunO ψ S T (g i)) :
    IsThetaFunO ψ S T (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Formalism.IndefR.Fock.CCR.theta_zero ψ S T
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact Formalism.IndefR.Fock.CCR.theta_add (hg a (Finset.mem_insert_self a s))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

lemma theta_opPow {ι : Type} (A : ι → (WO S T → ℂ) → (WO S T → ℂ))
    (hA : ∀ i g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (A i g)) (k : ι →₀ ℕ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (opPow A k f) := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => exact hf
  | cons i l ih => exact hA i _ ih

theorem ptStable (D : D7) : PtStable D := by
  intro ψ θ hψ hθ S T sS sT BS BT f P hf
  have hA : ∀ (i : FVar D T.rank S.rank) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g) := by
    intro i g hg
    unfold aPlusAll aPlus crea
    exact Formalism.IndefR.Fock.CCR.theta_smul
      (theta_sub (dRhoStable D ψ θ hψ hθ S T i.1 _ g hg)
        (Formalism.IndefR.Fock.CCR.theta_smul (dRhoStable D ψ θ hψ hθ S T i.1 _ g hg) _)) _
  unfold pureTensorO pureTensorL
  rw [Module.Basis.constr_apply, Finsupp.sum]
  exact theta_finsetSum _ _ fun k _ =>
    Formalism.IndefR.Fock.CCR.theta_smul (theta_opPow _ hA k hf) _

end Pt

end Formalism.IndefR.Fin
