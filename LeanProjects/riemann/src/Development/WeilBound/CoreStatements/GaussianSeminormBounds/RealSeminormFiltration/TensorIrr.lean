import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.FockAct1FockAct2Commute
import Formalism.LocalToGlobal.ThetaOperatorCommutation.RealTh
import ReciprocityTheory.ThetaSummability.RealCoinvariants.Numbers
import Mathlib.LinearAlgebra.PiTensorProduct

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action

namespace PositivityTheory.KReal

abbrev ThV (D : RealData) : Type := ThC D.P D.Q D.R D.S ((D.κ : ℂ) / 2)

abbrev ThV' (D : RealData) : Type := ThC D.P' D.Q' D.R D.S (-((D.κ : ℂ) / 2))

def opV (D : RealData) (W : Mat D.R D.S) : Module.End ℂ (ThV D) :=
  ReciprocityTheory.ThetaSummability.Real.coinvOp (chiTr ((D.κ : ℂ) / 2)) (fockAct2 _ _ _ _ W) fun Z => (fockAct1_fockAct2_commute Z W).symm

def opV' (D : RealData) (W : Mat D.R D.S) : Module.End ℂ (ThV' D) :=
  ReciprocityTheory.ThetaSummability.Real.coinvOp (chiTr (-((D.κ : ℂ) / 2))) (fockAct2 _ _ _ _ W) (fun Z => (fockAct1_fockAct2_commute Z W).symm) +
    ((D.κ : ℂ) / 2 * W.trace) • 1

def CoreLM : Prop :=
  ∀ D : RealData, D.Hyp → ∃ (Pi : Type) (_ : AddCommGroup Pi) (_ : Module ℂ Pi) (act : Mat D.R D.S → Module.End ℂ Pi)
    (π : ThV D →ₗ[ℂ] Pi) (π' : ThV' D →ₗ[ℂ] Pi), Function.Surjective π ∧ Function.Surjective π' ∧
    (∀ W x, π (opV D W x) = act W (π x)) ∧ (∀ W x, π' (opV' D W x) = act W (π' x)) ∧ Nontrivial Pi ∧
    ∀ N : Submodule ℂ Pi, (∀ W, ∀ x ∈ N, act W x ∈ N) → N = ⊥ ∨ N = ⊤

def TensorIrr : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : ι → Type) (M : ι → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (act : ∀ i, A i → Module.End ℂ (M i)),
    (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∀ i, Nontrivial (M i)) →
    (∀ i, ∀ N : Submodule ℂ (M i), (∀ a, ∀ x ∈ N, act i a x ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∀ N : Submodule ℂ (PiTensorProduct ℂ M),
      (∀ i a, ∀ x ∈ N, PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i (act i a)) x ∈ N) →
      N = ⊥ ∨ N = ⊤

end PositivityTheory.KReal

end
