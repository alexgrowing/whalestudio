import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.GIface
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CIface

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.TNZ

def TensorProductVectors : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (d : Fin s → ℕ)
    (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) (μ : Fin s → kˣ →* ℂˣ), (∀ a, HasDetVec (σ a) (μ a)) →
    ∃ v : ⨂[ℂ] a, X a, v ≠ 0 ∧ ∀ m : Levi k (fun a => Fin (d a)), (∀ a, m a ∈ KO k (Fin (d a))) →
      piTensor σ m v = (∏ a, ((μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)) • v

def LeviSubgroupRestriction : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (p : parab k G.e), (p : GL (Fin n) k) ∈ KO k (Fin n) →
      G.lam p = ∏ a, ((G.μ a (GeneralLinearGroup.det (leviProj k G.e p a)) : ℂˣ) : ℂ)

def ParabolicInductionKernel : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ)
    (hd : ∑ a, d a = n) (p : parab k (stdBlocks d hd)), (p : GL (Fin n) k) ∈ KO k (Fin n) →
      (∀ a, leviProj k (stdBlocks d hd) p a ∈ KO k (Fin (d a))) ∧
        deltaHalf k (fun a => Fin (d a)) (leviProj k (stdBlocks d hd) p) = 1

def InducedDeterminantTwist : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ)
    (hd : ∑ a, d a = n) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W)
    (F F' : IndSp (stdBlocks d hd) ρ), (∀ κ ∈ KO k (Fin n), F.1.1 κ = F'.1.1 κ) → F = F'

def InductionExtension : Prop :=
  LeviSubgroupRestriction → ParabolicInductionKernel →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (X : Fin G.s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (X a)) (v : ⨂[ℂ] a, X a),
    (∀ m : Levi k (fun a => Fin (G.d a)), (∀ a, m a ∈ KO k (Fin (G.d a))) →
      piTensor σ m v = (∏ a, ((G.μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ)) • v) →
    ∀ φ ∈ G.V0sp, ∃ F : IndSp G.e (piTensor σ), ∀ κ : ↥(KO k (Fin n)), F.1.1 κ = φ κ • v

def GEmb : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsTwSphProd π G.d G.hd G.μ →
    ∃ f : ↥G.V0sp →ₗ[ℂ] V, Function.Injective f ∧
      ∀ (κ : ↥(KO k (Fin n))) (φ φ' : ↥G.V0sp), (φ' : ↥(KO k (Fin n)) → ℂ) = Grp.Rreg (k := k) (n := n) κ φ → f φ' = π κ (f φ)

end UpperTheory.TNZ
