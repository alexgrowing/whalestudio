import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.JacTensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def oneBlock (N : ℕ) : (Σ _ : Fin 1, Fin N) ≃ Fin N where
  toFun p := p.2
  invFun i := ⟨0, i⟩
  left_inv p := by
    obtain ⟨a, i⟩ := p
    rw [Subsingleton.elim a 0]
  right_inv _ := rfl

theorem isIrreducible_multiProd_fin_one {N : ℕ} {c : Fin 1 → ℕ} (g : (Σ i, Fin (c i)) ≃ Fin N)
    (s : ∀ i, IrrRep (GL (Fin (c i)) k)) : (multiProd g fun i => (s i).ρ).IsIrreducible := by
  obtain ⟨M, rfl⟩ : ∃ M, c = fun _ => M := ⟨c 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨s₀, rfl⟩ : ∃ s₀, s = fun _ => s₀ := ⟨s 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain rfl : M = N := by simpa using Fintype.card_congr g
  obtain ⟨φ₁⟩ := (Placing.parInd_jac_placing k (Fin 1) (Fin M) (fun _ => Fin M) g (oneBlock M) _).1
    (piTensor fun _ : Fin 1 => s₀.ρ)
  obtain ⟨φ₂⟩ := LocGL.nonempty_equiv_multiProd_one s₀.smooth (oneBlock M) fun _ _ => rfl
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv (φ₂.trans φ₁.symm) s₀.irr

end GlobalTheory.JacTensor

open GlobalTheory.JacTensor in

theorem GlobalTheory.JacTensor.exists_irr_tensor_of_isSubquotient_jac : GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible → IsSubquotient τ (jac e π.π) → ∃ σ : ∀ a, Irr k (d a), IsSubquotient τ (piTensor fun a => (σ a).π) := by
  intro hGL k _ _ _ _ n π s d e Y _ _ τ hτ hs
  obtain ⟨φ⟩ := LocGL.nonempty_equiv_multiProd_one π.smooth (oneBlock n) fun _ _ => rfl
  have h1 : IsSubquotient τ (jac e (multiProd (oneBlock n) fun _ : Fin 1 => π.π)) :=
    hs.trans (GlobalTheory.JacquetExact.isSubquotient_jac e (isSmooth_parInd _ _)
      (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective))
  obtain ⟨b, f, g, t, -, ht⟩ := exists_cell_of_isSubquotient (hGL k).1 (hGL k).2
    (m' := fun a => Fin (d a)) (oneBlock n) e (fun _ => π.smooth)
    (fun _ => hasFiniteLength_of_isIrreducible π.irr) hτ h1
  exact ⟨fun a => ⟨_, multiProd (g a) fun i => (t i a).ρ, isSmooth_parInd _ _,
    isIrreducible_multiProd_fin_one (g a) fun i => t i a⟩, ht⟩
