import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin

noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.Orb (archMat)

namespace GlobalTheory.ULie

def IsLieHom {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) : Prop :=
  ∀ M N, ρ (M * N - N * M) = ρ M * ρ N - ρ N * ρ M

def unitAt {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (c : GL (Fin n) ℂ)
    (p q : Fin n) : A := ρ (c.1 * Matrix.single p q 1 * (c⁻¹).1)

def Before {r : ℕ} (S : Finset (Fin r)) (n : ℕ) (p q : Fin n) : Prop :=
  ∃ k ∈ S, (p.val ≤ k.val ∧ k.val < q.val) ∨ (p.val + k.val + 1 < n ∧ n ≤ q.val + k.val + 1)

theorem Before.trans {r : ℕ} {S : Finset (Fin r)} {n : ℕ} {p q s : Fin n} (h : Before S n p q) (h' : Before S n q s) :
    Before S n p s := by
  obtain ⟨k, hk, h⟩ := h
  obtain ⟨k', -, h'⟩ := h'
  exact ⟨k, hk, by omega⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def SmU : Submodule ℂ (GAd σ J → ℂ) where
  carrier := {f | IsSm σ J f}
  add_mem' := isSm_add
  zero_mem' := fun _ _ _ _ => contDiff_const
  smul_mem' := fun c _ h => isSm_smul c h

def IsLineOf {w : InfinitePlace F} (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → GAd σ J) : Prop :=
  ∀ t : ℝ, ∃ y : GArch σ J w, γ t = embArch σ J w y ∧ archMat σ J τ y = NormedSpace.exp (t • Z)

structure IsRho {w : InfinitePlace F} (τ : EmbOver E w) (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmU σ J)) :
    Prop where
  lie : IsLieHom ρ
  line : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → GAd σ J), Zᴴ * J.map τ.1 + J.map τ.1 * Z = 0 → IsLineOf σ J τ Z γ →
    ∀ f : SmU σ J, (ρ Z f).1 = lineDer γ f.1

variable {σ} in

def rtU (h : IsCMExt F E σ) (a : GAd σ J) : Module.End ℂ (SmU σ J) where
  toFun f := ⟨fun x => f.1 (x * a), GlobalTheory.EisCont.CentreFinite.isSm_mul_right h f.2 a⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {σ J} {w : InfinitePlace F}

@[simp] theorem rtU_apply (h : IsCMExt F E σ) (a x : GAd σ J) (f : SmU σ J) : (rtU J h a f).1 x = f.1 (x * a) := rfl

end GlobalTheory.ULie

end
