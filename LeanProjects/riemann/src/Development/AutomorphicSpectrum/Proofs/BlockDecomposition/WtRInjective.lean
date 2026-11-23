import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCountG

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

variable {n : ℕ}

def muZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Fin n → ℤ := fun a =>
  2 * lam a + (((univ.filter fun b => lev a < lev b).card : ℤ) - ((univ.filter fun b => lev b < lev a).card : ℤ))

theorem wtR_muZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : wtR (muZ lam lev) = muQ lam lev := by
  funext a
  simp only [wtR, muZ, muQ, rhoU]
  push_cast
  ring

theorem wtR_injective : Function.Injective (wtR : (Fin n → ℤ) → Fin n → ℝ) := fun x y h => by
  funext a
  have := congrFun h a
  simpa [wtR] using this

open Classical in

def harmZ (lam : Fin n → ℤ) : Finset (Fin n → ℤ) :=
  ((univ : Finset (Fin n → Fin n)).filter fun lev => IsLev lam fun a => (lev a : ℕ)).image
    fun lev => muZ lam fun a => (lev a : ℕ)

open Classical in
theorem harmSet_eq (lam : Fin n → ℤ) : harmSet lam = (harmZ lam).image wtR := by
  unfold harmSet harmZ
  rw [Finset.image_image]
  refine Finset.image_congr fun lev _ => ?_
  exact (wtR_muZ lam _).symm

def hwOf {M : Type*} [AddCommGroup M] [Module ℂ M] (G : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) :
    Submodule ℂ M where
  carrier := {v | Formalism.REAL.KHighest (fun _ => true) G μ v}
  add_mem' {x y} hx hy := ⟨fun a => by rw [map_add, hx.1 a, hy.1 a, smul_add],
    fun a b hab he => by rw [map_add, hx.2 a b hab he, hy.2 a b hab he, add_zero]⟩
  zero_mem' := ⟨fun a => by simp, fun a b _ _ => by simp⟩
  smul_mem' c x hx := ⟨fun a => by rw [map_smul, hx.1 a, smul_comm],
    fun a b hab he => by rw [map_smul, hx.2 a b hab he, smul_zero]⟩

def IsDualFam (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) : Prop :=
  Formalism.REAL.GlRel G ∧ ∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X →
    (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ ξ : E.V →L[ℂ] ℂ,
      HasDerivAt (fun t : ℝ => ξ ∘L E.ρ (γ t)⁻¹) (∑ a, ∑ b, X a b • G a b ξ) 0

end GlobalTheory.CompanionTheory.RealCountG
