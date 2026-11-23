import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.CartanLines

variable {n : ℕ}

def sform (M : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n → ℂ) : ℂ := a ⬝ᵥ M *ᵥ star b

def refl (M : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) (ν : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 - ν • Matrix.vecMulVec w (M *ᵥ star w)

section Cartan

variable {M θ : Matrix (Fin n) (Fin n) ℂ}

end Cartan

section Step

variable {M θ : Matrix (Fin n) (Fin n) ℂ}

noncomputable def plusPart (θ : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : Fin n → ℂ := (1 / 2 : ℂ) • (v + θ *ᵥ v)

noncomputable def minusPart (θ : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : Fin n → ℂ := (1 / 2 : ℂ) • (v - θ *ᵥ v)

end Step

theorem det_ne_zero_of_cartan {M θ : Matrix (Fin n) (Fin n) ℂ} (hθ : IsCartan M θ) : M.det ≠ 0 := by
  intro h0
  obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hy0' : star y ≠ 0 := by simpa using hy0
  have := hθ.2.2 (star y) hy0'
  rw [star_star, hy, dotProduct_zero] at this
  simp at this

end GlobalTheory.CartanLines
