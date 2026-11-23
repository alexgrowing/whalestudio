import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.RealInd

namespace GlobalTheory.LeviFactor

variable {n a : ℕ} (ε : Fin n → Bool)

def glPart (W : Flag n a) : Subgroup (UJ ε) where
  carrier := {g | g ∈ leviOne ε W ∧
    ∀ y : Fin n → ℂ, (∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ y) = 0) → uMat g *ᵥ y - y ∈ W (Fin.last a)}
  one_mem' := ⟨(leviOne ε W).one_mem, fun y _ => by simp [uMat_one]⟩
  mul_mem' := fun {g h} hg hh => ⟨(leviOne ε W).mul_mem hg.1 hh.1, fun y hy => by
    convert (W _).add_mem (hg.1.1 _ _ (hh.2 y hy)).1 (hg.2 y hy) using 1
    rw [uMat_mul, ← mulVec_mulVec, mulVec_sub]
    abel⟩
  inv_mem' := fun {g} hg => ⟨(leviOne ε W).inv_mem hg.1, fun y hy => by
    convert (W _).neg_mem (((leviOne ε W).inv_mem hg.1).1 _ _ (hg.2 y hy)).1 using 1
    rw [mulVec_sub, mulVec_mulVec, uMat_inv_mul, one_mulVec, neg_sub]⟩

def uPart (L : Submodule ℂ (Fin n → ℂ)) : Subgroup (UJ ε) where
  carrier := {g | ∀ y ∈ L, uMat g *ᵥ y = y ∧ (uMat g)ᴴ *ᵥ y = y}
  one_mem' := fun y _ => by simp [uMat_one]
  mul_mem' := fun {g h} hg hh y hy => by
    rw [uMat_mul, conjTranspose_mul, ← mulVec_mulVec, ← mulVec_mulVec, (hh y hy).1, (hg y hy).2]
    exact ⟨(hg y hy).1, (hh y hy).2⟩
  inv_mem' := fun {g} hg y hy => by
    constructor
    · conv_lhs => rw [← (hg y hy).1, mulVec_mulVec, uMat_inv_mul, one_mulVec]
    · conv_lhs => rw [← (hg y hy).2, mulVec_mulVec, ← conjTranspose_mul, uMat_mul_inv, conjTranspose_one, one_mulVec]

def slPart (W : Flag n a) : Subgroup (UJ ε) where
  carrier := {g | g ∈ glPart ε W ∧ ∀ i, ∀ h : ∀ y ∈ W i, Matrix.toLin' (uMat g) y ∈ W i,
    LinearMap.det ((Matrix.toLin' (uMat g)).restrict h) = 1}
  one_mem' := ⟨(glPart ε W).one_mem, fun i h => by
    rw [show (Matrix.toLin' (uMat (1 : UJ ε))).restrict h = 1 by ext y : 2; simp [uMat_one]]
    simp⟩
  mul_mem' := fun {g h} hg hh => ⟨(glPart ε W).mul_mem hg.1 hh.1, fun i e => by
    have h1 : ∀ y ∈ W i, Matrix.toLin' (uMat g) y ∈ W i := fun y hy => (hg.1.1.1 i y hy).1
    have h2 : ∀ y ∈ W i, Matrix.toLin' (uMat h) y ∈ W i := fun y hy => (hh.1.1.1 i y hy).1
    rw [show (Matrix.toLin' (uMat (g * h))).restrict e =
      (Matrix.toLin' (uMat g)).restrict h1 * (Matrix.toLin' (uMat h)).restrict h2 by
        ext y : 2; simp [uMat_mul, Matrix.toLin'_mul], map_mul, hg.2, hh.2, one_mul]⟩
  inv_mem' := fun {g} hg => ⟨(glPart ε W).inv_mem hg.1, fun i e => by
    have h1 : ∀ y ∈ W i, Matrix.toLin' (uMat g) y ∈ W i := fun y hy => (hg.1.1.1 i y hy).1
    have : (Matrix.toLin' (uMat g)).restrict h1 * (Matrix.toLin' (uMat g⁻¹)).restrict e = 1 := by
      ext y : 2; simp [uMat_mul_inv]
    have h3 := congrArg LinearMap.det this
    rwa [map_mul, hg.2, one_mul, map_one] at h3⟩

variable {ε}

theorem glPart_le (W : Flag n a) : glPart ε W ≤ leviOne ε W := fun _ h => h.1

theorem uPart_bot : uPart ε (⊥ : Submodule ℂ (Fin n → ℂ)) = ⊤ :=
  eq_top_iff.2 fun g _ y hy => by rw [(Submodule.mem_bot ℂ).1 hy]; simp

end GlobalTheory.LeviFactor

end
