import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv

noncomputable section

open NumberField

namespace GlobalTheory.HeckePoisson

variable {K : Type} [Field K] [NumberField K] {I : Type}

def embA (φ : I → K →+* ℂ) : 𝓞 K →+ EuclideanSpace ℂ I where
  toFun α := WithLp.toLp 2 (GlobalTheory.HeckeTheta.emb φ (α : K))
  map_zero' := by ext i; simp [GlobalTheory.HeckeTheta.emb]
  map_add' a b := by ext i; simp [GlobalTheory.HeckeTheta.emb]

def lat (φ : I → K →+* ℂ) (M : Ideal (𝓞 K)) : Submodule ℤ (EuclideanSpace ℂ I) :=
  AddSubgroup.toIntSubmodule (M.toAddSubgroup.map (embA φ))

theorem embA_apply (φ : I → K →+* ℂ) (α : 𝓞 K) (i : I) : embA φ α i = φ i (α : K) := rfl

theorem mem_lat {φ : I → K →+* ℂ} {M : Ideal (𝓞 K)} {x : EuclideanSpace ℂ I} :
    x ∈ lat φ M ↔ ∃ μ ∈ M, embA φ μ = x := by
  show x ∈ M.toAddSubgroup.map (embA φ) ↔ _
  rw [AddSubgroup.mem_map]
  rfl

def kappa [Fintype I] (n : I → ℤ) : ℂ := ((2 : ℂ) ^ Fintype.card I)⁻¹ * (-Complex.I) ^ (∑ i, (n i).natAbs)

end GlobalTheory.HeckePoisson
