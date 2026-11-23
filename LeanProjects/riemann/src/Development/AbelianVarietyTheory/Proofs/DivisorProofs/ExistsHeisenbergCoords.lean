import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvApply
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open GlobalTheory.PoleFactor

noncomputable section

namespace GlobalTheory.HeisCoords

open Matrix

section Cplx

variable {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ)

def hf (a b : Fin n → ℂ) : ℂ := star a ⬝ᵥ J *ᵥ b

theorem hf_add_right (a b c : Fin n → ℂ) : hf J a (b + c) = hf J a b + hf J a c := by
  simp [hf, mulVec_add]
theorem hf_smul_right (a b : Fin n → ℂ) (s : ℂ) : hf J a (s • b) = s * hf J a b := by
  simp [hf, mulVec_smul]

def hfL (a : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℝ] ℂ where
  toFun := hf J a
  map_add' := hf_add_right J a
  map_smul' s b := by
    rw [RingHom.id_apply, ← Complex.coe_smul, hf_smul_right, Complex.real_smul]

@[simp] theorem hfL_apply (a b : Fin n → ℂ) : hfL J a b = hf J a b := rfl

def Heisenberg₂ (x w : Fin n → ℂ) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + vecMulVec w (star x ᵥ* J) - vecMulVec x (star w ᵥ* J) + z • vecMulVec x (star x ᵥ* J)

variable {J}

end Cplx

section Coords

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ}

end Coords

section Transfer

open Formalism.UG (cT bc UJ)
open GlobalTheory.Orb (archMat)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {ν : InfinitePlace F}

theorem archMat_unitary (hcm : IsCMExt F E σ) (τ : EmbOver E ν) (g : HA ν.Completion σ J) :
    (archMat σ J τ g)ᴴ * J.map τ.1 * archMat σ J τ g = J.map τ.1 := (archEquiv J hcm τ g).2

end Transfer

open Formalism.UG (cT bc UJ)
open GlobalTheory.Orb (archMat)

end GlobalTheory.HeisCoords

end
