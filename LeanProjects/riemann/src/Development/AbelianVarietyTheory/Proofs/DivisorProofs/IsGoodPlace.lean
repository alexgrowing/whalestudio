import Mathlib
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

namespace GlobalTheory.PoleGK

open IsDedekindDomain
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsGoodPlace (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (x y : Matrix (Fin n) (Fin 1) E) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ (m : ℕ) (B : Matrix (Fin n) (Fin m) E) (B' : Matrix (Fin m) (Fin n) E) (θ : E), m + 2 = n ∧ B' * B = 1 ∧
    cT (σ : E →+* E) x * J * B = 0 ∧ cT (σ : E →+* E) y * J * B = 0 ∧ B' * x = 0 ∧ B' * y = 0 ∧
    B * B' + x * (cT (σ : E →+* E) y * J) + y * (cT (σ : E →+* E) x * J) = 1 ∧
    θ ≠ 0 ∧ σ θ = -θ ∧ inclR (F := F) (Fv F v) θ ∈ intLoc F E v ∧ inclR (F := F) (Fv F v) θ⁻¹ ∈ intLoc F E v ∧
    (2 : 𝓞 F) ∉ v.asIdeal ∧
    ∀ z : Fin n → Fv F v ⊗[F] E, z ∈ latLoc F L v ↔
      (((cT (σ : E →+* E) y * J).map (inclR (F := F) (Fv F v)) *ᵥ z) 0 ∈ intLoc F E v ∧
        (∀ i, (B'.map (inclR (F := F) (Fv F v)) *ᵥ z) i ∈ intLoc F E v) ∧
        ((cT (σ : E →+* E) x * J).map (inclR (F := F) (Fv F v)) *ᵥ z) 0 ∈ intLoc F E v)

end GlobalTheory.PoleGK

end
