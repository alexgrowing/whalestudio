import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.BoxLattice

variable (F : Type) [Field F] [NumberField F] (κ : Type)

def ratInf (ξ : κ → F) : κ → mixedEmbedding.mixedSpace F := fun i => mixedEmbedding F (ξ i)

def ratFin (ξ : κ → F) : κ → FiniteAdeleRing (𝓞 F) F := fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)

def boxLat (a : F) : Submodule ℤ (κ → mixedEmbedding.mixedSpace F) where
  carrier := {l | ∃ b : κ → 𝓞 F, l = ratInf F κ fun i => a * (b i : F)}
  add_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
    refine ⟨b + b', funext fun i => ?_⟩
    simp [ratInf, mul_add]
  zero_mem' := ⟨0, funext fun i => by simp [ratInf]⟩
  smul_mem' := by
    rintro c _ ⟨b, rfl⟩
    refine ⟨c • b, funext fun i => ?_⟩
    simp only [ratInf, Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast]
    push_cast
    ring

variable {F κ}

theorem psi_fin_rat {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) [Fintype κ] (ρ z : κ → F) :
    ψ (pairA F 0 (ratFin F κ ρ ⬝ᵥ ratFin F κ z)) =
      Complex.exp (2 * Real.pi * Complex.I * (GlobalTheory.VacLn.trPair F κ (ratInf F κ ρ) (ratInf F κ z) : ℂ)) := by
  have e1 : ratFin F κ ρ ⬝ᵥ ratFin F κ z = algebraMap F (FiniteAdeleRing (𝓞 F) F) (ρ ⬝ᵥ z) := by
    simp [ratFin, dotProduct, map_sum, map_mul]
  have e2 : GlobalTheory.VacLn.trPair F κ (ratInf F κ ρ) (ratInf F κ z) = ((Algebra.trace ℚ F (ρ ⬝ᵥ z) : ℚ) : ℝ) := by
    rw [GlobalTheory.VacLn.trPair_apply, ← GlobalTheory.PsiNontriv.trace_mixedEmbedding]
    simp [ratInf, dotProduct, map_sum, map_mul]
  rw [e1, e2]
  exact GlobalTheory.PsiNontriv.isStd_fin_rat hψ _

end GlobalTheory.BoxLattice
