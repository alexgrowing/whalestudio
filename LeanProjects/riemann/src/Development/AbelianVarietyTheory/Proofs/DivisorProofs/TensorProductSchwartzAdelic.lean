import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.BoxSchwartz

theorem boxFun_mem_schA_adelic :
    ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'] (Φ₁ : (κ → AF F) → ℂ) (Φ₂ : (κ' → AF F) → ℂ),
    Φ₁ ∈ schA F κ → Φ₂ ∈ schA F κ' → boxFun Φ₁ Φ₂ ∈ schA F (κ ⊕ κ') := by
  intro F _ _ κ κ' _ _ Φ₁ Φ₂ h₁ h₂
  exact GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ' Φ₁ h₁ Φ₂ h₂

end GlobalTheory.BoxSchwartz
