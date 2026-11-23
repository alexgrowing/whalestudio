import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSchwartzAdelic
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_product_schwartz_adelic : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ'] (Φ₁ : (κ → AF F) → ℂ) (Φ₂ : (κ' → AF F) → ℂ),
    Φ₁ ∈ schA F κ → Φ₂ ∈ schA F κ' → boxFun Φ₁ Φ₂ ∈ schA F (κ ⊕ κ') := by
  first | exact @GlobalTheory.BoxSchwartz.boxFun_mem_schA_adelic | exact GlobalTheory.BoxSchwartz.boxFun_mem_schA_adelic | (intros; apply GlobalTheory.BoxSchwartz.boxFun_mem_schA_adelic <;> assumption)
