import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanCmTypeHomeomorph
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_cm_type_homeomorph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ))
    (θ : Ψ → (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* ℂ)),
    (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ ρ : Ψ, IsInfEmb ρ.1 (θ ρ)) →
    ∃ Φ : (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) ≃ₜ (Ψ → ℂ), ∀ z ρ, Φ z ρ = θ ρ z := by
  first | exact @GlobalTheory.InfAdeleCMType.exists_homeomorph | exact GlobalTheory.InfAdeleCMType.exists_homeomorph | (intros; apply GlobalTheory.InfAdeleCMType.exists_homeomorph <;> assumption)
