import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryAdelicRealization
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_unitary_adelic_realization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Ψ : Finset (E →+* ℂ)) (θ : Ψ → (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* ℂ)),
    (∀ a b, IsCMField.complexConj E (G a b) = G b a) → G.det ≠ 0 →
    (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ ρ : Ψ, IsInfEmb ρ.1 (θ ρ)) →
    ∃ e : SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ ≃ₜ* realSU Ψ G × finSU (IsCMField.complexConj E).toAlgHom Gᵀ,
      ∀ h, (∀ ρ, (((e h).1 : Ψ → GL (Fin r) ℂ) ρ : Matrix (Fin r) (Fin r) ℂ) =
          infMat (IsCMField.complexConj E).toAlgHom Gᵀ (θ ρ) h.1) ∧
        ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ (e h).2.1 :
          GL (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
          Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) =
          finMat (IsCMField.complexConj E).toAlgHom Gᵀ h.1 := by
  first | exact @GlobalTheory.TamUnf.exists_SUAdelic_split | exact GlobalTheory.TamUnf.exists_SUAdelic_split | (intros; apply GlobalTheory.TamUnf.exists_SUAdelic_split <;> assumption)
