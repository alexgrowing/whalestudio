import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryAdelicSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanCmTypeHomeomorphStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSpecialUnitaryIsoStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf

namespace GlobalTheory.TamUnf

theorem exists_SUAdelic_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
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
  intro E _ _ _ r G Ψ θ hG hdet hΨ hθ
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.archimedean_cm_type_homeomorph E Ψ θ hΨ hθ
  obtain ⟨f, hf⟩ := GlobalTheory.T.archimedean_special_unitary_iso E r G Ψ θ hθ Φ hΦ
  obtain ⟨e, he⟩ := GlobalTheory.T.special_unitary_adelic_splitting (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom r Gᵀ
  let p : SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ ≃ₜ* realSU Ψ G × finSU (IsCMField.complexConj E).toAlgHom Gᵀ :=
    { e.toMulEquiv.trans (f.toMulEquiv.prodCongr (MulEquiv.refl _)) with
      continuous_toFun := ((f.continuous.comp continuous_fst).prodMk continuous_snd).comp e.continuous
      continuous_invFun := e.symm.continuous.comp ((f.symm.continuous.comp continuous_fst).prodMk continuous_snd) }
  refine ⟨p, fun h => ⟨fun ρ => ?_, (he h).2⟩⟩
  show (((f (e h).1 : Ψ → GL (Fin r) ℂ) ρ : Matrix (Fin r) (Fin r) ℂ)) = _
  rw [hf, (he h).1]
  rfl

end GlobalTheory.TamUnf
