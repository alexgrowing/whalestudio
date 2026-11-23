import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSpecialUnitaryIso
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_special_unitary_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Ψ : Finset (E →+* ℂ)) (θ : Ψ → (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* ℂ)),
    (∀ ρ : Ψ, IsInfEmb ρ.1 (θ ρ)) →
    ∀ Φ : (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) ≃ₜ (Ψ → ℂ), (∀ z ρ, Φ z ρ = θ ρ z) →
    ∃ f : ((Matrix.GeneralLinearGroup.det.comp
        (HR (Ainf (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ).subtype).ker :
          Subgroup (HA (Ainf (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ)) ≃ₜ* realSU Ψ G,
      ∀ g ρ, ((f g : Ψ → GL (Fin r) ℂ) ρ : Matrix (Fin r) (Fin r) ℂ) =
        ((HA.mat (Ainf (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ g.1 :
          GL (Fin r) (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
            Matrix (Fin r) (Fin r) (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)).map (θ ρ) := by
  first | exact @GlobalTheory.InfUnitarySU.infSU_equiv_realSU | exact GlobalTheory.InfUnitarySU.infSU_equiv_realSU | (intros; apply GlobalTheory.InfUnitarySU.infSU_equiv_realSU <;> assumption)
