import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf

namespace GlobalTheory.InfAdeleCMType

theorem exists_homeomorph : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ))
    (θ : Ψ → (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* ℂ)),
    (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ ρ : Ψ, IsInfEmb ρ.1 (θ ρ)) →
    ∃ Φ : (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) ≃ₜ (Ψ → ℂ), ∀ z ρ, Φ z ρ = θ ρ z := by
  intro E _ _ _ Ψ θ hΨ hθ
  have h : IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (fun ρ : Ψ => ρ.1) := by
    constructor
    · intro a b hab
      rcases InfinitePlace.mk_eq_iff.1 hab with e | e
      · exact Subtype.ext e
      · exact absurd (e ▸ b.2) ((hΨ a.1).1 a.2)
    · intro w
      by_cases hw : w.embedding ∈ Ψ
      · exact ⟨⟨_, hw⟩, w.mk_embedding⟩
      · have hc : ComplexEmbedding.conjugate w.embedding ∈ Ψ := by
          by_contra hn
          exact hw ((hΨ _).2 hn)
        exact ⟨⟨_, hc⟩, (InfinitePlace.mk_conjugate_eq _).trans w.mk_embedding⟩
  haveI : Module.Finite (maximalRealSubfield E) E := Module.Finite.of_restrictScalars_finite ℚ _ E
  haveI : IsModuleTopology (Ainf (maximalRealSubfield E))
    (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) :=
    IsModuleTopology.isTopologicalRing (Ainf (maximalRealSubfield E)) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele (maximalRealSubfield E)
  obtain ⟨e₀⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := maximalRealSubfield E) (E := E)
    (Ainf (maximalRealSubfield E))
  haveI : LocallyCompactSpace (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) :=
    e₀.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) :=
    e₀.secondCountableTopology
  have hb := GlobalTheory.Mem.VolExists.infEmb_bijective h hτ hθ
  let Θ : Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+ (Ψ → ℂ) := (RingHom.pi θ).toAddMonoidHom
  have hΘ : Continuous Θ := continuous_pi fun ρ => GlobalTheory.Mem.VolExists.infEmb_continuous (hθ ρ)
  have ho : IsOpenMap Θ := AddMonoidHom.isOpenMap_of_sigmaCompact Θ hb.2 hΘ
  exact ⟨(Equiv.ofBijective Θ hb).toHomeomorphOfContinuousOpen hΘ ho, fun _ _ => rfl⟩

end GlobalTheory.InfAdeleCMType
