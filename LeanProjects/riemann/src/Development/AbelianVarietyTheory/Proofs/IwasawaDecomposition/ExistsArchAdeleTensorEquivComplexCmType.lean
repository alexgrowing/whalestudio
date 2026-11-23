import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfEmb
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.VolInfIso

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem bijective_fam (σ : E →ₐ[F] E) {I : Type} (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ))
    (h : IsCMExt F E σ) (hτ : IsCMFam τ) (hθ : ∀ i, IsInfEmb (τ i) (θ i)) :
    Function.Bijective (fun (z : Ainf F ⊗[F] E) (i : I) => θ i z) := by
  obtain ⟨hF, hE, h2, hσ⟩ := h
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := hσ
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc : c ≠ 1 := by
    intro h1
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc', h1]
    rfl
  choose θ0 h0 h0' using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hΨ : ∀ φ : E →+* ℂ, φ ∈ Set.range τ ↔ ComplexEmbedding.conjugate φ ∉ Set.range τ := by
    intro φ
    constructor
    · rintro ⟨i, rfl⟩ ⟨j, hj⟩
      have : j = i := hτ.1 (by
        show InfinitePlace.mk (τ j) = InfinitePlace.mk (τ i)
        rw [hj, InfinitePlace.mk_conjugate_eq])
      subst this
      exact hnr _ hj.symm
    · intro hn
      obtain ⟨i, hi⟩ := hτ.2 (InfinitePlace.mk φ)
      rcases InfinitePlace.mk_eq_iff.1 hi with e | e
      · exact ⟨i, e⟩
      · refine absurd ⟨i, ?_⟩ hn
        rw [← e]
        ext x
        simp
  have hb := GlobalTheory.InfAdeleCM.bijective c h2 hc hc' θ0
    (fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ0 φ) (h0 φ) (h0' φ)) (Set.range τ) hΨ
  have hinj : Function.Injective τ := fun i j hij => hτ.1 (by
    show InfinitePlace.mk (τ i) = InfinitePlace.mk (τ j)
    rw [hij])
  let u : I ≃ Set.range τ := Equiv.ofInjective τ hinj
  have he : (fun (z : Ainf F ⊗[F] E) (i : I) => θ i z) =
      (Equiv.arrowCongr u.symm (Equiv.refl ℂ)) ∘ (fun (z : Ainf F ⊗[F] E) (φ : Set.range τ) => θ0 φ.1 z) := by
    funext z i
    rw [GlobalTheory.Mem.VolEmb.infEmb_unique (τ i) (θ i) (θ0 (τ i)) (hθ i) ⟨h0 _, h0' _⟩]
    rfl
  rw [he]
  exact (Equiv.bijective _).comp hb

theorem infEmb_sigR (σ : E →ₐ[F] E) (τ : E →+* ℂ) (θ : Ainf F ⊗[F] E →+* ℂ)
    (h : IsCMExt F E σ) (hθ : IsInfEmb τ θ) (z : Ainf F ⊗[F] E) :
    θ (sigR (Ainf F) σ z) = star (θ z) := by
  obtain ⟨hF, -, -, hσ⟩ := h
  have hθ' := GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    show θ (a ⊗ₜ[F] σ x) = starRingEnd ℂ _
    rw [hθ', hθ', map_mul, GlobalTheory.InfAdeleCM.conj_ext, hσ]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, star_add]

theorem exists_infAdele_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → ∃ e : (Ainf F ⊗[F] E) ≃+* (I → ℂ), (∀ x i, e x i = θ i x) ∧ Continuous e ∧ Continuous e.symm ∧ ∀ x i, e (sigR (Ainf F) σ x) i = star (e x i) := by
  intro F E _ _ _ _ _ σ I _ τ θ h hτ hθ
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; omega)
  haveI : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Ainf F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Ainf F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_infiniteAdele F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Ainf F)
  haveI : LocallyCompactSpace (Ainf F ⊗[F] E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Ainf F ⊗[F] E) := e0.secondCountableTopology
  have hb : Function.Bijective (Pi.ringHom θ : Ainf F ⊗[F] E →+* (I → ℂ)) := bijective_fam σ τ θ h hτ hθ
  let e : (Ainf F ⊗[F] E) ≃+* (I → ℂ) := RingEquiv.ofBijective _ hb
  have hc : Continuous e := continuous_pi fun i =>
    IsModuleTopology.continuous_of_ringHom (R := Ainf F) (θ i) (hθ i).2
  have ho : IsOpenMap e :=
    AddMonoidHom.isOpenMap_of_sigmaCompact e.toAddEquiv.toAddMonoidHom e.surjective hc
  refine ⟨e, fun _ _ => rfl, hc, ?_, fun x i => infEmb_sigR σ (τ i) (θ i) h (hθ i) x⟩
  exact (e.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous

end GlobalTheory.Mem.VolInfIso
