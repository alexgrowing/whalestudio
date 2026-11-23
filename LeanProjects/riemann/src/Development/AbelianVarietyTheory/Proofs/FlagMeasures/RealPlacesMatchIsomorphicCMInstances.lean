import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso.Places

noncomputable def placeEquiv (I : AutInst) : InfinitePlace I.F ≃ InfinitePlace I.E :=
  (Equiv.ofBijective _ (GlobalTheory.Count.FrameMajorant.comap_bijective I)).symm

theorem placeEquiv_apply (I : AutInst) (v : InfinitePlace I.F) :
    placeEquiv I v = InfinitePlace.mk (I.φ v) := by
  have h : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
  rw [placeEquiv, Equiv.symm_apply_eq]
  show v = (InfinitePlace.mk (I.φ v)).comap (algebraMap I.F I.E)
  rw [InfinitePlace.comap_mk, h, InfinitePlace.mk_embedding]

noncomputable def comapEquiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) :
    InfinitePlace L ≃ InfinitePlace K where
  toFun w := w.comap (e : K →+* L)
  invFun w := w.comap (e.symm : L →+* K)
  left_inv w := by
    beta_reduce; rw [← InfinitePlace.comap_comp]; simp [InfinitePlace.comap_id]
  right_inv w := by
    beta_reduce; rw [← InfinitePlace.comap_comp]; simp [InfinitePlace.comap_id]

theorem exists_twist {K : Type} [Field K] (φ ψ : K →+* ℂ)
    (h : InfinitePlace.mk φ = InfinitePlace.mk ψ) :
    ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧ ∀ y, φ y = τ (ψ y) := by
  rcases InfinitePlace.mk_eq_iff.mp h with h' | h'
  · exact ⟨RingHom.id ℂ, Or.inl rfl, fun y => by rw [h', RingHom.id_apply]⟩
  · refine ⟨starRingEnd ℂ, Or.inr rfl, fun y => ?_⟩
    rw [← h', ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

theorem places_match : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E), (∀ y, e (star y) = star (e y)) → ∃ (β : InfinitePlace I.F ≃ InfinitePlace I.E) (σ : InfinitePlace I.F ≃ InfinitePlace I₀.F) (τ τ₀ : InfinitePlace I.F → (ℂ →+* ℂ)), (∀ v, τ v = RingHom.id ℂ ∨ τ v = starRingEnd ℂ) ∧ (∀ v, τ₀ v = RingHom.id ℂ ∨ τ₀ v = starRingEnd ℂ) ∧ (∀ v y, I.φ v y = τ v ((β v).embedding y)) ∧ ∀ v y, I.φ v (e y) = τ₀ v (I₀.φ (σ v) y) := by
  intro I I₀ e _

  let σ : InfinitePlace I.F ≃ InfinitePlace I₀.F :=
    (placeEquiv I).trans ((comapEquiv e).trans (placeEquiv I₀).symm)
  have h1 : ∀ v : InfinitePlace I.F, ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧
      ∀ y, I.φ v y = τ ((placeEquiv I v).embedding y) := fun v =>
    exists_twist _ _ (by rw [InfinitePlace.mk_embedding, placeEquiv_apply])
  have h2 : ∀ v : InfinitePlace I.F, ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧
      ∀ y, I.φ v (e y) = τ (I₀.φ (σ v) y) := by
    intro v
    refine exists_twist ((I.φ v).comp (e : I₀.E →+* I.E)) (I₀.φ (σ v)) ?_
    rw [← placeEquiv_apply]
    simp only [σ, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [placeEquiv_apply]
    show _ = (InfinitePlace.mk (I.φ v)).comap (e : I₀.E →+* I.E)
    rw [InfinitePlace.comap_mk]
  choose τ hτ using h1
  choose τ₀ hτ₀ using h2
  exact ⟨placeEquiv I, σ, τ, τ₀, fun v => (hτ v).1, fun v => (hτ₀ v).1, fun v => (hτ v).2,
    fun v => (hτ₀ v).2⟩

end GlobalTheory.LeviIso.Places
