import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PlaceEmbeddingsBijectiveInfinitePlaces
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

open NumberField GlobalTheory.UnitaryBC GlobalTheory.CuspRep Formalism.BasicNotions
open UpperTheory.V.Z.J.D

private theorem dual_dual' {n : ℕ} (lam : DomWeight n) : lam.dual.dual = lam := by
  have h : ∀ a b : DomWeight n, (∀ i, a.w i = b.w i) → a = b := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    have : a = b := funext h
    subst this
    rfl
  exact h _ _ fun i => by simp [DomWeight.dual]

private theorem conj_wt {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {σ : Submodule ℂ (UA E n → ℂ)}
    (hσ : IsAutRepU σ) {τ : E →+* ℂ} {μ : DomWeight n} (h : HasWeightAt σ τ μ) :
    HasWeightAt σ (ComplexEmbedding.conjugate τ) μ.dual :=
  (GlobalTheory.DefU.AU.hasWt_mk (⟨σ, hσ⟩ : GlobalTheory.DefU.AutSub E n) _ _).1
    ((GlobalTheory.DefU.AU.hasWt_mk (⟨σ, hσ⟩ : GlobalTheory.DefU.AutSub E n) _ _).2 h).conjugate

private theorem link_abs {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {I : Type} (φ : I → E →+* ℂ)
    (hb : Function.Bijective fun i => InfinitePlace.mk (φ i)) (μ : I → DomWeight n) :
    ∃ lam' : InfinitePlace E → DomWeight n, ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
      ((∀ i, HasWeightAt σ (φ i) (μ i)) ↔ ∀ v : InfinitePlace E, HasWeightAt σ v.embedding (lam' v)) := by
  classical
  choose y hy using hb.2
  have hconj : ∀ v, v.embedding ≠ φ (y v) → ComplexEmbedding.conjugate (φ (y v)) = v.embedding := fun v c => by
    have e : InfinitePlace.mk (φ (y v)) = InfinitePlace.mk v.embedding := (hy v).trans (InfinitePlace.mk_embedding v).symm
    exact (InfinitePlace.mk_eq_iff.1 e).resolve_left fun e' => c e'.symm
  refine ⟨fun v => if v.embedding = φ (y v) then μ (y v) else (μ (y v)).dual, fun σ hσ => ⟨fun h v => ?_, fun h i => ?_⟩⟩
  · by_cases c : v.embedding = φ (y v)
    · simp only [if_pos c]
      rw [c]
      exact h _
    · simp only [if_neg c]
      rw [← hconj v c]
      exact conj_wt hσ (h _)
  · have hi : y (InfinitePlace.mk (φ i)) = i := hb.1 (hy _)
    have key : ∀ v, HasWeightAt σ v.embedding (if v.embedding = φ (y v) then μ (y v) else (μ (y v)).dual) →
        HasWeightAt σ (φ (y v)) (μ (y v)) := fun v hv => by
      by_cases c : v.embedding = φ (y v)
      · simp only [if_pos c] at hv
        rwa [c] at hv
      · simp only [if_neg c] at hv
        have h2 := conj_wt hσ hv
        rw [← hconj v c, dual_dual'] at h2
        exact (star_star (φ (y v))) ▸ h2
    have h3 := key _ (h (InfinitePlace.mk (φ i)))
    rwa [hi] at h3

theorem UpperTheory.V.Z.J.D.wtEx :
    WtEx := by
  intro l _ L Ω _ _ _ _ _ _ s n _ V _ ι lam
  exact link_abs (fun y : UpperTheory.V.Hi.Emb l (fun v : V.frame.Vl => s.w v.1) => ι.toRingHom.comp y.res)
    (UpperTheory.placeEmbeddings_bijective_infinitePlaces l L Ω s V ι).2 fun y => (lam y.res).dual
