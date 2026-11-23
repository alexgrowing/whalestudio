import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RootCoordinateFrames

noncomputable section

open NumberField
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def embOf (φ : InfinitePlace F → (E →+* ℂ)) (p : InfinitePlace F × Bool) : E →+* ℂ :=
  if p.2 then (starRingEnd ℂ).comp (φ p.1) else φ p.1

theorem embOf_injective [IsTotallyReal F] [IsTotallyComplex E] (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) : Function.Injective (embOf φ) := by
  have hre : ∀ (v : InfinitePlace F) (a : F), starRingEnd ℂ (v.embedding a) = v.embedding a := by
    intro v a
    have h := ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal v))
    exact RingHom.congr_fun h a
  have hres : ∀ p : InfinitePlace F × Bool, (embOf φ p).comp (algebraMap F E) = p.1.embedding := by
    rintro ⟨v, b⟩
    ext a
    cases b <;> simp [embOf, hφ, hre]
  have hnr : ∀ v, (starRingEnd ℂ).comp (φ v) ≠ φ v := by
    intro v h
    have hc := IsTotallyComplex.isComplex (InfinitePlace.mk (φ v))
    rw [InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff] at hc
    exact hc (RingHom.ext fun x => RingHom.congr_fun h x)
  rintro ⟨v, b⟩ ⟨v', b'⟩ h
  have hv : v = v' := by
    have := congrArg (fun σ => σ.comp (algebraMap F E)) h
    simp only [hres] at this
    rw [← InfinitePlace.mk_embedding v, ← InfinitePlace.mk_embedding v', this]
  subst hv
  cases b <;> cases b' <;> simp [embOf] at h ⊢
  · exact hnr v h.symm
  · exact hnr v h

theorem embOf_bijective [IsTotallyReal F] [IsTotallyComplex E] (h2 : Module.finrank F E = 2)
    (φ : InfinitePlace F → (E →+* ℂ)) (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) :
    Function.Bijective (embOf φ) := by
  classical
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨embOf_injective φ hφ, ?_⟩
  rw [Fintype.card_prod, Fintype.card_bool, Embeddings.card E ℂ,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
    ← Module.finrank_mul_finrank ℚ F E, h2]
  have h := InfinitePlace.card_add_two_mul_card_eq_rank F
  rw [IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero] at h
  rw [h]

theorem trace_eq_sum_places [IsTotallyReal F] [IsTotallyComplex E] (h2 : Module.finrank F E = 2)
    (φ : InfinitePlace F → (E →+* ℂ)) (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ v, (φ v x + starRingEnd ℂ (φ v x)) := by
  classical
  have h1 : algebraMap ℚ ℂ (Algebra.trace ℚ E x) = ∑ τ : E →ₐ[ℚ] ℂ, τ x := trace_eq_sum_embeddings ℂ
  have h3 : ∑ σ : E →+* ℂ, σ x = ∑ τ : E →ₐ[ℚ] ℂ, τ x :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun τ => τ x)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])
  have h4 : ∑ p : InfinitePlace F × Bool, embOf φ p x = ∑ σ : E →+* ℂ, σ x :=
    (embOf_bijective h2 φ hφ).sum_comp (fun σ => σ x)
  rw [show ((Algebra.trace ℚ E x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E x) from rfl, h1, ← h3, ← h4,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_bool]
  simp [embOf, add_comm]

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem TraceSum_holds : Formalism.L2.SG.RealObj.RootCoordinateFrames.TraceSum := by
  intro D X g x
  have : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  have : IsTotallyComplex X.B.I.E := X.B.I.cm.cmUnram.1
  have htr : ((Algebra.trace ℚ D.host.E (X.ιE x) : ℚ) : ℂ) = ((Algebra.trace ℚ X.B.I.E x : ℚ) : ℂ) := by
    rw [show X.ιE x = X.ιE.toRatAlgEquiv x from rfl, Algebra.trace_eq_of_algEquiv]
  unfold Formalism.L2.SG.PairVal.psiInf
  rw [htr, trace_eq_sum_places X.B.I.cm.deg2 X.B.I.φ X.B.I.φ_over x, ← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum, Finset.sum_div]
  rfl

end Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums
