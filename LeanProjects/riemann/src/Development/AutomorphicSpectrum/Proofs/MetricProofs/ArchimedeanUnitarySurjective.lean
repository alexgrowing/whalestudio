import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

section TmSurj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in

theorem embOf_coe (s : 𝓞 E →+* ℂ) (x : 𝓞 E) : embOf s (x : E) = s x :=
  IsFractionRing.lift_algebraMap (intEmb_injective s) x

omit [IsCMField E] in

theorem embOf_restrict (φ : E →+* ℂ) : embOf (φ.comp (algebraMap (𝓞 E) E)) = φ := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
  ext x
  simpa using embOf_coe (φ.comp (algebraMap (𝓞 E) E)) x

omit [IsCMField E] in

theorem embOf_conj (s : 𝓞 E →+* ℂ) : embOf ((starRingEnd ℂ).comp s) = ComplexEmbedding.conjugate (embOf s) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
  ext x
  have h1 := embOf_coe ((starRingEnd ℂ).comp s) x
  have h2 := embOf_coe s x
  simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq]
  change embOf ((starRingEnd ℂ).comp s) (x : E) = starRingEnd ℂ (embOf s (x : E))
  rw [h1, h2]; rfl

omit [IsCMField E] in

theorem embOf_inj {s s' : 𝓞 E →+* ℂ} (h : embOf s = embOf s') : s = s' := by
  ext x
  rw [← embOf_coe s, ← embOf_coe s', h]

variable {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem plc_bijective (F : UnivFam E Ψ j j' n g Λ) : Function.Bijective (plc F) := by
  constructor
  · intro τ τ' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact F.cm.1 (embOf_inj h)
    · exfalso
      rw [← embOf_conj] at h
      have h' := embOf_inj h
      exact (F.cm.2 (F.σ τ)).1 ⟨τ, rfl⟩ ⟨τ', h'.symm⟩
  · intro w
    by_cases hs : ∃ τ, F.σ τ = w.embedding.comp (algebraMap (𝓞 E) E)
    · obtain ⟨τ, hτ⟩ := hs
      refine ⟨τ, ?_⟩
      simp only [plc, hτ, embOf_restrict, InfinitePlace.mk_embedding]
    · have := not_imp_not.2 (F.cm.2 (w.embedding.comp (algebraMap (𝓞 E) E))).2 hs
      obtain ⟨τ, hτ⟩ := not_not.1 this
      refine ⟨τ, ?_⟩
      have : embOf (F.σ τ) = ComplexEmbedding.conjugate w.embedding := by
        rw [hτ, ← RingHom.comp_assoc, embOf_restrict]; rfl
      simp only [plc, this, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

end TmSurj

theorem tm_surj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (b : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), (∀ τ, (b τ)ᴴ * C.gr τ * b τ = C.gr τ) → ∃ a : C.Arch, ∀ τ, C.tm a τ = b τ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C b hb
  classical
  have hbij := plc_bijective F
  let e : Ψ ≃ InfinitePlace E := Equiv.ofBijective (plc F) hbij
  have he : ∀ τ, e.symm (plc F τ) = τ := fun τ => e.symm_apply_apply τ
  have hw : ∀ w, plc F (e.symm w) = w := fun w => e.apply_symm_apply w
  let v := Pi.basisFun E (Fin (j + j'))
  let M : InfinitePlace E → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun w =>
    if w.embedding = embOf (F.σ (e.symm w)) then b (e.symm w) else (b (e.symm w)).map (starRingEnd ℂ)
  have hct : ∀ X : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, (X.map (starRingEnd ℂ))ᵀ = Xᴴ := fun X => by
    ext i k; simp [Matrix.conjTranspose_apply]
  have hM : ∀ w, ((M w).map (starRingEnd ℂ))ᵀ * gramAt C.h v w * M w = gramAt C.h v w := by
    intro w
    have hτ := hb (e.symm w)
    rw [hct]
    by_cases hc : w.embedding = embOf (F.σ (e.symm w))
    · have hg : gramAt C.h v w = C.gr (e.symm w) := by
        simp only [gramAt, LatEmb.gr, hc]; rfl
      simp only [M, if_pos hc, hg]
      exact hτ
    · have hconj : w.embedding = ComplexEmbedding.conjugate (embOf (F.σ (e.symm w))) := by
        have h1 : InfinitePlace.mk (embOf (F.σ (e.symm w))) = InfinitePlace.mk w.embedding := by
          rw [InfinitePlace.mk_embedding]; exact hw w
        rcases InfinitePlace.mk_eq_iff.1 h1 with h | h
        · exact absurd h.symm hc
        · exact h.symm
      have hg : gramAt C.h v w = (C.gr (e.symm w)).map (starRingEnd ℂ) := by
        ext i k
        simp only [gramAt, LatEmb.gr, Matrix.map_apply, hconj]
        rfl
      have h2 := congrArg (fun X : Matrix (Fin (j + j')) (Fin (j + j')) ℂ => X.map (starRingEnd ℂ)) hτ
      simp only [Matrix.map_mul] at h2
      have h3 : ((b (e.symm w)).map (starRingEnd ℂ))ᴴ = ((b (e.symm w))ᴴ).map (starRingEnd ℂ) := by
        ext i k; simp [Matrix.conjTranspose_apply]
      simp only [M, if_neg hc, hg]
      rw [h3]
      exact h2
  have hH : ∀ w, IsUnit (gramAt C.h v w).det := by
    intro w
    have := (isUnit_det_gram C.h v).map w.embedding
    rw [RingHom.map_det] at this
    exact this
  let a : InfinitePlace E → GL (Fin (j + j')) ℂ := fun w =>
    Matrix.nonsingInvUnit (M w) (isUnit_det_of_unitary (starRingEnd ℂ) (hH w) (hM w))
  have ha : a ∈ C.Arch := mem_archUnitary.2 fun w => hM w
  refine ⟨⟨a, ha⟩, fun τ => ?_⟩
  have haM : ∀ w, (a w : Matrix (Fin (j + j')) (Fin (j + j')) ℂ) = M w := fun w => rfl
  simp only [LatEmb.tm, tauMat, haM, M, he]
  by_cases hc : (plc F τ).embedding = embOf (F.σ τ)
  · simp only [if_pos hc]
  · simp only [if_neg hc]
    ext i k
    simp

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
