import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKStableOnOfLieStableFiniteDim
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.RealPar

theorem flow_pair_mem_range {E H₁ H₂ : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (j₁ : E →ₗ[ℂ] H₁) (j₂ : E →ₗ[ℂ] H₂) (a : E →ₗ[ℂ] E)
    (U₁ : ℝ → H₁ →L[ℂ] H₁) (U₂ : ℝ → H₂ →L[ℂ] H₂) (h₁ : U₁ 0 = 1) (h₂ : U₂ 0 = 1)
    (a₁ : ∀ s t, U₁ (s + t) = U₁ s * U₁ t) (a₂ : ∀ s t, U₂ (s + t) = U₂ s * U₂ t)
    (d₁ : ∀ v, HasDerivAt (fun t : ℝ => U₁ t (j₁ v)) (j₁ (a v)) 0)
    (d₂ : ∀ v, HasDerivAt (fun t : ℝ => U₂ t (j₂ v)) (j₂ (a v)) 0) (t : ℝ) (w : E) :
    ∃ w' : E, U₁ t (j₁ w) = j₁ w' ∧ U₂ t (j₂ w) = j₂ w' := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂
  let ι : E →ₗ[ℂ] WithLp 2 (H₁ × H₂) := e.symm.toLinearEquiv.toLinearMap ∘ₗ j₁.prod j₂
  let U : ℝ → WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂) := fun s =>
    (e.symm : H₁ × H₂ →L[ℂ] WithLp 2 (H₁ × H₂)) ∘L ((U₁ s).prodMap (U₂ s)) ∘L
      (e : WithLp 2 (H₁ × H₂) →L[ℂ] H₁ × H₂)
  have hU : ∀ s x, U s x = e.symm (U₁ s (e x).1, U₂ s (e x).2) := fun s x => rfl
  have hι : ∀ v, ι v = e.symm (j₁ v, j₂ v) := fun v => rfl
  have key := flow_mem_map ι a ⊤ (fun _ _ => trivial) U
    (by
      refine ContinuousLinearMap.ext fun x => ?_
      rw [hU, h₁, h₂]
      exact e.symm_apply_apply x)
    (fun s r => by
      refine ContinuousLinearMap.ext fun x => ?_
      rw [ContinuousLinearMap.mul_apply, hU, hU, hU, a₁, a₂, e.apply_symm_apply]
      rfl)
    (fun v => by
      have h := ((e.symm : H₁ × H₂ →L[ℂ] WithLp 2 (H₁ × H₂)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
        (0 : ℝ) ((d₁ v).prodMk (d₂ v))
      exact h) t (ι w) ⟨w, trivial, rfl⟩
  obtain ⟨w', -, hw'⟩ := key
  rw [hU, hι, hι, e.apply_symm_apply] at hw'
  have h := e.symm.injective hw'
  exact ⟨w', (congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩

theorem pair_kEquivariant_of_lie : ∀ (p q : ℕ) (T : GrpData p q), (∀ k ∈ T.Kset, k ∈ Subgroup.closure (T.expt '' {Y | Y ∈ upq p q ∧ IsKC Y})) → ∀ (π₁ π₂ : URep T) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (a : Mat p q → E →ₗ[ℂ] E) (j₁ : E →ₗ[ℂ] π₁.H) (j₂ : E →ₗ[ℂ] π₂.H), (∀ Y ∈ upq p q, IsKC Y → ∀ w, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ w)) (j₁ (a Y w)) 0 ∧ HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ w)) (j₂ (a Y w)) 0) → (∀ k ∈ T.Kset, ∀ w : E, ∃ w' : E, π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') := by
  intro p q T hgen π₁ π₂ E _ _ _ a j₁ j₂ hder k hk
  have hflow : ∀ Y ∈ upq p q, IsKC Y → ∀ (t : ℝ) (w : E), ∃ w' : E,
      π₁.π (T.expt (t • Y)) (j₁ w) = j₁ w' ∧ π₂.π (T.expt (t • Y)) (j₂ w) = j₂ w' := by
    intro Y hY hK t w
    exact flow_pair_mem_range j₁ j₂ (a Y) (fun t => π₁.π (T.expt (t • Y))) (fun t => π₂.π (T.expt (t • Y)))
      (by simp [T.expt_zero]) (by simp [T.expt_zero])
      (fun s t => by simp only [T.expt_add Y hY, map_mul])
      (fun s t => by simp only [T.expt_add Y hY, map_mul])
      (fun v => (hder Y hY hK v).1) (fun v => (hder Y hY hK v).2) t w
  refine Subgroup.closure_induction'' (p := fun k _ => ∀ w : E, ∃ w' : E,
    π₁.π k (j₁ w) = j₁ w' ∧ π₂.π k (j₂ w) = j₂ w') ?_ ?_ ?_ ?_ (hgen k hk)
  · rintro _ ⟨Y, ⟨hY, hK⟩, rfl⟩ w
    simpa using hflow Y hY hK 1 w
  · rintro _ ⟨Y, ⟨hY, hK⟩, rfl⟩ w
    have h : (T.expt Y)⁻¹ = T.expt ((-1 : ℝ) • Y) := by
      have := T.expt_add Y hY (-1) 1
      rw [neg_add_cancel, zero_smul, one_smul, T.expt_zero] at this
      exact (eq_inv_of_mul_eq_one_left this.symm).symm
    rw [h]
    exact hflow Y hY hK (-1) w
  · intro w
    exact ⟨w, by simp, by simp⟩
  · intro x y _ _ hx hy w
    obtain ⟨w', h1, h2⟩ := hy w
    obtain ⟨w'', h3, h4⟩ := hx w'
    exact ⟨w'', by rw [map_mul, ContinuousLinearMap.mul_apply, h1, h3],
      by rw [map_mul, ContinuousLinearMap.mul_apply, h2, h4]⟩

end GlobalTheory.RealPar
