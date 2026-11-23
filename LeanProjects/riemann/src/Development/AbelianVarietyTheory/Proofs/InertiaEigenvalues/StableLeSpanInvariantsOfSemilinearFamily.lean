import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory

private lemma span_range_eval_embeddings_eq_whole (F D : Type) [Field F] [Fintype D] (σ : D → (F →+* F))
    (hσ : Function.Injective σ) :
    Submodule.span F (Set.range (fun c : F => fun d : D => σ d c)) = ⊤ := by

  classical
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hli : LinearIndependent F (fun d : D => ((σ d : F →* F) : F → F)) := by
    refine (linearIndependent_monoidHom F F).comp (fun d => (σ d : F →* F)) ?_
    intro a b h
    apply hσ
    ext x
    exact congrArg (fun g : F →* F => g x) h
  rw [Fintype.linearIndependent_iff] at hli
  have hzero : ∑ d, f (Pi.single d 1) • ((σ d : F →* F) : F → F) = 0 := by
    funext c
    have hc : (fun d : D => σ d c) ∈ LinearMap.ker f := hle (Submodule.subset_span ⟨c, rfl⟩)
    rw [LinearMap.mem_ker] at hc
    have hdecomp : (fun d : D => σ d c) = ∑ d, σ d c • Pi.single d (1 : F) := by
      ext e
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hdecomp, map_sum] at hc
    simp only [map_smul, smul_eq_mul] at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hc]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [mul_comm]
  have hall := hli _ hzero
  apply hf0
  ext d
  simpa using hall d

theorem stable_le_span_invariants_of_semilinear_family :
    ∀ (F M D : Type) [Field F] [AddCommGroup M] [Module F M] [Fintype D] (σ : D → (F →+* F)) (t : D → (M →+ M)) (V : Submodule F M), Function.Injective σ → (∀ d (c : F), ∀ y ∈ V, t d (c • y) = σ d c • t d y) → (∀ d, ∀ y ∈ V, t d y ∈ V) → (∀ d, ∀ y ∈ V, t d (∑ d', t d' y) = ∑ d', t d' y) → (∃ d, ∀ y ∈ V, t d y = y) → V ≤ Submodule.span F {y | y ∈ V ∧ ∀ d, t d y = y} := by
  classical
  rintro F M D _ _ _ _ σ t V hσ hsemi hV hinv ⟨d₀, hd₀⟩ y hy
  let W := Submodule.span F {y | y ∈ V ∧ ∀ d, t d y = y}
  let Φ : (D → F) →ₗ[F] M :=
    { toFun := fun w => ∑ d, w d • t d y
      map_add' := by
        intro a b
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp [Finset.smul_sum, smul_smul] }
  have hmem : ∀ c : F, (∑ d, σ d c • t d y) ∈ W := by
    intro c
    apply Submodule.subset_span
    have hcy : c • y ∈ V := V.smul_mem c hy
    have heq : ∑ d, σ d c • t d y = ∑ d, t d (c • y) :=
      Finset.sum_congr rfl fun d _ => (hsemi d c y hy).symm
    rw [heq]
    exact ⟨V.sum_mem fun d _ => hV d _ hcy, fun d => hinv d _ hcy⟩
  have hle : Submodule.span F (Set.range (fun c : F => fun d : D => σ d c)) ≤ W.comap Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact hmem c
  rw [span_range_eval_embeddings_eq_whole F D σ hσ] at hle
  have h1 : Φ (Pi.single d₀ 1) ∈ W := hle Submodule.mem_top
  have h2 : Φ (Pi.single d₀ 1) = y := by
    show ∑ d, (Pi.single d₀ (1 : F) : D → F) d • t d y = y
    rw [Finset.sum_eq_single d₀]
    · simp [hd₀ y hy]
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h2] at h1
  exact h1

end GlobalTheory
