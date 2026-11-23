import Mathlib
import Formalism.PeriodIntegrals.KerIso

noncomputable section
open scoped BigOperators

namespace PI.KerExtCWork

theorem ringHom_coeff_zero {E : Type} [Field E] {n : Type} [Fintype n]
    (τ : n → E →+* ℂ) (hτ : Function.Injective τ) (c : n → ℂ)
    (h : ∀ e : E, ∑ i, c i * τ i e = 0) : c = 0 := by
  have hinj : Function.Injective (fun i => (τ i).toMonoidHom) := by
    intro i j hij
    apply hτ
    ext x
    exact DFunLike.congr_fun hij x
  have hli := (linearIndependent_monoidHom E ℂ).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  funext i
  apply hli c
  funext e
  simpa [Finset.sum_apply, smul_eq_mul] using h e

theorem extC : PI.KerIso.ExtC := by
  intro K E _ _ _ _ n _ φ τ hτ hφ _ g
  classical
  let ι : (Fin 4 → E) → (Fin 4 × n → ℂ) := fun x w => τ w.2 (x w.1)
  let b : Fin 4 × n → (Fin 4 → E) := fun v => g.symm (Pi.single v 1)
  let M : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ) :=
    { toFun := fun c => ∑ v, c v • ι (b v)
      map_add' := by intro c d; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro r c; simp [Finset.smul_sum, smul_smul] }
  have hx : ∀ x : Fin 4 → E, x = ∑ v, g x v • b v := by
    intro x
    have hgx : g x = ∑ v, g x v • (Pi.single v (1 : K) : Fin 4 × n → K) := by
      ext w
      simp [Finset.sum_apply, Pi.single_apply]
    calc x = g.symm (g x) := (g.symm_apply_apply x).symm
      _ = g.symm (∑ v, g x v • (Pi.single v (1 : K) : Fin 4 × n → K)) := by
          conv_lhs => rw [hgx]
      _ = ∑ v, g x v • b v := by
          rw [map_sum]
          simp only [LinearEquiv.map_smul, b]
  have hι : ∀ k : Fin 4 × n → K, ι (∑ v, k v • b v) = ∑ v, φ (k v) • ι (b v) := by
    have hs : ∀ i (k : K) (y : E), τ i (k • y) = φ k * τ i y := by
      intro i k y
      rw [Algebra.smul_def, map_mul, hφ]
    intro k
    funext w
    simp only [ι, Finset.sum_apply, Pi.smul_apply, map_sum, hs, smul_eq_mul]
  have hM : ∀ x : Fin 4 → E, M (fun v => φ (g x v)) = ι x := by
    intro x
    exact (hι (g x)).symm.trans (congrArg ι (hx x).symm)
  have hsurj : Function.Surjective M := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨f, hf0, hf⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    apply hf0
    have hfι : ∀ x, f (ι x) = 0 := by
      intro x
      have hmem : f (M (fun v => φ (g x v))) ∈ (LinearMap.range M).map f :=
        Submodule.mem_map_of_mem (LinearMap.mem_range_self M _)
      rw [hf, Submodule.mem_bot, hM] at hmem
      exact hmem
    have hc : ∀ a i, f (Pi.single (a, i) 1) = 0 := by
      intro a
      have h0 := ringHom_coeff_zero τ hτ (fun i => f (Pi.single (a, i) 1)) ?_
      · intro i; exact congrFun h0 i
      intro e
      have h1 : ι (Pi.single a e) = ∑ i, τ i e • (Pi.single (a, i) 1 : Fin 4 × n → ℂ) := by
        funext w
        rcases w with ⟨a', i'⟩
        by_cases ha : a' = a
        · subst ha
          simp [ι, Finset.sum_apply, Pi.single_apply]
        · simp [ι, Finset.sum_apply, ha]
      have h2 := hfι (Pi.single a e)
      rw [h1, map_sum] at h2
      simpa [smul_eq_mul, mul_comm] using h2
    refine (Pi.basisFun ℂ (Fin 4 × n)).ext (fun w => ?_)
    rcases w with ⟨a, i⟩
    simp only [Pi.basisFun_apply, LinearMap.zero_apply]
    exact hc a i
  let e := LinearEquiv.ofBijective M ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩
  refine ⟨e.symm, fun x => ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  exact (hM x).symm

end PI.KerExtCWork
