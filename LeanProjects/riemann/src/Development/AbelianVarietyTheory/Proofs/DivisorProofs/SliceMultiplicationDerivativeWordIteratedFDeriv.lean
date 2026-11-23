import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerDerivativeSliceDirectionalAddPhaseStatement

open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory.WeilL2Words

theorem slice_word_fderivs (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type)
    [Fintype κ] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hψ : ∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)))
    (vs : List (κ → mixedEmbedding.mixedSpace F)) :
    (fun x => word F ψ (vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) =
        vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y))) := by
  induction vs with
  | nil => exact ⟨rfl, hΦ⟩
  | cons v vs ih =>
    obtain ⟨h1, h2⟩ := ih
    have hd : Differentiable ℝ (fun x => word F ψ (vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) := by
      rw [h1]; exact h2.differentiable (by simp)
    refine ⟨?_, ?_⟩
    · funext x
      simp only [List.map_cons, List.foldr_cons]
      rw [word_cons, GlobalTheory.T.schroedingerDerivative_slice_directional_add_phase F κ ψ ℓ hψ _ y hd (v, 0) x, h1]
      simp
    · simp only [List.foldr_cons]
      exact (h2.fderiv_right (by simp)).clm_apply contDiff_const

theorem slice_word_mul_fderivs : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) →
    ∀ (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (y : κ → FiniteAdeleRing (𝓞 F) F),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) →
      ∀ (u : κ → mixedEmbedding.mixedSpace F) (i : ℕ) (vs : List (κ → mixedEmbedding.mixedSpace F))
        (x : κ → mixedEmbedding.mixedSpace F),
        GlobalTheory.WeilL2Words.word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
          (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
            vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x := by
  intro F _ _ _ κ _ ψ ℓ hψ Φ y hΦ u i vs x
  obtain ⟨h1, h2⟩ := slice_word_fderivs F κ ψ ℓ hψ Φ y hΦ vs
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : κ → mixedEmbedding.mixedSpace F => ℓ (∑ k, x k * u k)) := by
    let L : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
      ℓ ∘ₗ ∑ k, (LinearMap.mulRight ℝ (u k)) ∘ₗ LinearMap.proj k
    have hLe : (fun x : κ → mixedEmbedding.mixedSpace F => ℓ (∑ k, x k * u k)) = L := by
      funext x; simp [L, LinearMap.sum_apply]
    rw [hLe]
    exact (LinearMap.toContinuousLinearMap L).contDiff
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : κ → mixedEmbedding.mixedSpace F => 2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hL)
  suffices H : ∀ i : ℕ,
      (fun x => word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) =
        (fun x => (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
          vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * u k) : ℂ)) ^ i *
          vs.foldr (fun v g' => fun z => fderiv ℝ g' z v) (fun x => Φ (GlobalTheory.WeilCont.adeleJoin F x y)) x) by
    exact congrFun (H i).1 x
  intro i
  induction i with
  | zero =>
    refine ⟨?_, ?_⟩
    · funext x; simp only [List.replicate_zero, List.nil_append, pow_zero, one_mul]; exact congrFun h1 x
    · simpa using h2
  | succ i ih =>
    obtain ⟨e1, e2⟩ := ih
    have hd : Differentiable ℝ (fun x =>
        word F ψ (List.replicate i (0, u) ++ vs.map fun v => (v, 0)) Φ (GlobalTheory.WeilCont.adeleJoin F x y)) := by
      rw [e1]; exact e2.differentiable (by simp)
    refine ⟨?_, (hc.pow (i + 1)).mul h2⟩
    funext x
    rw [List.replicate_succ, List.cons_append, word_cons, GlobalTheory.T.schroedingerDerivative_slice_directional_add_phase F κ ψ ℓ hψ _ y hd (0, u) x]
    have e1x := congrFun e1 x
    simp only [ContinuousLinearMap.map_zero, zero_add, e1x]
    ring

end GlobalTheory.WeilL2Words
