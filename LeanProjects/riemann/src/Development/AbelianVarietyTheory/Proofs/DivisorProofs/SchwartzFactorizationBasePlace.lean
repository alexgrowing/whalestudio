import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.FacAtFixed

open scoped Classical

theorem dec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ Φ ∈ G.M'.So B.ψ B.τ₁, ∃ (N : ℕ) (ψ : Fin N → ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ)) (r : Fin N → ((Fin a' × Fin (a + a') → AF F) → ℂ)), (∀ j, ψ j ∈ G.M'.SoLoc B.ψ B.τ₁) ∧ (∀ j, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁), Rest (evFin F B.v₁) φ (r j)) ∧ (∀ j, ∀ φ ∈ G.M'.SoLoc B.ψ B.τ₁, tens (evFin F B.v₁) φ (r j) ∈ G.M'.So B.ψ B.τ₁) ∧ Φ = ∑ j, tens (evFin F B.v₁) (ψ j) (r j) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT Φ hΦ
  have hstd := hT.geo.hM'.std
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, φ, hSB, hev, hv, rfl⟩ := hΨ
    have hφ : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hev.and hstd).mono fun v hv => hv.1.trans hv.2
    obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor B.v₁ f φ hφ
    refine ⟨1, fun _ => φ B.v₁, fun _ => r, fun _ => hv, fun _ χ hχ => ⟨hr, ?_⟩, fun _ χ hχ => ?_, ?_⟩
    · rw [hrt χ]
      refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φ B.v₁ χ hφ)
      by_cases hw : w = B.v₁
      · subst hw; rw [Function.update_self]; exact hχ
      · rw [Function.update_of_ne hw]; exact hSB w
    · rw [hrt χ]
      refine Submodule.subset_span ⟨f, Function.update φ B.v₁ χ, fun w => ?_, ?_, by rwa [Function.update_self], rfl⟩
      · by_cases hw : w = B.v₁
        · subst hw; rw [Function.update_self]; exact hχ.1
        · rw [Function.update_of_ne hw]; exact hSB w
      · filter_upwards [hev, Filter.eventually_cofinite_ne B.v₁] with w hw hne
        rw [Function.update_of_ne hne]; exact hw
    · rw [Fin.sum_univ_one, hrt, Function.update_eq_self]
  | zero =>
    refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, ?_⟩
    simp
  | add x y _ _ hx hy =>
    obtain ⟨N₁, ψ₁, r₁, h1, h2, h3, rfl⟩ := hx
    obtain ⟨N₂, ψ₂, r₂, k1, k2, k3, rfl⟩ := hy
    refine ⟨N₁ + N₂, Fin.append ψ₁ ψ₂, Fin.append r₁ r₂, ?_, ?_, ?_, ?_⟩
    · intro j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [Fin.append_left]; exact h1 i
      · rw [Fin.append_right]; exact k1 i
    · intro j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [Fin.append_left]; exact h2 i
      · rw [Fin.append_right]; exact k2 i
    · intro j; refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [Fin.append_left]; exact h3 i
      · rw [Fin.append_right]; exact k3 i
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨N₁, ψ₁, r₁, h1, h2, h3, rfl⟩ := hx
    have htc : ∀ (χ : (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) (s : (Fin a' × Fin (a + a') → AF F) → ℂ),
        tens (evFin F B.v₁) χ (c • s) = c • tens (evFin F B.v₁) χ s := by
      intro χ s; funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
    refine ⟨N₁, ψ₁, fun j => c • r₁ j, h1, fun j χ hχ => ⟨fun x z hz => ?_, ?_⟩, fun j χ hχ => ?_, ?_⟩
    · simp only [Pi.smul_apply, (h2 j χ hχ).1 x z hz]
    · rw [htc]; exact Submodule.smul_mem _ c (h2 j χ hχ).2
    · rw [htc]; exact Submodule.smul_mem _ c (h3 j χ hχ)
    · rw [Finset.smul_sum]
      simp only [htc]

end GlobalTheory.FacAtFixed
