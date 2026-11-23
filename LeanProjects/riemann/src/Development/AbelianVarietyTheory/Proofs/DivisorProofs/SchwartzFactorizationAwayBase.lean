import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaGoodPlaceLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLatticeSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarFunctionalGoodPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

open scoped Classical

namespace GlobalTheory.SoFactorAt

theorem tens_smul {F : Type} [Field F] [NumberField F] {R κ : Type} (ev : AF F → R) (φ : (κ → R) → ℂ)
    (r : (κ → AF F) → ℂ) (c : ℂ) : tens ev φ (c • r) = c • tens ev φ r := by
  funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring

theorem dec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ Φ ∈ G.M'.So B.ψ B.τ₁, ∀ v : Pl F, v ≠ B.v₁ → ∃ (N : ℕ) (ψ : Fin N → ((Fin a' × Fin (a + a') → Fv F v) → ℂ)) (r : Fin N → ((Fin a' × Fin (a + a') → AF F) → ℂ)), (∀ j, ψ j ∈ SB (Fin a' × Fin (a + a') → Fv F v)) ∧ (∀ j, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rest (evFin F v) φ (r j) ∧ tens (evFin F v) φ (r j) ∈ G.M'.So B.ψ B.τ₁) ∧ Φ = ∑ j, tens (evFin F v) (ψ j) (r j) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT Φ hΦ v hv
  unfold Model.So at hΦ
  induction hΦ using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨f, φ, hSB, hev, hv₁, rfl⟩ := hΨ
    have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
      (hev.and hT.geo.hM'.std).mono fun w hw => hw.1.trans hw.2
    obtain ⟨ρ, hρ, hρt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
    refine ⟨1, fun _ => φ v, fun _ => ρ, fun _ => hSB v, fun _ ψ₀ hψ₀ => ?_, ?_⟩
    · have hmem : ∀ w, Function.update φ v ψ₀ w ∈ SB _ := by
        intro w
        by_cases hw : w = v
        · subst hw; rw [Function.update_self]; exact hψ₀
        · rw [Function.update_of_ne hw]; exact hSB w
      have hst' := GlobalTheory.PureFactor.update_eventually φ v ψ₀ hstd
      refine ⟨⟨hρ, by rw [hρt]; exact GlobalTheory.TensUniq.pure_mem_schA f _ hmem hst'⟩, ?_⟩
      rw [hρt]
      refine Submodule.subset_span ⟨f, Function.update φ v ψ₀, hmem, ?_, ?_, rfl⟩
      · filter_upwards [hev, Filter.eventually_cofinite_ne v] with w hw hne
        rw [Function.update_of_ne hne]; exact hw
      · rw [Function.update_of_ne (Ne.symm hv)]; exact hv₁
    · rw [Fin.sum_univ_one, hρt, Function.update_eq_self]
  | zero =>
    exact ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, ψ, r, h1, h2, rfl⟩ := hx
    obtain ⟨N', ψ', r', h1', h2', rfl⟩ := hy
    refine ⟨N + N', Fin.append ψ ψ', Fin.append r r', ?_, ?_, ?_⟩
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [Fin.append_left]; exact h1 i
      · rw [Fin.append_right]; exact h1' i
    · intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · rw [Fin.append_left]; exact h2 i
      · rw [Fin.append_right]; exact h2' i
    · rw [Fin.sum_univ_add]; simp only [Fin.append_left, Fin.append_right]
  | smul c x _ hx =>
    obtain ⟨N, ψ, r, h1, h2, rfl⟩ := hx
    refine ⟨N, ψ, fun j => c • r j, h1, fun j φ hφ => ?_, ?_⟩
    · obtain ⟨⟨hinv, hsch⟩, hSo⟩ := h2 j φ hφ
      refine ⟨⟨fun x z hz => ?_, ?_⟩, ?_⟩
      · simp only [Pi.smul_apply, hinv x z hz]
      · rw [tens_smul]; exact Submodule.smul_mem _ c hsch
      · rw [tens_smul]; exact Submodule.smul_mem _ c hSo
    · rw [Finset.smul_sum]; simp only [tens_smul]

end GlobalTheory.SoFactorAt

end
