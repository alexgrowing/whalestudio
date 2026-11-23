import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PreimageTranslate
open AlgebraicGeometry CategoryTheory GlobalTheory.KS

namespace GlobalTheory.KS.Refine

local macro "opens_le" : tactic =>
  `(tactic| (rw [SetLike.le_def]; intro y hy; simp only [TopologicalSpace.Opens.mem_inf] at hy ⊢; aesop))

theorem isCob_of_refine : ∀ {Y : Scheme.{0}} {I J : Type} (Uc : I → Y.Opens) (c : GlobalTheory.KS.C1 Uc),
    GlobalTheory.KS.IsCoc Uc c → ∀ (V : J → Y.Opens) (σ : J → I), (∀ p, V p ≤ Uc (σ p)) → (⨆ p, V p = ⊤) →
    ∀ (B : ∀ p, Γ(Y, V p)), (∀ p p', GlobalTheory.KS.rsT (c (σ p) (σ p')) (V p ⊓ V p') =
      GlobalTheory.KS.rsT (B p') (V p ⊓ V p') - GlobalTheory.KS.rsT (B p) (V p ⊓ V p')) → GlobalTheory.KS.IsCob Uc c := by
  intro Y I J Uc c hc V σ hV hVt B hB
  have hV' : ∀ p y, y ∈ V p → y ∈ Uc (σ p) := fun p y h => hV p h
  have cov : ∀ O : Y.Opens, O ≤ ⨆ p, O ⊓ V p := by
    intro O x hx
    have : x ∈ ⨆ p, V p := by rw [hVt]; trivial
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hx, hp⟩
  have glue : ∀ i, ∃ t : Γ(Y, Uc i), ∀ p, rsT t (Uc i ⊓ V p) =
      rsT (B p) (Uc i ⊓ V p) + rsT (c (σ p) i) (Uc i ⊓ V p) := by
    intro i
    refine exists_rsT_eq (fun p => Uc i ⊓ V p) (fun p => inf_le_left) (cov _) _ fun p p' => ?_
    have h1 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hB p p')
    have h2 := congrArg (fun s => rsT s ((Uc i ⊓ V p) ⊓ (Uc i ⊓ V p'))) (hc (σ p) (σ p') i)
    simp only [rsT_add, rsT_sub] at h1 h2 ⊢
    simp (disch := opens_le) only [rsT_rsT] at h1 h2 ⊢
    linear_combination h1 - h2
  choose t ht using glue
  refine ⟨t, fun i j => ?_⟩
  refine eq_of_rsT_eq (fun p => Uc i ⊓ Uc j ⊓ V p) (fun p => inf_le_left) (cov _) _ _ fun p => ?_
  have h1 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht i p)
  have h2 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (ht j p)
  have h3 := congrArg (fun s => rsT s (Uc i ⊓ Uc j ⊓ V p)) (hc (σ p) i j)
  simp only [rsT_add, rsT_sub] at h1 h2 h3 ⊢
  simp (disch := opens_le) only [rsT_rsT] at h1 h2 h3 ⊢
  linear_combination h1 - h2 + h3

end GlobalTheory.KS.Refine
