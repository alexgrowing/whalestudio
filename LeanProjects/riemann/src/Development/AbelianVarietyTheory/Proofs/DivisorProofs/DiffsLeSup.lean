import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev

noncomputable section

namespace GlobalTheory.ThK.DescB

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def thetaSpanV (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a') : Submodule ℂ (UA σ G.W.J → ℂ) :=
  Submodule.span ℂ {f | ∃ Φ, ∃ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' ∧ f = G.M.I om Φ}

def thetaSpanV' (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om' : Rep σ G.V' G.W) (R : RealMaps F a a')
    (Rf : FinMaps F a a') : Submodule ℂ (UA σ G.W.J → ℂ) :=
  Submodule.span ℂ {f | ∃ Φ, ∃ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' ∧ f = G.M'.I om' Φ'}

theorem diffs_le_sup (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a') (c : ℂ) :
    Diffs B G X om om' R Rf c ≤ thetaSpanV B G X om R Rf ⊔ thetaSpanV' B G X om' R Rf := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨Φ, Φ', hΦ', hm, rfl⟩
  have h1 : G.M.I om Φ ∈ thetaSpanV B G X om R Rf := Submodule.subset_span ⟨Φ, Φ', hΦ', hm, rfl⟩
  have h2 : G.M'.I om' Φ' ∈ thetaSpanV' B G X om' R Rf := Submodule.subset_span ⟨Φ, Φ', hΦ', hm, rfl⟩
  have : (fun h => G.M.I om Φ h - c * G.M'.I om' Φ' h) = G.M.I om Φ + (-c) • G.M'.I om' Φ' := by
    funext h; simp [sub_eq_add_neg]
  rw [SetLike.mem_coe, this]
  exact Submodule.add_mem_sup h1 (Submodule.smul_mem _ _ h2)

end GlobalTheory.ThK.DescB

end
