import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorMulOfPublished
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF

theorem compact_locConst_KAt : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ K : Subgroup (UA σ G.V'.J), IsStab B K → ∀ v : Pl F,
    CompactSpace (KAt K (evFin F v)) ∧ ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      IsLocallyConstant (fun k : KAt K (evFin F v) => locOp v (om' (k.1, 1)) φ) := by
  intro hPr F E _ _ _ _ _ σ B a a' G X om om' hT K hK v
  have hP := GlobalTheory.ThK.Inhab.pairV' hT
  refine ⟨?_, ?_⟩
  · obtain ⟨K₀, -, -, hK₀, hc, -, -⟩ := GlobalTheory.StabHaar.stabEx hPr F E σ B a' G.V' _ _ hP.base hP.herm
    have e : K = K₀ := Subgroup.ext fun g => (hK g).trans (hK₀ g).symm
    subst e
    exact isCompact_iff_compactSpace.1 (isCompact_KAt hc (evFin F v))
  · intro φ hφ
    obtain ⟨U, hU, hUact⟩ := ((GlobalTheory.T.theta_action_exists hPr) F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP v).2.2 φ hφ
    have hmul := locOpMul hPr F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP v
    have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := (UAtSub σ G.W (evFin F v)).one_mem
    rw [IsLocallyConstant.iff_eventually_eq]
    intro k₀
    have hc : Continuous fun k : KAt K (evFin F v) => (((k₀⁻¹ * k : KAt K (evFin F v)) : UA σ G.V'.J), (1 : UA σ G.W.J)) :=
      (continuous_subtype_val.comp (continuous_const.mul continuous_id)).prodMk continuous_const
    have hU' : U ∈ 𝓝 ((((k₀⁻¹ * k₀ : KAt K (evFin F v)) : UA σ G.V'.J), (1 : UA σ G.W.J))) := by
      rw [inv_mul_cancel]; exact hU
    filter_upwards [hc.continuousAt.preimage_mem_nhds hU'] with k hk
    set h : KAt K (evFin F v) := k₀⁻¹ * k with hh
    have hkh : k = k₀ * h := by rw [hh, mul_inv_cancel_left]
    have hhv : (h : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := (mem_KAt.1 h.2).2
    have hk₀v : (k₀ : UA σ G.V'.J) ∈ UAt σ G.V' (evFin F v) := (mem_KAt.1 k₀.2).2
    have hfix : locOp v (om' ((h : UA σ G.V'.J), 1)) φ = φ := locOp_eq hφ hφ (hUact _ hk hhv h1W)
    have e1 : (((k₀ * h : KAt K (evFin F v)) : UA σ G.V'.J), (1 : UA σ G.W.J)) =
        ((k₀ : UA σ G.V'.J), (1 : UA σ G.W.J)) * ((h : UA σ G.V'.J), 1) := by
      simp [Prod.mk_mul_mk]
    show locOp v (om' ((k : UA σ G.V'.J), 1)) φ = locOp v (om' ((k₀ : UA σ G.V'.J), 1)) φ
    rw [hkh, e1, hmul _ _ hk₀v h1W hhv h1W φ hφ, hfix]

end GlobalTheory.ThK.LemF

end
