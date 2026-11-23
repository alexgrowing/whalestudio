import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorMulOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExistsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.KFin

theorem kFinite : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ (v : Pl F), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      IsCompact (KAt K (evFin F v) : Set (UA σ G.V.J)) ∧
        IsLocallyConstant (fun k : KAt K (evFin F v) => locOp v (om (k.1, 1)) φ) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT K hK v φ hφ
  obtain ⟨hpair, -⟩ := GlobalTheory.ThK.Check.isPair_of_isTriple hT
  have hc : IsCompact (K : Set (UA σ G.V.J)) := by
    obtain ⟨K', _, _, hK', hc, -, -⟩ := GlobalTheory.T.theta_stabilizer_exists hP F E σ B a G.V _ _ hpair.base hpair.herm
    have e : K = K' := by
      ext g
      rw [hK g, hK' g]
    subst e
    exact hc
  refine ⟨isCompact_KAt hc _, ?_⟩
  obtain ⟨-, -, h3⟩ := GlobalTheory.T.theta_action_exists hP F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hpair v
  have hmul := GlobalTheory.T.local_operator_mul_of_classicalTheorems hP F E σ B a (a + a') G.V G.W G.M _ _ om _ _ _ _ hpair v
  obtain ⟨U, hU, hUact⟩ := h3 φ hφ
  rw [IsLocallyConstant.iff_eventually_eq]
  intro k₀
  have hcont : Continuous fun k : KAt K (evFin F v) => ((k₀.1⁻¹ * k.1 : UA σ G.V.J), (1 : UA σ G.W.J)) :=
    (continuous_const.mul continuous_subtype_val).prodMk continuous_const
  have h1 : ((k₀.1⁻¹ * k₀.1 : UA σ G.V.J), (1 : UA σ G.W.J)) = 1 := by
    rw [inv_mul_cancel]; rfl
  have hev : ∀ᶠ k in 𝓝 k₀, ((k₀.1⁻¹ * k.1 : UA σ G.V.J), (1 : UA σ G.W.J)) ∈ U :=
    hcont.continuousAt.preimage_mem_nhds (by rw [h1]; exact hU)
  filter_upwards [hev] with k hk
  have hk₀ : k₀.1 ∈ UAt σ G.V (evFin F v) := (mem_KAt.1 k₀.2).2
  have hkk : k.1 ∈ UAt σ G.V (evFin F v) := (mem_KAt.1 k.2).2
  have hx1 : k₀.1⁻¹ * k.1 ∈ UAt σ G.V (evFin F v) :=
    (UAtSub σ G.V (evFin F v)).mul_mem ((UAtSub σ G.V (evFin F v)).inv_mem hk₀) hkk
  have hone : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F v) := (UAtSub σ G.W (evFin F v)).one_mem
  have hact := hUact _ hk hx1 hone
  have hfix : locOp v (om ((k₀.1⁻¹ * k.1 : UA σ G.V.J), (1 : UA σ G.W.J))) φ = φ := locOp_eq hφ hφ hact
  have hprod : ((k.1 : UA σ G.V.J), (1 : UA σ G.W.J)) = (k₀.1, 1) * ((k₀.1⁻¹ * k.1 : UA σ G.V.J), (1 : UA σ G.W.J)) := by
    ext <;> simp
  show locOp v (om (k.1, 1)) φ = locOp v (om (k₀.1, 1)) φ
  rw [hprod, hmul _ _ hk₀ hone hx1 hone φ hφ, hfix]

end GlobalTheory.KFin
