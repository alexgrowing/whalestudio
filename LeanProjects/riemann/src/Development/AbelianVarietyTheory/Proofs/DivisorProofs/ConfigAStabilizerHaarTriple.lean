import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactTorusGroupMeasureDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerLocallyCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalMeasurableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerHaarRightInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalStabilizerMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCompactSubgroupTopologyStatement

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

theorem quotInv : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ m : (AE F E)ˣ → UA σ G.V.J,
      (∀ t ∈ idelesAt E (evFin F v), IsLevi H t (1 : UA σ G₁.V.J) (m t) ∧ m t ∈ UAt σ G.V (evFin F v)) →
      ∀ f : UA σ G.V.J → ℂ,
      (∀ q ∈ UAt σ G.V (evFin F v), mat q *ᵥ incV F H.x = incV F H.x → ∀ x ∈ UAt σ G.V (evFin F v), f (q * x) = f x) →
      Continuous (fun x : UAtSub σ G.V (evFin F v) => f x.1) →
      (∀ g ∈ UAt σ G.V (evFin F v), Integrable (fun p : KAt K (evFin F v) × idelesAt E (evFin F v) =>
          f ((m p.2.1)⁻¹ * p.1.1 * g) * ((absE F E p.2.1 : ℝ) : ℂ) ^ (b + 1)) (μK.prod μ)) →
      ∀ g ∈ UAt σ G.V (evFin F v),
        ∫ k, ∫ t, f ((m t.1)⁻¹ * k.1 * g) * ((absE F E t.1 : ℝ) : ℂ) ^ (b + 1) ∂μ ∂μK =
          ∫ k, ∫ t, f ((m t.1)⁻¹ * k.1) * ((absE F E t.1 : ℝ) : ℂ) ^ (b + 1) ∂μ ∂μK := by
  intro hP F E _ _ _ _ _ σ B b a' G G₁ H H' hcfg K hK X om om' om₁ om₁' hT hT₁ v μK μ hμK hμ m hm f hfQ hfc hint g hg
  obtain ⟨m₀, hemb, hlev, htriv⟩ := GlobalTheory.T.levi_embedding_local_closed F E σ B b a' G G₁ H H' hcfg X om om' om₁ om₁' hT hT₁ v
  obtain ⟨hLC, hSC, hT2, huni⟩ := GlobalTheory.T.local_stabilizer_locally_compact F E σ B b a' G G₁ H H' hcfg X om om' om₁ om₁' hT hT₁ v
  obtain ⟨hQc, hPc⟩ := GlobalTheory.T.levi_embedding_local_measurable F E σ B b a' G G₁ H H' hcfg X om om' om₁ om₁' hT hT₁ v m₀ hlev
  have hQu := GlobalTheory.T.local_stabilizer_haar_right_invariant F E σ B b a' G G₁ H H' hcfg X om om' om₁ om₁' hT hT₁ v
  obtain ⟨hKc, hKs, hKt⟩ := GlobalTheory.T.local_compact_subgroup_topology F E σ B b a' G G₁ H H' hcfg X om om' om₁ om₁' hT hT₁ v K hK
  have hIw := GlobalTheory.T.levi_embedding_local_stabilizer_mem F E σ B b a' G G₁ H H' hcfg X om om' om₁ om₁' hT hT₁ v K hK m₀ hlev
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI := hKc
  haveI := hKs
  haveI := hKt

  have hinvx : ∀ t : idelesAt E (evFin F v),
      mat (m₀ t).1⁻¹ *ᵥ incV F H.x = (((t.1)⁻¹ : (AE F E)ˣ) : AE F E) • incV F H.x := by
    intro t
    have e : (m₀ t).1⁻¹ = (m₀ t⁻¹).1 := by rw [map_inv]; rfl
    rw [e, (hlev t⁻¹).1]
    rfl
  have hn : ∀ t, ∀ q ∈ stabAt σ G.V (evFin F v) H.x, (m₀ t)⁻¹ * q * m₀ t ∈ stabAt σ G.V (evFin F v) H.x := by
    intro t q hq
    rw [mem_stabAt] at hq ⊢
    show mat ((m₀ t).1⁻¹ * q.1 * (m₀ t).1) *ᵥ incV F H.x = incV F H.x
    rw [GlobalTheory.StabHaar.mat_mul, GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hlev t).1,
      Matrix.mulVec_smul, hq, Matrix.mulVec_smul, hinvx t, smul_smul, Units.mul_inv, one_smul]
  have key : ∀ t : idelesAt E (evFin F v), ∀ y ∈ UAt σ G.V (evFin F v), f ((m t.1)⁻¹ * y) = f ((m₀ t).1⁻¹ * y) := by
    intro t y hy
    obtain ⟨hl, hmu⟩ := hm t.1 t.2
    have hq : (m₀ t).1⁻¹ * m t.1 ∈ UAt σ G.V (evFin F v) :=
      (UAtSub σ G.V (evFin F v)).mul_mem ((UAtSub σ G.V (evFin F v)).inv_mem (m₀ t).2) hmu
    have hqx : mat ((m₀ t).1⁻¹ * m t.1) *ᵥ incV F H.x = incV F H.x := by
      rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hl.1, Matrix.mulVec_smul, hinvx t, smul_smul, Units.mul_inv,
        one_smul]
    have hy' : (m t.1)⁻¹ * y ∈ UAt σ G.V (evFin F v) :=
      (UAtSub σ G.V (evFin F v)).mul_mem ((UAtSub σ G.V (evFin F v)).inv_mem hmu) hy
    rw [← hfQ _ hq hqx _ hy']
    congr 1
    group
  let f' : UAtSub σ G.V (evFin F v) → ℂ := fun x => f x.1
  have pw : ∀ (k : KAt K (evFin F v)) (t : idelesAt E (evFin F v)) (g' : UAtSub σ G.V (evFin F v)),
      f ((m t.1)⁻¹ * k.1 * g'.1) * ((absE F E t.1 : ℝ) : ℂ) ^ (b + 1) =
        f' ((m₀ t)⁻¹ * kIncl K (evFin F v) k * g') * ((absPow E (evFin F v) (b + 1) t : ℝ) : ℂ) := by
    intro k t g'
    have hk : k.1 * g'.1 ∈ UAt σ G.V (evFin F v) := (UAtSub σ G.V (evFin F v)).mul_mem (mem_KAt.1 k.2).2 g'.2
    rw [mul_assoc, key t _ hk, absPow_apply, NNReal.coe_pow, Complex.ofReal_pow, ← mul_assoc]
    rfl
  have hδ : Continuous (absPow E (evFin F v) (b + 1)) :=
    (continuous_pow (b + 1)).comp (GlobalTheory.Doubling.continuous_absE.comp continuous_subtype_val)
  have hκ : Continuous (kIncl K (evFin F v)) :=
    Continuous.subtype_mk continuous_subtype_val (fun k => (mem_KAt.1 k.2).2)
  have hfQ' : ∀ q ∈ stabAt σ G.V (evFin F v) H.x, ∀ x : UAtSub σ G.V (evFin F v), f' (q * x) = f' x :=
    fun q hq x => hfQ q.1 q.2 hq x.1 x.2
  have hint' : ∀ g' : UAtSub σ G.V (evFin F v), Integrable (fun p : KAt K (evFin F v) × idelesAt E (evFin F v) =>
      f' ((m₀ p.2)⁻¹ * kIncl K (evFin F v) p.1 * g') * ((absPow E (evFin F v) (b + 1) p.2 : ℝ) : ℂ)) (μK.prod μ) := by
    intro g'
    refine (hint g'.1 g'.2).congr (Filter.Eventually.of_forall fun p => ?_)
    exact pw p.1 p.2 g'
  have hA := GlobalTheory.T.compact_torus_group_measure_decomposition (UAtSub σ G.V (evFin F v)) (KAt K (evFin F v)) (idelesAt E (evFin F v))
    (stabAt σ G.V (evFin F v) H.x) (kIncl K (evFin F v)) m₀ (absPow E (evFin F v) (b + 1)) μK μ hQc hκ hemb hδ hμK hμ
    huni hQu hn (GlobalTheory.T.levi_embedding_local_continuous F E σ B b a' G G₁ H H' hcfg X om om' om₁ om₁' hT hT₁ v m₀ hlev hn) htriv hPc hIw f'
    hfc hfQ' hint' ⟨g, hg⟩
  have e1 : ∀ k : KAt K (evFin F v), ∫ t, f ((m t.1)⁻¹ * k.1 * g) * ((absE F E t.1 : ℝ) : ℂ) ^ (b + 1) ∂μ =
      ∫ t, f' ((m₀ t)⁻¹ * kIncl K (evFin F v) k * ⟨g, hg⟩) * ((absPow E (evFin F v) (b + 1) t : ℝ) : ℂ) ∂μ :=
    fun k => integral_congr_ae (Filter.Eventually.of_forall fun t => pw k t ⟨g, hg⟩)
  have e2 : ∀ k : KAt K (evFin F v), ∫ t, f ((m t.1)⁻¹ * k.1) * ((absE F E t.1 : ℝ) : ℂ) ^ (b + 1) ∂μ =
      ∫ t, f' ((m₀ t)⁻¹ * kIncl K (evFin F v) k) * ((absPow E (evFin F v) (b + 1) t : ℝ) : ℂ) ∂μ := by
    intro k
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have := pw k t 1
    simp only [mul_one, OneMemClass.coe_one] at this
    exact this
  exact (integral_congr_ae (Filter.Eventually.of_forall e1)).trans
    (hA.trans (integral_congr_ae (Filter.Eventually.of_forall e2)).symm)

end GlobalTheory.ThK.LemF.QuotInv
