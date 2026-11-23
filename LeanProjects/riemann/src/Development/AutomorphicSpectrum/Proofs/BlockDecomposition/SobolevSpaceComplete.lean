import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevOperatorFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLimitRightDerivativesStatement

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobComplete

section Limit

variable {n : ℕ} [MeasurableSpace (G n)] {μ : Measure (G n)}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem ae_eq_of_tendsto {K : ℕ → Mat n → V} {L : Mat n → V} {y : Lp V 2 μ}
    (hK : ∀ k, MemLp (fun g : G n => K k g.val) 2 μ)
    (hy : Tendsto (fun k => cls μ (K k)) atTop (𝓝 y))
    (hp : ∀ g : G n, Tendsto (fun k => K k g.val) atTop (𝓝 (L g.val))) :
    y =ᵐ[μ] fun g : G n => L g.val := by
  have hm : TendstoInMeasure μ (fun k => (cls μ (K k) : G n → V)) atTop y :=
    tendstoInMeasure_of_tendsto_Lp hy
  obtain ⟨ns, hns0, hns⟩ := hm.exists_seq_tendsto_ae
  have hc : ∀ᵐ g ∂μ, ∀ k, (cls μ (K k) : G n → V) g = K k (g : G n).val :=
    ae_all_iff.2 fun k => by
      have e : cls μ (K k) = (hK k).toLp _ := dif_pos (hK k)
      rw [e]
      exact (hK k).coeFn_toLp
  filter_upwards [hns, hc] with g h1 h2
  simp only [h2] at h1
  exact tendsto_nhds_unique h1 ((hp g).comp (StrictMono.tendsto_atTop hns0))

end Limit

theorem sob_complete : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], SobG →
    ∀ a : ℕ → Mat n → V, (∀ k, Sob μ (a k)) → (∀ w, CauchySeq fun k => cls μ (Rw w (a k))) →
    ∃ b : Mat n → V, Sob μ b ∧ (∀ w, Tendsto (fun k => cls μ (Rw w (a k))) atTop (𝓝 (cls μ (Rw w b)))) ∧
      ∀ g ∈ GLs n, Tendsto (fun k => a k g) atTop (𝓝 (b g)) := by
  intro n _ _ μ _ V _ _ _ hS a ha hC
  obtain ⟨S, C, hb'⟩ := GlobalTheory.CompanionTheory.CurveJ.sup_bound hS n μ
  have hb := hb' V
  have hs : ∀ k w, Sob μ (Rw w (a k)) := fun k w => GlobalTheory.CompanionTheory.SobOpsPf.sob_Rw w (ha k)
  have hU : ∀ w, UniformCauchySeqOn (fun k => Rw w (a k)) atTop (GLs n) := by
    intro w
    have hT : Tendsto (fun p : ℕ × ℕ => C * ∑ w' ∈ S,
        dist (cls μ (Rw w' (Rw w (a p.1)))) (cls μ (Rw w' (Rw w (a p.2))))) (atTop ×ˢ atTop) (𝓝 0) := by
      have e0 : (C * ∑ w' ∈ S, (0 : ℝ)) = 0 := by simp
      rw [← e0]
      refine Tendsto.const_mul C (tendsto_finset_sum _ fun w' _ => ?_)
      have h1 := hC (w' ++ w)
      simp only [← GlobalTheory.CompanionTheory.CurveJ.Rw_append] at h1
      rw [prod_atTop_atTop_eq]
      exact cauchySeq_iff_tendsto_dist_atTop_0.1 h1
    intro u hu
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
    filter_upwards [hT.eventually (gt_mem_nhds hε)] with p hp x hx
    refine hεu ?_
    have b := GlobalTheory.CompanionTheory.CurveJ.bound3 hb (hs p.1 w) (hs p.2 w) (hs p.2 w) 0 hx
    simp only [zero_smul, sub_zero, ← dist_eq_norm] at b
    exact lt_of_le_of_lt b hp
  obtain ⟨Gf, hG, hsm, hR⟩ := GlobalTheory.T.uniform_limit_right_derivatives n V a (fun k => (ha k).1) hU
  have hy : ∀ w, ∃ y : Lp V 2 μ, Tendsto (fun k => cls μ (Rw w (a k))) atTop (𝓝 y) := fun w =>
    cauchySeq_tendsto_of_complete (hC w)
  choose y hy using hy
  have hae : ∀ w, y w =ᵐ[μ] fun g : G n => Rw w (Gf []) g.val := by
    intro w
    have h := ae_eq_of_tendsto (fun k => (hs k w).2 []) (K := fun k => Rw w (a k)) (L := Gf w) (hy w)
      (fun g => (hG w).tendsto_at (GlobalTheory.CompanionTheory.SobOpsPf.val_mem g))
    filter_upwards [h] with g hg
    rw [hg, hR w _ (GlobalTheory.CompanionTheory.SobOpsPf.val_mem g)]
  have hM : ∀ w, MemLp (fun g : G n => Rw w (Gf []) g.val) 2 μ := fun w =>
    (Lp.memLp (y w)).ae_eq (hae w)
  have hcl : ∀ w, cls μ (Rw w (Gf [])) = y w := by
    intro w
    rw [GlobalTheory.CompanionTheory.CurveJ.cls_of (hM w)]
    exact Lp.ext ((hM w).coeFn_toLp.trans (hae w).symm)
  refine ⟨Gf [], ⟨hsm, hM⟩, fun w => ?_, fun g hg => (hG []).tendsto_at hg⟩
  rw [hcl w]
  exact hy w

end GlobalTheory.CompanionTheory.SobComplete
