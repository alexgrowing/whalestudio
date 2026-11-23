import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledIntegralFiniteAdelePointsSubsetNhds
import GroundTheory.AutomorphicForms.StrongApproximationSLDense

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaSumNeScaled

theorem exists_thetaSum_pureA_scaledInt_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    Set.indicator {y | y - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ a} (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      thetaSum F (pureA F f (Set.indicator {y | y - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ a} fun _ => (1 : ℂ))) ≠ 0 := by
  intro F _ _ κ _ a _ hg
  classical
  let V := κ → mixedEmbedding.mixedSpace F
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap V ℂ := h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    Set.indicator {y | y - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ a} fun _ => (1 : ℂ) with hgdef
  refine ⟨f, ?_⟩
  set t : (κ → F) → ℂ := fun ξ => pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) with ht
  have hsum : Summable t := summable_pureA F f hg
  have hre : ∀ ξ, (t ξ).re = b (fun i => mixedEmbedding F (ξ i)) *
      (g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))).re := fun ξ => by
    simp only [ht, pureA_algebraMap, hf, Complex.re_ofReal_mul]
  have hg0 : ∀ y, 0 ≤ (g y).re := fun y => by
    rw [hgdef, Set.indicator_apply]
    split_ifs <;> simp
  have hnn : ∀ ξ, 0 ≤ (t ξ).re := fun ξ => by
    rw [hre]; exact mul_nonneg (b.nonneg) (hg0 _)
  have hz : (t 0).re = 1 := by
    rw [hre]
    have h0 : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) ∈
        {y | y - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ a} := by
      show _ - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ a
      have : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) = 0 := by
        funext i; exact map_zero _
      rw [this, sub_zero]
      exact zero_mem _
    have hx : (fun i : κ => mixedEmbedding F ((0 : κ → F) i)) = 0 := by
      funext i; exact map_zero _
    rw [hx, b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
    simp only [g, Set.indicator_of_mem h0, Complex.one_re, one_mul]
  have hpos : 0 < ∑' ξ, (t ξ).re :=
    (Complex.reCLM.summable hsum).tsum_pos hnn 0 (by show 0 < (t 0).re; rw [hz]; exact one_pos)
  intro h
  have : (thetaSum F (pureA F f g)).re = ∑' ξ, (t ξ).re := Complex.re_tsum hsum
  rw [h, Complex.zero_re] at this
  exact hpos.ne' this.symm

end GlobalTheory.ThetaSumNeScaled

end
