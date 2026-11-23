import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFrameBlockEigenRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvaluationCompactSetBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockScaledNormDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockScaledIntegralOfLocalStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus

theorem frameMajorant : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ (M₁ : Model σ X W) (blk : Fin q → Finset (Fin n × Fin d)) (e : Fn F n d →ₗ[ℂ] Fn F n d),
    M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk → IsEv B M M₁ 1 1 ∅ e →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ c : ℝ, 0 < c → ∀ φ ∈ SB (Fin n × Fin d → Af F),
    ∃ A : ℕ, ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (t : Fin q → ℝ) (a κ : UA σ X.J) (h : UA σ W.J),
      (∀ i, c ≤ t i) → IsTorusU x y t a → κ ∈ Cc → ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * (ht h : ℝ) ^ k ∧
        ∀ ξ : Fin n × Fin d → F, ‖e (om (a * κ, h) (pureA F f φ)) (fun j => algebraMap F (AF F) (ξ j))‖ ≤
          C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majI blk A N m t ξ := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP q x y hxy M₁ blk e hG hco hev Cc hCc c hc φ hφ
  obtain ⟨ex, hex⟩ := GlobalTheory.T.pair_frame_block_eigen_relation hKP F E σ B n d X W M χX χW om r s r' s' hP q x y hxy M₁ blk e hG hco hev φ hφ
  obtain ⟨A, hAex⟩ : ∃ A : ℕ, ∀ i, ex i ≤ A := by
    obtain ⟨A, hA⟩ := exists_nat_ge (∑ i, |ex i|)
    exact ⟨A, fun i => (le_abs_self _).trans
      ((Finset.single_le_sum (fun j _ => abs_nonneg (ex j)) (Finset.mem_univ i)).trans hA)⟩
  refine ⟨A, fun N => ?_⟩
  obtain ⟨Cb, k, hb⟩ := GlobalTheory.T.evaluation_compact_set_bound hKP F E σ B n d X W M χX χW om r s r' s' hP M₁ e hG hev Cc hCc φ hφ ((q + 1) * N)
  obtain ⟨Cm, hCm0, hCm⟩ := GlobalTheory.T.block_scaled_norm_decay F blk hco.1 c hc N
  set Ct : ℝ := ∏ i, c ^ (ex i - A) with hCt
  have hCt0 : 0 ≤ Ct := Finset.prod_nonneg fun i _ => Real.rpow_nonneg hc.le _
  refine ⟨Cb * max 1 (Ct * Cm), k, ?_⟩
  intro f t a κ h htc ha hκ
  have ht0 : ∀ i, 0 < t i := fun i => hc.trans_le (htc i)
  obtain ⟨m, hm1, hmC, hz⟩ := hb f κ h hκ
  have hhk : 0 ≤ (ht h : ℝ) ^ k := pow_nonneg (NNReal.coe_nonneg _) _
  have hCb : 0 < Cb := by
    by_contra hneg
    push_neg at hneg
    have h2 : Cb * (ht h : ℝ) ^ k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hhk
    have h3 : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have hmax : 1 ≤ max 1 (Ct * Cm) := le_max_left _ _
  refine ⟨m, hm1, hmC.trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hCb.le hmax) hhk), fun ξ => ?_⟩
  set z : Fin n × Fin d → AF F := fun j => algebraMap F (AF F) (ξ j) with hzdef
  have h1 := hex t a ht0 ha f κ h z
  have hp : 0 ≤ semK (Fin n × Fin d) k f := apply_nonneg _ _
  by_cases hI : ∀ j, IsIntegral ℤ ((m : F) * ξ j)
  · rw [majI, if_pos hI]
    obtain ⟨hbd, -⟩ := hz (blkScale blk t z)
    have hc' := hCm t htc ξ
    have hprod : (∏ i, t i ^ ex i) ≤ Ct * (∏ i, t i) ^ A := by
      rw [hCt, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (ht0 i).le _) (fun i _ => ?_)
      have e1 : t i ^ ex i = t i ^ (ex i - A) * t i ^ (A : ℝ) := by
        rw [← Real.rpow_add (ht0 i)]; ring_nf
      rw [e1, Real.rpow_natCast]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hc (htc i) (by linarith [hAex i])) (pow_nonneg (ht0 i).le _)
    have hW := majW_nonneg blk A N t ξ (fun i => (ht0 i).le)
    have hT : 0 ≤ (∏ i, t i) ^ A := pow_nonneg (Finset.prod_nonneg fun i _ => (ht0 i).le) _
    calc _ ≤ (∏ i, t i ^ ex i) * ‖e (om (κ, h) (pureA F f φ)) (blkScale blk t z)‖ := h1
      _ ≤ (Ct * (∏ i, t i) ^ A) * (Cb * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k *
            ((1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (blkScale blk t z j))) ^ ((q + 1) * N))⁻¹) :=
          mul_le_mul hprod hbd (norm_nonneg _) (mul_nonneg hCt0 hT)
      _ ≤ (Ct * (∏ i, t i) ^ A) * (Cb * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k *
            (Cm * ((∏ i, (1 + t i * ∑ j ∈ blk i, ∑ w : InfinitePlace F, w (ξ j)) ^ N) *
              (1 + ∑ j, ∑ w : InfinitePlace F, w (ξ j)) ^ N)⁻¹)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc' ?_) (mul_nonneg hCt0 hT)
          exact mul_nonneg (mul_nonneg hCb.le hp) hhk
      _ = Cb * (Ct * Cm) * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majW blk A N t ξ := by
          unfold majW; ring
      _ ≤ Cb * max 1 (Ct * Cm) * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majW blk A N t ξ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _) hCb.le) hp) hhk) hW
  · have h0 : e (om (κ, h) (pureA F f φ)) (blkScale blk t z) = 0 := by
      by_contra hne
      exact hI fun j => GlobalTheory.T.block_scaled_integral_of_local F blk t m ξ j fun v => (hz _).2 hne j v
    rw [majI, if_neg hI, mul_zero]
    rw [h0, norm_zero, mul_zero] at h1
    exact h1

end GlobalTheory.ThKTorus
