import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelBlocksUnitaryFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFrameModelEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFrameModelVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSumPolynomialBoundStatement

noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus

theorem torusDecay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ c : ℝ, 0 < c →
    ∀ φ ∈ SB (Fin n × Fin d → Af F), (∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ M.So B.ψ B.τ₁) →
    ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (t : Fin q → ℝ) (a κ : UA σ X.J) (h : UA σ W.J),
      (∀ i, c ≤ t i) → IsTorusU x y t a → κ ∈ Cc →
      ‖theta om (pureA F f φ) (a * κ) h‖ * (1 + ∏ i, t i) ^ N ≤ C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair q x y hxy Cc hCc c hc φ hφ hφS N
  obtain ⟨M₁, blk, e, c₀, hM₁, hF, hE, hc₀, hθ⟩ := GlobalTheory.T.exists_model_blocks_unitary_frame hP F E σ B n d X W M χX χW om r s r' s' hPair q x y hxy
  obtain ⟨A, hA⟩ := GlobalTheory.T.norm_weil_action_pure_tensor_le_majorant hP F E σ B n d X W M χX χW om r s r' s' hPair q x y hxy M₁ blk e hM₁ hF hE Cc hCc c hc φ hφ
  obtain ⟨N₁, C₅, K, h5⟩ := GlobalTheory.T.lattice_sum_polynomial_bound F (Fin n × Fin d) q blk A N c hc
  obtain ⟨C₄, k, h4⟩ := hA N₁
  refine ⟨‖c₀⁻¹‖ * max C₄ 0 * max C₅ 0 * (max C₄ 0) ^ K, k * (K + 1), fun f t a κ h htc ha hκ => ?_⟩
  obtain ⟨m, hm1, hmC, hb⟩ := h4 f t a κ h htc ha hκ
  obtain ⟨hsum, hle⟩ := h5 m t hm1 htc
  have hΦ : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  have hΨ : om (a * κ, h) (pureA F f φ) ∈ schA F (Fin n × Fin d) := hPair.weil.isUSplitting.pres _ _ hΦ
  have ht0 : ∀ i, 0 ≤ t i := fun i => hc.le.trans (htc i)
  have hsk : 0 ≤ semK (Fin n × Fin d) k f := apply_nonneg _ _
  have hhk : (0 : ℝ) ≤ (ht h : ℝ) ^ k := pow_nonneg (NNReal.coe_nonneg _) _
  have hC4 : (0 : ℝ) ≤ max C₄ 0 := le_max_right _ _
  have hB' : 0 ≤ max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k := mul_nonneg (mul_nonneg hC4 hsk) hhk
  have hpt : ∀ ξ : Fin n × Fin d → F, ‖e (om (a * κ, h) (pureA F f φ)) (fun j => algebraMap F (AF F) (ξ j))‖ ≤
      max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * latG (F := F) blk A N₁ m t ξ := by
    intro ξ
    unfold latG
    split_ifs with hnz
    · calc _ ≤ C₄ * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majI blk A N₁ m t ξ := hb ξ
        _ ≤ max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majI blk A N₁ m t ξ := by
          apply mul_le_mul_of_nonneg_right _ (majI_nonneg _ _ _ _ _ _ ht0)
          apply mul_le_mul_of_nonneg_right _ hhk
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hsk
    · push_neg at hnz
      rw [GlobalTheory.T.unitary_frame_model_evaluation hP F E σ B n d X W M χX χW om r s r' s' hPair q x y hxy M₁ blk e hM₁ hF hE _ (hφS f) (a * κ) h ξ hnz]
      simp
  have hs : Summable fun ξ : Fin n × Fin d → F =>
      ‖e (om (a * κ, h) (pureA F f φ)) (fun j => algebraMap F (AF F) (ξ j))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsum.mul_left _)
  have hT : ‖thetaSum F (e (om (a * κ, h) (pureA F f φ)))‖ ≤
      max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * ∑' ξ, latG (F := F) blk A N₁ m t ξ := by
    rw [← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum hpt hs (hsum.mul_left _))
  have e1 : theta om (pureA F f φ) (a * κ) h = c₀⁻¹ * thetaSum F (e (om (a * κ, h) (pureA F f φ))) := by
    rw [hθ _ hΨ, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]; rfl
  have hP0 : (0 : ℝ) ≤ (1 + ∏ i, t i) ^ N := pow_nonneg (add_nonneg zero_le_one (Finset.prod_nonneg fun i _ => ht0 i)) _
  have hmK : (m : ℝ) ^ K ≤ (max C₄ 0 * (ht h : ℝ) ^ k) ^ K :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hmC.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hhk)) K
  have hsemi : semK (Fin n × Fin d) k f ≤ semK (Fin n × Fin d) (k * (K + 1)) f := by
    have hk : k ≤ k * (K + 1) := Nat.le_mul_of_pos_right k (Nat.succ_pos K)
    have hle' : semK (F := F) (Fin n × Fin d) k ≤ semK (F := F) (Fin n × Fin d) (k * (K + 1)) :=
      Finset.sup_mono (Finset.Iic_subset_Iic.2 (Prod.mk_le_mk.2 ⟨hk, hk⟩))
    exact hle' f
  have hS0 : 0 ≤ ∑' ξ, latG (F := F) blk A N₁ m t ξ := tsum_nonneg fun ξ => latG_nonneg _ _ _ _ _ _ ht0
  calc ‖theta om (pureA F f φ) (a * κ) h‖ * (1 + ∏ i, t i) ^ N
      ≤ ‖c₀⁻¹‖ * (max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * ∑' ξ, latG (F := F) blk A N₁ m t ξ) *
          (1 + ∏ i, t i) ^ N := by
        rw [e1, norm_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT (norm_nonneg _)) hP0
    _ = ‖c₀⁻¹‖ * (max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k) *
          ((∑' ξ, latG (F := F) blk A N₁ m t ξ) * (1 + ∏ i, t i) ^ N) := by ring
    _ ≤ ‖c₀⁻¹‖ * (max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k) * (max C₅ 0 * (m : ℝ) ^ K) :=
        mul_le_mul_of_nonneg_left (hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (Nat.cast_nonneg _) _)))
          (mul_nonneg (norm_nonneg _) hB')
    _ ≤ ‖c₀⁻¹‖ * (max C₄ 0 * semK (Fin n × Fin d) (k * (K + 1)) f * (ht h : ℝ) ^ k) *
          (max C₅ 0 * (max C₄ 0 * (ht h : ℝ) ^ k) ^ K) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsemi hC4) hhk)
          (norm_nonneg _)) (mul_le_mul_of_nonneg_left hmK (le_max_right _ _))
          (mul_nonneg (le_max_right _ _) (pow_nonneg (Nat.cast_nonneg _) _))
        exact mul_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg hC4 (apply_nonneg _ _)) hhk)
    _ = ‖c₀⁻¹‖ * max C₄ 0 * max C₅ 0 * (max C₄ 0) ^ K * semK (Fin n × Fin d) (k * (K + 1)) f *
          (ht h : ℝ) ^ (k * (K + 1)) := by
        rw [mul_pow, ← pow_mul, show k * (K + 1) = k + k * K by ring, pow_add]; ring

end GlobalTheory.ThKTorus
