import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajINonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticBlockBasisOrthogonal

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThKTorus.FrameBlock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tAd_one : tAd F 1 = 1 := by
  have hr : realAd F 0 = 0 := by
    simp only [realAd, map_zero]
    rfl
  rw [tAd, sub_self, hr, add_zero]

theorem eq_zero_of_tAd_mul_eq {r s : ℝ} (hrs : r ≠ s) (u : F)
    (h : tAd F r * algebraMap F (AF F) u = tAd F s * algebraMap F (AF F) u) : u = 0 := by
  have hadd : ∀ a b : AF F, evI F (a + b) = evI F a + evI F b := fun a b =>
    map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have hmul : ∀ a b : AF F, evI F (a * b) = evI F a * evI F b := fun a b =>
    map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
  have hone : evI F 1 = 1 := map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have hreal : ∀ t : ℝ, evI F (realAd F t) = algebraMap ℝ _ t := fun t => by simp [evI, realAd]
  have halg : evI F (algebraMap F (AF F) u) = mixedEmbedding F u := by
    rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl
  have ht : ∀ t : ℝ, evI F (tAd F t) = algebraMap ℝ _ t := fun t => by
    rw [tAd, hadd, hone, hreal, map_sub, map_one, add_sub_cancel]
  have h1 := congrArg (evI F) h
  rw [hmul, hmul, ht, ht, halg, ← Algebra.smul_def, ← Algebra.smul_def, ← sub_eq_zero, ← sub_smul,
    smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd (sub_eq_zero.1 h1) hrs
  · exact mixedEmbedding_injective F (h1.trans (map_zero _).symm)

end GlobalTheory.ThKTorus.FrameBlock

open GlobalTheory.ThKTorus.FrameBlock GlobalTheory.ThKTorus.FrameCoords

theorem GlobalTheory.ThKTorus.frameCo_vecMulVec_mem_block : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (q : ℕ) (x y : Fin q → Fin n → E) (M₁ : Model σ X W)
    (blk : Fin q → Finset (Fin n × Fin d)), M₁.IsGood B.ψ → IsFrameCo σ X.J W.J x y M₁.co blk →
    (∀ t : Fin q → ℝ, (∀ i, 0 < t i) → ∃ a : UA σ X.J, IsTorusU x y t a) →
    ∀ (i : Fin q) (z : Fin d → AE F E), ∃ z' : Fin n × Fin d → AF F, (∀ j, j ∉ blk i → z' j = 0) ∧
      M₁.co.e (Matrix.vecMulVec (incV F (x i)) z) = (0, z') := by
  intro F E _ _ _ _ _ σ B n d X W q x y M₁ blk hG hF hT i
  classical
  let t : Fin q → ℝ := Function.update (fun _ => 1) i 2
  have hti : t i = 2 := by simp [t]
  have htk : ∀ k, k ≠ i → t k = 1 := fun k hk => by simp [t, hk]
  have ht : ∀ k, 0 < t k := fun k => by
    by_cases hk : k = i
    · rw [hk, hti]; norm_num
    · rw [htk k hk]; norm_num
  obtain ⟨a, ha⟩ := hT t ht
  have hprod : ∀ s : Fin q → ℝ, (∀ k, k ≠ i → s k = 1) → ∀ j : Fin n × Fin d,
      (∏ k, if j ∈ blk k then tAd F (s k) else 1) = tAd F (if j ∈ blk i then s i else 1) := by
    intro s hs j
    rw [Finset.prod_eq_single i (fun k _ hk => by rw [hs k hk, tAd_one, ite_self])
      (fun h => absurd (Finset.mem_univ i) h)]
    split_ifs
    · rfl
    · exact tAd_one.symm

  have hrat : ∀ z₀ : Fin d → E, (M₁.co.e (Matrix.vecMulVec (incV F (x i)) (incV F z₀))).1 = 0 ∧
      ∀ j, j ∉ blk i → (M₁.co.e (Matrix.vecMulVec (incV F (x i)) (incV F z₀))).2 j = 0 := by
    intro z₀
    obtain ⟨u, v, huv⟩ := hG.rat (Matrix.vecMulVec (x i) z₀)
    rw [incM_vecMulVec] at huv
    set w := Matrix.vecMulVec (incV F (x i)) (incV F z₀) with hw
    have h1 : mat a * w = tAd F 2 • w := by
      rw [hw, mul_vecMulVec_eq, mulVec_eq_tAd _ _ _ (ha.1 i), hti]
      ext r l
      simp [Matrix.vecMulVec_apply, smul_mul_assoc]
    have h2 : w = M₁.co.e.symm (fun j => algebraMap F (AF F) (u j), 0) +
        M₁.co.e.symm (0, fun j => algebraMap F (AF F) (v j)) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, ← huv, LinearEquiv.symm_apply_apply]
    have h3 : M₁.co.e (mat a * w) = (blkScale blk (fun k => (t k)⁻¹) fun j => algebraMap F (AF F) (u j),
        blkScale blk t fun j => algebraMap F (AF F) (v j)) := by
      conv_lhs => rw [h2]
      rw [Matrix.mul_add, map_add, (hF.2 t a ht ha _).1, (hF.2 t a ht ha _).2, Prod.mk_add_mk, add_zero, zero_add]
    rw [h1, map_smul, huv] at h3
    rw [huv]
    refine ⟨funext fun j => ?_, fun j hj => ?_⟩
    · have h4 := congrFun (congrArg Prod.fst h3) j
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, blkScale] at h4
      rw [hprod _ (fun k hk => by rw [htk k hk, inv_one]), hti] at h4
      have := eq_zero_of_tAd_mul_eq (by split_ifs <;> norm_num) _ h4
      simp [this]
    · have h4 := congrFun (congrArg Prod.snd h3) j
      simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, blkScale] at h4
      rw [hprod _ htk, if_neg hj] at h4
      have := eq_zero_of_tAd_mul_eq (by norm_num) _ h4
      simp [this]

  let P : (Fin d → AE F E) → Prop := fun z => (M₁.co.e (Matrix.vecMulVec (incV F (x i)) z)).1 = 0 ∧
      ∀ j, j ∉ blk i → (M₁.co.e (Matrix.vecMulVec (incV F (x i)) z)).2 j = 0
  have hP0 : P 0 := by
    have e : Matrix.vecMulVec (incV F (x i)) (0 : Fin d → AE F E) = 0 := by
      ext r l
      rw [Matrix.vecMulVec_apply, Pi.zero_apply, mul_zero, Matrix.zero_apply]
    refine ⟨?_, fun j _ => ?_⟩
    · rw [e, map_zero]; rfl
    · rw [e, map_zero]; rfl
  have hPadd : ∀ z z', P z → P z' → P (z + z') := by
    intro z z' h h'
    have e : Matrix.vecMulVec (incV F (x i)) (z + z') =
        Matrix.vecMulVec (incV F (x i)) z + Matrix.vecMulVec (incV F (x i)) z' := by
      ext r l
      simp [Matrix.vecMulVec_apply, mul_add]
    refine ⟨?_, fun j hj => ?_⟩
    · rw [e, map_add, Prod.fst_add, h.1, h'.1, add_zero]
    · rw [e, map_add, Prod.snd_add, Pi.add_apply, h.2 j hj, h'.2 j hj, add_zero]
  have hPsmul : ∀ (c : AF F) z, P z → P (c • z) := by
    intro c z h
    have e : Matrix.vecMulVec (incV F (x i)) (c • z) = c • Matrix.vecMulVec (incV F (x i)) z := by
      ext r l
      simp [Matrix.vecMulVec_apply]
    refine ⟨?_, fun j hj => ?_⟩
    · rw [e, map_smul, Prod.smul_fst, h.1, smul_zero]
    · rw [e, map_smul, Prod.smul_snd, Pi.smul_apply, h.2 j hj, smul_zero]
  have hsingle : ∀ (l : Fin d) (c : AE F E), P (Pi.single l c) := by
    intro l c
    induction c using TensorProduct.induction_on with
    | zero => rw [Pi.single_zero]; exact hP0
    | add b c hb hc => rw [Pi.single_add]; exact hPadd _ _ hb hc
    | tmul b e =>
      have e1 : (Pi.single l (b ⊗ₜ[F] e) : Fin d → AE F E) = b • incV F (Pi.single l e) := by
        funext k
        by_cases hk : k = l
        · subst hk
          simp [incV, inclR, TensorProduct.smul_tmul']
        · simp [incV, hk]
      rw [e1]
      exact hPsmul _ _ (hrat _)
  intro z
  have hz : P z := by
    rw [← Finset.univ_sum_single z]
    exact Finset.sum_induction _ P hPadd hP0 fun l _ => hsingle l _
  exact ⟨_, hz.2, Prod.ext hz.1 rfl⟩
