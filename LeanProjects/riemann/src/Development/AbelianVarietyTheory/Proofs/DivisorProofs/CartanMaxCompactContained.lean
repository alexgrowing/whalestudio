import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevSplitOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOfSkewHermitianTwist
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.SqIntMaxCptGen

open GlobalTheory.ThK.SqIntMaxCpt

theorem exists_isMaxCpt_le_kInf_of_cartan : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n), (∀ i j, σ (Y.J j i) = -Y.J i j) →
      (∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) → ∀ (c : E) (hc : c ≠ 0), σ c = -c →
      ∃ K, IsMaxCpt σ (c • Y.J.map σ) K ∧ ∀ x ∈ K, (toGAd hσ Y.J hc).symm x ∈ KInf σ Y B.emb := by
  intro F E _ _ _ _ _ σ hσ B hB n W hskew hcartan c hc hσc
  have h := hB.cm
  have hcj : ∀ (τ : E →+* ℂ) x, star (τ x) = τ (σ x) := fun τ x => (h.2.2.2 τ x).symm
  have key : ∀ w : InfinitePlace F, ∃ (ε : Fin n → Bool) (Q : GL (Fin n) ℂ),
      Q.1ᴴ * (c • W.J.map σ).map (B.emb w).1 * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * (c • W.J.map σ).map (B.emb w).1 * k = (c • W.J.map σ).map (B.emb w).1 →
        ((Q⁻¹).1 * k * Q.1)ᴴ * ((Q⁻¹).1 * k * Q.1) = 1 → Commute k (W.θ w) := fun w => by
    have hre : ((B.emb w).1 c).re = 0 := by
      have := congrArg Complex.re (hcj (B.emb w).1 c)
      rw [hσc, map_neg] at this
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
      linarith
    have him : ((B.emb w).1 c).im ≠ 0 := fun e =>
      (map_ne_zero (B.emb w).1).2 hc (Complex.ext hre e)
    refine exists_frame (s := -((B.emb w).1 c).im) ?_ (hcartan w) (neg_ne_zero.2 him) ?_
    · ext i j
      simp [hcj, hskew]
    · ext i j
      have e : (B.emb w).1 c = ((B.emb w).1 c).im * Complex.I := by
        conv_lhs => rw [← Complex.re_add_im ((B.emb w).1 c), hre]
        simp
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, star_mul', hcj]
      conv_lhs => rw [e]
      simp [mul_assoc]
  choose ε Q hQ hk using key
  let e := fun w : InfinitePlace F => RingEquiv.ofBijective _ (infEmb_bijective h (B.emb w))
  let b := fun w : InfinitePlace F => Formalism.UG.bc (e w).symm.toRingHom (Q w)
  have h1 : ∀ w, (b w).1.map (infEmb (B.emb w)) = (Q w).1 := fun w => Matrix.ext fun i j => (e w).apply_symm_apply _
  have h1' : ∀ w, ((b w)⁻¹).1.map (infEmb (B.emb w)) = ((Q w)⁻¹).1 := fun w =>
    Matrix.ext fun i j => (e w).apply_symm_apply _
  have h2 : ∀ w, (JR w.Completion (c • W.J.map σ)).map (infEmb (B.emb w)) = (c • W.J.map σ).map (B.emb w).1 := fun w => by
    ext r s; simp [JR, inclR]
  refine ⟨majCpt σ _ b, isMaxCpt_majCpt h fun w => ⟨ε w, Matrix.map_injective (e w).injective ?_⟩, fun k hkK => ?_⟩
  · change Matrix.map _ (infEmb (B.emb w)) = Matrix.map _ (infEmb (B.emb w))
    rw [Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR h, h1, h2, hQ, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    split_ifs <;> simp
  obtain ⟨hk1, hk2⟩ := mem_majCpt.1 hkK
  have hm : mat ((toGAd hσ W.J hc).symm k) = (matHom _ σ _ k).1 := rfl
  refine ⟨fun u hu => Matrix.ext fun i j => at_evI_of_compFin (fun v => ?_) u hu, fun w => ?_⟩
  · have := congrArg (fun g => (matHom _ σ _ g).1 i j) (mem_infPts_iff_forall.1 hk1 v)
    rw [hm, Matrix.sub_apply, map_sub, sub_eq_zero]
    refine this.trans ?_
    simp [Matrix.one_apply, apply_ite (compFin F E v)]
  · have e1 : (mat ((toGAd hσ W.J hc).symm k)).map (piInf (B.emb w)) =
        (matHom _ σ _ (projArch σ _ w k)).1.map (infEmb (B.emb w)) := rfl
    rw [e1]
    refine hk w _ ?_ ?_
    · have : Formalism.UG.cT (sigR _ σ) (matHom _ σ _ (projArch σ _ w k)).1 * JR w.Completion (c • W.J.map σ) *
        (matHom _ σ _ (projArch σ _ w k)).1 = JR w.Completion (c • W.J.map σ) := (projArch σ _ w k).2
      have := congrArg (fun A => A.map (infEmb (B.emb w))) this
      simpa only [Matrix.map_mul, Frames.map_cT_sigR h, h2] using this
    · have : Formalism.UG.cT (sigR _ σ) ((b w)⁻¹ * matHom _ σ _ (projArch σ _ w k) * b w).1 * 1 *
        ((b w)⁻¹ * matHom _ σ _ (projArch σ _ w k) * b w).1 = 1 := mem_stabArch.1 (hk2 w)
      have := congrArg (fun A => A.map (infEmb (B.emb w))) this
      simpa only [Matrix.mul_one, Matrix.map_mul, Frames.map_cT_sigR h, Units.val_mul, h1, h1',
        Matrix.map_one _ (map_zero _) (map_one _)] using this

end GlobalTheory.ThK.SqIntMaxCptGen
