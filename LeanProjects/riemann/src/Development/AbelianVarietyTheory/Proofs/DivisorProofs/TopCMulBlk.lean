import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledModelDarbouxWeilActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledPairEmbeddingBlockDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledPairDarbouxSeesawStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

noncomputable section

namespace GlobalTheory.DblWeilSecond

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem topC_mul_blk {n d : ℕ} (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) (A C : Matrix (Fin d) (Fin d) (AE F E)) :
    topC (u * (blkMat finSumFinEquiv A C)ᵀ) = topC u * Aᵀ := by
  ext r j
  simp only [topC, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, blkMat, id, Function.comp_apply]
  rw [← finSumFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
    zero_add]

theorem botC_mul_blk {n d : ℕ} (u : Matrix (Fin n) (Fin (d + d)) (AE F E)) (A C : Matrix (Fin d) (Fin d) (AE F E)) :
    botC (u * (blkMat finSumFinEquiv A C)ᵀ) = botC u * Cᵀ := by
  ext r j
  simp only [botC, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, blkMat, id, Function.comp_apply]
  rw [← finSumFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero,
    zero_add]

theorem diag_box (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W)
    (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ) (hP : IsPair B M χX χW om r s' r₁ s₁)
    (W₂ : Spc F E (d + d)) (hJ : W₂.J = dblGram finSumFinEquiv W.J)
    (i : UA σ W.J × UA σ W.J →* UA σ W₂.J) (hi : ∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h'))
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)))
    (hrat : ∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
      co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    (hΔ : ∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0)
    (hN : ∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0)
    (om₂ : Rep σ Xs W₂) (hom₂ : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F Xs.J) (incM F W₂.J) co χX 1 om₂)
    (e : (((Fin n × Fin d ⊕ Fin n × Fin d) → AF F) → ℂ) →ₗ[ℂ] ((Fin n × Fin (d + d) → AF F) → ℂ))
    (he1 : Set.BijOn e (schA F (Fin n × Fin d ⊕ Fin n × Fin d) : Set _) (schA F (Fin n × Fin (d + d)) : Set _))
    (he2 : ∀ l ∈ (adeleClass F).adm (Fin n × Fin (d + d)), l ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d ⊕ Fin n × Fin d))
    (he3 : ∀ u, ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e (schr B.ψ (dblE M.co u) Ψ) = co.rho B.ψ u (e Ψ))
    (h : UA σ W.J) (Φ₁ : Fn F n d) (hΦ₁ : Φ₁ ∈ schA F (Fin n × Fin d)) (Φ₂ : Fn F n d)
    (hΦ₂ : Φ₂ ∈ schA F (Fin n × Fin d)) :
    om₂ (1, i (h, h)) (e (boxC Φ₁ Φ₂)) =
      ((χX (Matrix.GeneralLinearGroup.det h.1) : Circle) : ℂ) • e (boxC (om (1, h) Φ₁) (om (1, h) Φ₂)) := by
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨hbox, hmove⟩ := GlobalTheory.T.doubled_model_darboux_weil_action F E σ B hP.base n d Xs W M W₂ hJ co e he1 he2 he3
  have hS1 := GlobalTheory.T.doubled_pair_embedding_block_diagonal F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ i hi co hrat hΔ hN om₂ hom₂
  have hS3 := GlobalTheory.T.doubled_pair_darboux_seesaw F E σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ hJ co hrat hΔ hN e he1 he2 he3
  have hsp2 := hom₂.isUSplitting
  have hsp := hP.weil.isUSplitting
  have hrho : ∀ a, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ a Φ ∈ schA F (Fin n × Fin d) :=
    fun a Φ hΦ => GlobalTheory.HeisSchA.schr_mem_schA B.ψ hstd _ Φ hΦ
  have hom : ∀ Φ ∈ schA F (Fin n × Fin d), om (1, h) Φ ∈ schA F (Fin n × Fin d) :=
    fun Φ hΦ => hsp.pres (1, h) Φ hΦ
  have heS : ∀ Ψ ∈ schA F (Fin n × Fin d ⊕ Fin n × Fin d), e Ψ ∈ schA F (Fin n × Fin (d + d)) :=
    fun Ψ hΨ => he1.mapsTo hΨ

  have ev : ∀ (x : Fin n × Fin (d + d) → AF F) (Φ : (Fin n × Fin (d + d) → AF F) → ℂ),
      co.rho B.ψ (co.e.symm (x, 0)) Φ 0 = Φ x := by
    intro x Φ
    simp [Darboux.rho, schr]

  have hinv : mat (i (h, h))⁻¹ = blkMat finSumFinEquiv (mat h⁻¹) (mat h⁻¹) := by
    rw [← map_inv, Prod.inv_mk, hi]
  have hmul : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (g : UA σ J), mat g * mat g⁻¹ = 1 := by
    intro m J g
    show ((g * g⁻¹ : UA σ J) : GL (Fin m) (AE F E)).1 = 1
    rw [mul_inv_cancel]; rfl
  funext x
  set u := co.e.symm (x, 0) with hu
  set v := u * (mat (i (h, h))⁻¹)ᵀ with hv
  have hvu : actAB (cA σ) ((1 : UA σ Xs.J), i (h, h)) v = u := by
    simp only [actAB, hv]
    show (1 : Matrix (Fin n) (Fin n) (AE F E)) * (u * (mat (i (h, h))⁻¹)ᵀ) * (mat (i (h, h)))ᵀ = u
    rw [Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, hmul, Matrix.transpose_one, Matrix.mul_one]
  have htop : actAB (cA σ) ((1 : UA σ Xs.J), h) (topC v) = topC u := by
    simp only [actAB, hv, hinv, topC_mul_blk]
    show (1 : Matrix (Fin n) (Fin n) (AE F E)) * (topC u * (mat h⁻¹)ᵀ) * (mat h)ᵀ = topC u
    rw [Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, hmul, Matrix.transpose_one, Matrix.mul_one]
  have hbot : actAB (cA σ) ((1 : UA σ Xs.J), h) (botC v) = botC u := by
    simp only [actAB, hv, hinv, botC_mul_blk]
    show (1 : Matrix (Fin n) (Fin n) (AE F E)) * (botC u * (mat h⁻¹)ᵀ) * (mat h)ᵀ = botC u
    rw [Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, hmul, Matrix.transpose_one, Matrix.mul_one]
  have hb := hbox Φ₁ hΦ₁ Φ₂ hΦ₂
  have hb' := hbox _ (hrho (topC v) Φ₁ hΦ₁) _ (hrho (botC v) Φ₂ hΦ₂)
  rw [Pi.smul_apply, smul_eq_mul]
  calc om₂ (1, i (h, h)) (e (boxC Φ₁ Φ₂)) x
      = co.rho B.ψ u (om₂ (1, i (h, h)) (e (boxC Φ₁ Φ₂))) 0 := (ev x _).symm
    _ = om₂ (1, i (h, h)) (co.rho B.ψ v (e (boxC Φ₁ Φ₂))) 0 := by rw [hsp2.impl _ v _ (heS _ hb), hvu]
    _ = om₂ (1, i (h, h)) (e (boxC (M.co.rho B.ψ (topC v) Φ₁) (M.co.rho B.ψ (botC v) Φ₂))) 0 := by
      rw [hmove v Φ₁ hΦ₁ Φ₂ hΦ₂]
    _ = ((χX (Matrix.GeneralLinearGroup.det h.1) : Circle) : ℂ) *
          e (boxC (M.co.rho B.ψ (topC v) Φ₁) (M.co.rho B.ψ (botC v) Φ₂)) 0 := hS1 h _ (heS _ hb')
    _ = ((χX (Matrix.GeneralLinearGroup.det h.1) : Circle) : ℂ) *
          e (boxC (om (1, h) (M.co.rho B.ψ (topC v) Φ₁)) (om (1, h) (M.co.rho B.ψ (botC v) Φ₂))) 0 := by
      rw [hS3 h _ (hrho _ Φ₁ hΦ₁) _ (hrho _ Φ₂ hΦ₂)]
    _ = ((χX (Matrix.GeneralLinearGroup.det h.1) : Circle) : ℂ) *
          e (boxC (M.co.rho B.ψ (topC u) (om (1, h) Φ₁)) (M.co.rho B.ψ (botC u) (om (1, h) Φ₂))) 0 := by
      rw [hsp.impl _ _ _ hΦ₁, htop, hsp.impl _ _ _ hΦ₂, hbot]
    _ = ((χX (Matrix.GeneralLinearGroup.det h.1) : Circle) : ℂ) *
          co.rho B.ψ u (e (boxC (om (1, h) Φ₁) (om (1, h) Φ₂))) 0 := by
      rw [hmove u _ (hom Φ₁ hΦ₁) _ (hom Φ₂ hΦ₂)]
    _ = ((χX (Matrix.GeneralLinearGroup.det h.1) : Circle) : ℂ) * e (boxC (om (1, h) Φ₁) (om (1, h) Φ₂)) x := by
      rw [ev x]

end GlobalTheory.DblWeilSecond
