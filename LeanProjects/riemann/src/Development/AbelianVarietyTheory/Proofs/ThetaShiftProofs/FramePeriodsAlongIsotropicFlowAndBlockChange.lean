import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.EmbeddingHermitianPairs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MmatMulVec

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.PerFlow

open Matrix
open scoped ComplexConjugate ComplexOrder

section aux

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma perFr_mem (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) :
    perFr X x v τ.1 i =
      if hi : X.p0 + i < r then ((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) ⟨X.p0 + i, hi⟩ else 0 := by
  unfold perFr
  rw [dif_pos τ.2]

lemma perFr_conj (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) (j : Fin r)
    (hj : (j : ℕ) = X.p0 - 1 - i) :
    perFr X x v (conjEmb τ.1) i = hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
  have hcc : conjEmb (conjEmb τ.1) = τ.1 := by
    ext a; simp [conjEmb]
  have h1 : conjEmb τ.1 ∉ X.Ψ := (X.cmType τ.1).1 τ.2
  have h2 : conjEmb (conjEmb τ.1) ∈ X.Ψ := by rw [hcc]; exact τ.2
  have h3 : X.p0 - 1 - i < r := hj ▸ j.2
  unfold perFr
  rw [dif_neg h1, dif_pos h2, dif_pos h3]
  have key : ∀ (σ : E →+* ℂ) (hσ : σ ∈ X.Ψ), σ = τ.1 →
      hermC σ X.Gm (FD.col (mat x ⟨σ, hσ⟩) ⟨X.p0 - 1 - i, h3⟩) (Data.emb σ v) =
        hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
    intro σ hσ h
    subst h
    have : (⟨X.p0 - 1 - i, h3⟩ : Fin r) = j := Fin.ext hj.symm
    rw [this]
  exact key _ h2 hcc

lemma flowMat_mulVec (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (u : Fin r → ℂ) :
    X.flowMat ξ τ s *ᵥ u =
      u + (s * τ.1 X.κ0 * hermC τ.1 X.Gm u (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
  rw [EmbeddingHermitianPairs.flowMat_eq, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    EmbeddingHermitianPairs.wv_dot, X.tau_kappa0]
  funext a
  simp
  ring

lemma flow_mem {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (s : X.Ψ → ℂ) (x : Frame X.Ψ r)
    (v : Fin r → E) (τ : X.Ψ) (i : ℕ) :
    perFr X (X.flow ξ s x) v τ.1 i =
      perFr X x v τ.1 i - s τ * τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ τ.1 i := by
  simp only [perFr_mem]
  split_ifs with hi
  · have hm : mat (X.flow ξ s x) τ = X.flowMat ξ τ (s τ) * mat x τ := rfl
    have hinv : (X.flowMat ξ τ (s τ))⁻¹ = X.flowMat ξ τ (-s τ) := by
      apply inv_eq_right_inv
      rw [EmbeddingHermitianPairs.flowMat_mul X hξ, add_neg_cancel, EmbeddingHermitianPairs.flowMat_zero]
    have he : hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 ξ) = τ.1 (herm X.Gm v ξ) :=
      EmbeddingHermitianPairs.hermC_emb _ _ _ _
    rw [hm, Matrix.mul_inv_rev, hinv, ← mulVec_mulVec, flowMat_mulVec, mulVec_add, mulVec_smul, he,
      map_mul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simp

lemma flow_conj (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r)
    (v : Fin r → E) (τ : X.Ψ) (i : ℕ) (hi : i < X.p0) :
    perFr X (X.flow ξ s x) v (conjEmb τ.1) i =
      perFr X x v (conjEmb τ.1) i -
        s τ * conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ (conjEmb τ.1) i := by
  have hlt : X.p0 - 1 - i < r := by have := X.p0_le; omega
  simp only [perFr_conj X _ _ τ i ⟨_, hlt⟩ rfl]
  have hc : FD.col (mat (X.flow ξ s x) τ) ⟨_, hlt⟩ =
      X.flowMat ξ τ (s τ) *ᵥ FD.col (mat x τ) ⟨_, hlt⟩ := rfl
  have he : hermC τ.1 X.Gm (Data.emb τ.1 v) (Data.emb τ.1 ξ) = τ.1 (herm X.Gm v ξ) :=
    EmbeddingHermitianPairs.hermC_emb _ _ _ _
  have he' : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 v) = conj (τ.1 (herm X.Gm v ξ)) := by
    rw [← he, hermC_conj τ.1 X.Gm_herm]
  have hk : conj (τ.1 X.κ0) = -τ.1 X.κ0 := by
    rw [← EmbeddingHermitianPairs.emb_cc', X.cc_kappa0, map_neg]
  have h2 : conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) = -τ.1 X.κ0 * conj (τ.1 (herm X.Gm v ξ)) := by
    rw [← hk, ← map_mul, ← map_mul]; rfl
  rw [hc, flowMat_mulVec, hermC_add_left, hermC_smul_left, he', h2]
  ring

def blockEquiv : Fin X.p0 ⊕ Fin (r - X.p0) ≃ Fin r :=
  finSumFinEquiv.trans (finCongr (by have := X.p0_le; omega))

lemma blockEquiv_inl (a : Fin X.p0) : blockEquiv X (.inl a) = Fin.castLE X.p0_le a := by
  apply Fin.ext; simp [blockEquiv]

lemma blockEquiv_inr (a : Fin (r - X.p0)) : ((blockEquiv X (.inr a) : Fin r) : ℕ) = X.p0 + a := by
  simp [blockEquiv]

def blk (P : Matrix (Fin X.p0) (Fin X.p0) ℂ) (Q : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.reindex (blockEquiv X) (blockEquiv X) (fromBlocks P 0 0 Q)

lemma blk_mul (P P' : Matrix (Fin X.p0) (Fin X.p0) ℂ)
    (Q Q' : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) :
    blk X P Q * blk X P' Q' = blk X (P * P') (Q * Q') := by
  simp [blk, fromBlocks_multiply]

lemma blk_one : blk X 1 1 = 1 := by
  simp [blk]

lemma blk_mulVec_inr (P : Matrix (Fin X.p0) (Fin X.p0) ℂ)
    (Q : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (w : Fin r → ℂ) (i : Fin (r - X.p0)) :
    (blk X P Q *ᵥ w) (blockEquiv X (.inr i)) = ∑ k, Q i k * w (blockEquiv X (.inr k)) := by
  simp only [mulVec, dotProduct]
  rw [← (blockEquiv X).sum_comp]
  simp [blk, Fintype.sum_sum_type]

lemma col_mul_blk (M : Matrix (Fin r) (Fin r) ℂ) (P : Matrix (Fin X.p0) (Fin X.p0) ℂ)
    (Q : Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (j : Fin X.p0) :
    FD.col (M * blk X P Q) (Fin.castLE X.p0_le j) =
      ∑ k, P k j • FD.col M (Fin.castLE X.p0_le k) := by
  funext a
  simp only [FD.col, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    ← blockEquiv_inl]
  rw [← (blockEquiv X).sum_comp]
  simp [blk, Fintype.sum_sum_type, mul_comm]

lemma block_change (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (A : X.Ψ → Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ)
    (B : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ) (hA : ∀ τ, (A τ).det ≠ 0) (hB : ∀ τ, (B τ).det ≠ 0) :
    ∃ x' ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ),
      (∀ i : Fin (r - X.p0), perFr X x' v τ.1 i = ∑ k, A τ i k * perFr X x v τ.1 k) ∧
      ∀ i : Fin X.p0, perFr X x' v (conjEmb τ.1) i = ∑ k, B τ i k * perFr X x v (conjEmb τ.1) k := by
  let P : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ :=
    fun τ => ((B τ).submatrix Fin.revPerm Fin.revPerm)ᵀ
  have hP : ∀ τ, (P τ).det ≠ 0 := fun τ => by
    simp only [P, det_transpose, det_submatrix_equiv_self]; exact hB τ
  let x' : Frame X.Ψ r := fun τ => (mat x τ * blk X (P τ) (A τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
  have hm : ∀ τ, mat x' τ = mat x τ * blk X (P τ) (A τ)⁻¹ := fun τ => rfl
  have hone : ∀ τ, blk X (P τ) (A τ)⁻¹ * blk X (P τ)⁻¹ (A τ) = 1 := fun τ => by
    rw [blk_mul, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hP τ)),
      nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hA τ)), blk_one]
  have hcol : ∀ τ j, X.colP x' τ j = ∑ k, P τ k j • X.colP x τ k := fun τ j => by
    unfold Data.colP
    rw [hm, col_mul_blk]
  refine ⟨x', AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨?_, ?_⟩, fun v τ => ⟨fun i => ?_, fun i => ?_⟩⟩
  · rw [hm, det_mul]
    refine mul_ne_zero (hx τ).1 fun h0 => ?_
    have := congrArg det (hone τ)
    rw [det_mul, h0] at this
    simp at this
  · have hg : X.gramPos x' τ = (P τ)ᵀ * X.gramPos x τ * ((P τ)ᵀ)ᴴ := by
      ext a b
      rw [Data.gramPos_apply, hcol, hcol, hermC_sum_right]
      simp only [Matrix.mul_apply, hermC_smul_right, hermC_sum_left, hermC_smul_left,
        conjTranspose_apply, transpose_apply, Data.gramPos_apply, Complex.star_def]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hg]
    refine (X.gramPos_posDef hx τ).mul_mul_conjTranspose_same ?_
    exact Matrix.vecMul_injective_iff_isUnit.2
      ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (by rw [det_transpose]; exact hP τ)))
  · have hlt : ∀ k : Fin (r - X.p0), X.p0 + k < r := fun k => by have := k.2; omega
    have hidx : ∀ k : Fin (r - X.p0), (⟨X.p0 + k, hlt k⟩ : Fin r) = blockEquiv X (.inr k) :=
      fun k => Fin.ext (blockEquiv_inr X k).symm
    simp only [perFr_mem, dif_pos (hlt _), hidx]
    rw [hm, Matrix.mul_inv_rev, inv_eq_right_inv (hone τ), ← mulVec_mulVec, blk_mulVec_inr]
  · have hr : ∀ (y : Frame X.Ψ r) (k : Fin X.p0), perFr X y v (conjEmb τ.1) k =
        hermC τ.1 X.Gm (X.colP y τ k.rev) (Data.emb τ.1 v) := fun y k =>
      perFr_conj X y v τ k (Fin.castLE X.p0_le k.rev) (by simp [Fin.val_rev]; omega)
    simp only [hr]
    rw [hcol, hermC_sum_left, ← Equiv.sum_comp Fin.revPerm]
    simp [P, hermC_smul_left]

end aux

theorem perFr_flow_block : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ ξ, herm X.Gm ξ ξ = 0 → ∀ (s : X.Ψ → ℂ), ∀ x ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ) (i : ℕ), perFr X (X.flow ξ s x) v τ.1 i = perFr X x v τ.1 i - s τ * τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ τ.1 i ∧ (i < X.p0 → perFr X (X.flow ξ s x) v (conjEmb τ.1) i = perFr X x v (conjEmb τ.1) i - s τ * conjEmb τ.1 (X.κ0 * herm X.Gm v ξ) * perFr X x ξ (conjEmb τ.1) i)) ∧ ∀ x ∈ X.dom, ∀ (A : X.Ψ → Matrix (Fin (r - X.p0)) (Fin (r - X.p0)) ℂ) (B : X.Ψ → Matrix (Fin X.p0) (Fin X.p0) ℂ), (∀ τ, (A τ).det ≠ 0) → (∀ τ, (B τ).det ≠ 0) → ∃ x' ∈ X.dom, ∀ (v : Fin r → E) (τ : X.Ψ), (∀ i : Fin (r - X.p0), perFr X x' v τ.1 i = ∑ k, A τ i k * perFr X x v τ.1 k) ∧ ∀ i : Fin X.p0, perFr X x' v (conjEmb τ.1) i = ∑ k, B τ i k * perFr X x v (conjEmb τ.1) k := by
  intro E _ _ _ r X
  exact ⟨fun ξ hξ s x _ v τ i => ⟨flow_mem X hξ s x v τ i, flow_conj X ξ s x v τ i⟩,
    fun x hx A B hA hB => block_change X x hx A B hA hB⟩

end GlobalTheory.PerFlow
