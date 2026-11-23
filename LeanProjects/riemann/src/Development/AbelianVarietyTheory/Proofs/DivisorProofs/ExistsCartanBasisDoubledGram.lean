import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasIwasawaOfSmul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.SkewDblIwasawa

noncomputable section
namespace GlobalTheory.SkewDblIwasawa

theorem exists_imaginary {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hw : w.IsComplex := hcm.2.1.isComplex w
  have hτ : ¬ ComplexEmbedding.IsReal w.embedding := InfinitePlace.isComplex_iff.1 hw
  have hx : ∃ x : E, σ x ≠ x := by
    by_contra h
    push Not at h
    apply hτ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := hcm.2.2.2 w.embedding x
    rw [h x] at this
    exact this.symm
  obtain ⟨x, hx⟩ := hx
  have hσσ : σ (σ x) = x := w.embedding.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  exact ⟨x - σ x, sub_ne_zero.2 hx.symm, by rw [map_sub, hσσ, neg_sub]⟩

theorem isCartan_smul_pos {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) {t : ℝ} (ht : 0 < t) :
    IsCartan ((t : ℂ) • M) θ := by
  refine ⟨h.1, ?_, fun x hx => ?_⟩
  · rw [Matrix.mul_smul, Matrix.smul_mul, h.2.1]
  · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_pos ht (h.2.2 x hx)

theorem isCartan_neg {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : IsCartan (-M) (-θ) := by
  refine ⟨by rw [neg_mul_neg, h.1], ?_, fun x hx => ?_⟩
  · rw [Matrix.transpose_neg, Matrix.map_neg _ (fun a => star_neg a), neg_mul_neg, Matrix.mul_neg, h.2.1]
  · rw [Matrix.neg_mulVec, Matrix.neg_mulVec, neg_dotProduct, dotProduct_neg, neg_neg]
    exact h.2.2 x hx

theorem blkMat_neg_neg {n : ℕ} (x y : Matrix (Fin n) (Fin n) ℂ) :
    blkMat finSumFinEquiv (-x) (-y) = -blkMat finSumFinEquiv x y := by
  ext i j
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp only [blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.neg_apply, neg_zero]

theorem stabArch_eq_comap {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {m : ℕ}
    (Q : Matrix (Fin m) (Fin m) E) (w : InfinitePlace F) (b : GL (Fin m) (w.Completion ⊗[F] E)) :
    stabArch σ Q w b = ((Formalism.UG.UJ (sigR w.Completion σ) 1).comap
      (MulEquiv.toMonoidHom (MulAut.conj b⁻¹))).comap (GlobalTheory.AdelicU.matHom w.Completion σ Q) := by
  rw [Subgroup.comap_comap, stabArch]

theorem hasIwasawa_stabArch_of_smul {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (c : E) (hc : c ≠ 0) (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (w : InfinitePlace F)
    (b : GL (Fin (n + n)) (w.Completion ⊗[F] E)) (h : HasIwasawa σ (c • Q) (stabArch σ (c • Q) w b)) :
    HasIwasawa σ Q (stabArch σ Q w b) := by
  rw [stabArch_eq_comap] at h ⊢
  exact hasIwasawa_of_smul σ c hc Q _ h

theorem mem_stabArch_congr {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {m : ℕ}
    {Q Q' : Matrix (Fin m) (Fin m) E} (w : InfinitePlace F) (b : GL (Fin m) (w.Completion ⊗[F] E))
    {k : GArch σ Q w} {k' : GArch σ Q' w}
    (e : GlobalTheory.AdelicU.matHom w.Completion σ Q k = GlobalTheory.AdelicU.matHom w.Completion σ Q' k') :
    k ∈ stabArch σ Q w b ↔ k' ∈ stabArch σ Q' w b := by
  rw [stabArch_eq_comap, stabArch_eq_comap, Subgroup.mem_comap, Subgroup.mem_comap (f := GlobalTheory.AdelicU.matHom _ _ Q'), e]

theorem arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (B : Base F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (θ : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ),
    (∀ i j, σ (J j i) = -J i j) → (∀ w, IsCartan (Complex.I • J.map (B.emb w).1) (θ w)) →
    ∀ {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}, Q = dblGram finSumFinEquiv Jᵀ →
    ∃ a : GL (Fin n) (AF F ⊗[F] E), ∀ w : InfinitePlace F,
      HasIwasawa σ Q (KArch σ Q w (Formalism.UG.bc (compInf F E w) a)) ∧
      ∀ k : GArch σ Q w, k ∈ KArch σ Q w (Formalism.UG.bc (compInf F E w) a) ↔
        Commute ((GlobalTheory.AdelicU.matHom w.Completion σ Q k).1.map (infEmb (B.emb w))) (blkMat finSumFinEquiv (θ w) (-θ w)) := by
  intro F E _ _ _ _ _ σ hcm B n J θ hJ hθ Q hQ
  obtain ⟨δ, hδ0, hδ⟩ := exists_imaginary hcm
  have ht : ∀ w : InfinitePlace F, ∃ t : ℝ, t ≠ 0 ∧ (B.emb w).1 δ = (t : ℂ) * Complex.I := fun w => by
    have h1 := hcm.2.2.2 (B.emb w).1 δ
    rw [hδ, map_neg] at h1
    have h2 : ((B.emb w).1 δ).re = 0 := by
      have := congrArg Complex.re h1
      simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at this
      linarith
    have h3 : (B.emb w).1 δ = (((B.emb w).1 δ).im : ℂ) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im ((B.emb w).1 δ), h2]
      simp
    refine ⟨_, fun h0 => ?_, h3⟩
    rw [h0] at h3
    exact hδ0 ((B.emb w).1.injective (by simpa using h3))
  choose t ht0 ht using ht
  have hJ' : ∀ i j, σ ((δ • J) j i) = (δ • J) i j := fun i j => by
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, hδ, hJ, neg_mul_neg]
  have hmap : ∀ w, (δ • J).map (B.emb w).1 = (t w : ℂ) • (Complex.I • J.map (B.emb w).1) := fun w => by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, ht, mul_assoc]
  have hθ' : ∀ w, IsCartan ((δ • J).map (B.emb w).1) (if 0 < t w then θ w else -θ w) := fun w => by
    rw [hmap]
    split_ifs with h
    · exact isCartan_smul_pos (hθ w) h
    · have h' : 0 < -t w := neg_pos.2 (lt_of_le_of_ne (not_lt.1 h) (ht0 w))
      have := isCartan_smul_pos (isCartan_neg (hθ w)) h'
      rwa [Complex.ofReal_neg, neg_smul, smul_neg, neg_neg] at this
  have hQ' : δ • Q = dblGram finSumFinEquiv (δ • J)ᵀ := by
    rw [Matrix.transpose_smul, dblGram_smul, hQ]
  obtain ⟨a, hmaj, harch⟩ := GlobalTheory.DblIwasawa.arch hcm B (δ • J) (fun w => if 0 < t w then θ w else -θ w) hJ' hθ' hQ'
  refine ⟨a, fun w => ⟨?_, fun k => ?_⟩⟩
  · obtain ⟨ε, hε⟩ := hmaj w
    exact hasIwasawa_stabArch_of_smul σ δ hδ0 Q w _ (GlobalTheory.Core.Rk.IwArch.hasIwasawa_KArch hcm hQ' w _ ε hε)
  · obtain ⟨k', e⟩ : ∃ k' : GArch σ (δ • Q) w,
        GlobalTheory.AdelicU.matHom w.Completion σ Q k = GlobalTheory.AdelicU.matHom w.Completion σ (δ • Q) k' :=
      ⟨⟨k.1, (mem_hR_smul_iff _ σ δ hδ0 Q k.1).2 k.2⟩, rfl⟩
    refine (mem_stabArch_congr σ w _ e).trans ((harch w k').trans ?_)
    rw [← e]
    split_ifs with h0
    · rfl
    · rw [blkMat_neg_neg, Commute.neg_right_iff]

end GlobalTheory.SkewDblIwasawa

end
