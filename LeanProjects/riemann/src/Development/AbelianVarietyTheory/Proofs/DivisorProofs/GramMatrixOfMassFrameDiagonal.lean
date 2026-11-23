import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.OrthFrames

open Matrix
open scoped ComplexConjugate

theorem exists_perm_initial {r : ℕ} (P : Fin r → Prop) [DecidablePred P] :
    ∃ (σ : Equiv.Perm (Fin r)) (p : ℕ), ∀ a, P (σ a) ↔ (a : ℕ) < p := by
  classical
  let f : Fin r → ℕ := fun a => if P a then 0 else 1
  let σ := Tuple.sort f
  have hm : Monotone (f ∘ σ) := Tuple.monotone_sort f
  let S : Finset (Fin r) := Finset.univ.filter fun a => f (σ a) = 0
  refine ⟨σ, S.card, fun a => ?_⟩
  have hP : P (σ a) ↔ f (σ a) = 0 := by
    simp only [f]; split_ifs with h <;> simp [h]
  rw [hP]
  constructor
  · intro h0
    have hsub : Finset.Iic a ⊆ S := by
      intro b hb
      rw [Finset.mem_Iic] at hb
      have := hm hb
      simp only [Function.comp_apply] at this
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hlt
    by_contra h0
    have hsub : S ⊆ Finset.Iio a := by
      intro b hb
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [Finset.mem_Iio]
      by_contra hba
      have := hm (not_lt.1 hba)
      simp only [Function.comp_apply] at this
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

theorem exists_sgn_frame {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) (hN : N.IsHermitian) (hd : N.det ≠ 0) :
    ∃ (X : Matrix (Fin r) (Fin r) ℂ) (p : ℕ),
      Xᴴ * N * X = diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  classical
  set U : Matrix (Fin r) (Fin r) ℂ := (hN.eigenvectorUnitary : Matrix (Fin r) (Fin r) ℂ) with hUdef
  set lam := hN.eigenvalues with hlam
  have hU : Uᴴ * N * U = diagonal fun k => ((lam k : ℝ) : ℂ) := by
    have h := hN.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at h
    simp only [hUdef, Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose] at h ⊢
    rw [h]; rfl
  have hne : ∀ k, lam k ≠ 0 := by
    intro k hk
    apply hd
    rw [hN.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [← hlam, hk])
  obtain ⟨σ, p, hσ⟩ := exists_perm_initial fun k => 0 < lam k
  let s : Fin r → ℝ := fun a => (Real.sqrt |lam (σ a)|)⁻¹
  let Y : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun k a => if k = σ a then ((s a : ℝ) : ℂ) else 0
  refine ⟨U * Y, p, ?_⟩
  have e1 : (U * Y)ᴴ * N * (U * Y) = Yᴴ * (Uᴴ * N * U) * Y := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  rw [e1, hU]
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, conjTranspose_apply, Y, Matrix.of_apply, diagonal_apply]
  rw [Finset.sum_eq_single (σ a)]
  · by_cases hab : a = b
    · subst hab
      simp only [if_true, Complex.star_def, Complex.conj_ofReal]
      have hs : s a * lam (σ a) * s a = ReciprocityTheory.ChartRestriction.G.FD.sgn p a := by
        have habs : 0 < |lam (σ a)| := abs_pos.2 (hne _)
        have hsq : s a * s a = |lam (σ a)|⁻¹ := by
          simp only [s]
          rw [← mul_inv, Real.mul_self_sqrt habs.le]
        unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
        by_cases hpos : 0 < lam (σ a)
        · rw [if_pos ((hσ a).1 hpos)]
          calc s a * lam (σ a) * s a = (s a * s a) * lam (σ a) := by ring
            _ = 1 := by rw [hsq, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
        · have hneg : lam (σ a) < 0 := lt_of_le_of_ne (not_lt.1 hpos) (hne _)
          rw [if_neg (fun h => hpos ((hσ a).2 h))]
          calc s a * lam (σ a) * s a = (s a * s a) * lam (σ a) := by ring
            _ = -1 := by
              rw [hsq, abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hneg.ne]
      rw [← hs]; push_cast; ring
    · have : σ a ≠ σ b := fun h => hab (σ.injective h)
      simp [this, hab]
  · intro k _ hk
    simp [hk]
  · simp

theorem gram_eq_transpose {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (τ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = (xᴴ * (G.map τ)ᵀ * x)ᵀ := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul,
    Complex.star_def]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.OrthFrames

namespace GlobalTheory.OrthFrames

open Matrix

theorem hspace_gram_det_ne {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E) :
    V.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hm⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have h0 : V.frame.equivFun.symm v = 0 := by
    refine V.nondeg.2 _ fun x => ?_
    have : V.hT.flip (V.frame.equivFun.symm v) = 0 := by
      refine V.frame.ext fun i => ?_
      have := congrFun hm i
      simp only [Matrix.mulVec, dotProduct, HSpace.gram, Pi.zero_apply] at this
      simp only [LinearMap.flip_apply, Module.Basis.equivFun_symm_apply, map_sum, map_smul, smul_eq_mul,
        LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.smul_apply]
      refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) this
      exact mul_comm (v j) _
    exact congrArg (fun f => f x) this
  exact (LinearEquiv.map_eq_zero_iff _).1 h0

theorem gm_isHermitian (D : D7) (i : Fin D.R.m) (τ : D.host.E →+* ℂ) :
    (((GlobalTheory.MassLink.gm D i).map τ)ᵀ).IsHermitian := by
  haveI hcm : IsCMField D.host.E := D.host.isCMField_hostE
  refine Matrix.IsHermitian.ext fun a b => ?_
  simp only [Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.MassLink.gm, Matrix.submatrix_apply, HSpace.gram]
  rw [← (Wc D i).herm.eq ((Wc D i).frame (Fin.cast (rank_Wc i).symm b))]
  exact (IsCMField.complexEmbedding_complexConj D.host.E τ _).symm

theorem gm_det_ne (D : D7) (i : Fin D.R.m) (τ : D.host.E →+* ℂ) :
    (((GlobalTheory.MassLink.gm D i).map τ)ᵀ).det ≠ 0 := by
  rw [Matrix.det_transpose]
  have e := RingHom.map_det τ (GlobalTheory.MassLink.gm D i)
  rw [RingHom.mapMatrix_apply] at e
  rw [← e, map_ne_zero]
  simp only [GlobalTheory.MassLink.gm, Matrix.det_transpose]
  have e2 : (HSpace.gram (Wc D i)).submatrix (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm) =
      (HSpace.gram (Wc D i)).submatrix (finCongr (rank_Wc i).symm) (finCongr (rank_Wc i).symm) := rfl
  rw [e2, Matrix.det_submatrix_equiv_self]
  exact hspace_gram_det_ne _

theorem exists_orth_frames : ∀ (D : D7) (i : Fin D.R.m),
    letI : IsCMField D.host.E := D.host.isCMField_hostE;
    ∃ (x : ReciprocityTheory.ChartRestriction.G.FD.Frame (GlobalTheory.MassLink.psi D) D.R.r) (p0 : GlobalTheory.MassLink.psi D → ℕ),
      ∀ τ : GlobalTheory.MassLink.psi D, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 (GlobalTheory.MassLink.gm D i) (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) =
        Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ) := by
  intro D i
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  have key : ∀ τ : GlobalTheory.MassLink.psi D, ∃ (X : Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (p : ℕ),
      ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 (GlobalTheory.MassLink.gm D i) X =
        Matrix.diagonal fun a : Fin D.R.r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
    intro τ
    obtain ⟨X, p, hX⟩ := exists_sgn_frame _ (gm_isHermitian D i τ.1) (gm_det_ne D i τ.1)
    refine ⟨X, p, ?_⟩
    rw [gram_eq_transpose, hX, Matrix.diagonal_transpose]
  choose X p hX using key
  exact ⟨fun τ => X τ, p, fun τ => hX τ⟩

end GlobalTheory.OrthFrames
