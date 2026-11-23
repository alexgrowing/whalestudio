import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIncMLagP

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.SiegelConv

theorem lagrangian_injective_diagonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      Function.Injective (GlobalTheory.SiegelConv.lagP n H'.ι H'.x) ∧
      ∀ y : Fin n → E, Matrix.vecMulVec H'.y (Sum.elim y y) ∈ LinearMap.range (GlobalTheory.SiegelConv.lagP n H'.ι H'.x) → y = 0 := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hp₁
  have hσσ : ∀ x : E, σ (σ x) = x := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro x; apply τ.injective; rw [hp.base.cm.2.2.2 τ, hp.base.cm.2.2.2 τ, star_star]
  have fadd : ∀ a b w : Fin d → E, form σ W.J (a + b) w = form σ W.J a w + form σ W.J b w := by
    intro a b w; simp only [form, add_dotProduct]
  have fsmul : ∀ (c : E) (a w : Fin d → E), form σ W.J (c • a) w = c * form σ W.J a w := by
    intro c a w; simp only [form, smul_dotProduct, smul_eq_mul]
  have fswap : ∀ a b : Fin d → E, form σ W.J b a = -σ (form σ W.J a b) := by
    intro a b
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσσ, hp.skew.skew, Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hcol : ∀ (p : Matrix (Fin d₁) (Fin n) E × (Fin n ⊕ Fin n → E)) (j : Fin n ⊕ Fin n), ∃ u : Fin d₁ → E,
      (fun i => lagP n H'.ι H'.x p i j) = H'.ι *ᵥ u + p.2 j • H'.x := by
    intro p j
    refine ⟨fun k => (p.1 * Matrix.transpose (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E)) k j, ?_⟩
    funext i
    simp [lagP, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, mul_comm]
  have hinl : ∀ (p : Matrix (Fin d₁) (Fin n) E × (Fin n ⊕ Fin n → E)) (k : Fin n) (i : Fin d),
      lagP n H'.ι H'.x p i (Sum.inl k) = (H'.ι *ᵥ fun m => p.1 m k) i + H'.x i * p.2 (Sum.inl k) := by
    intro p k i
    simp [lagP, diagCols, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Matrix.one_apply]
  have hdet : W₁.J.det ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    obtain ⟨hrs, A, hAeq⟩ := hp₁.skew.sig w
    intro h0
    have hMc : (Complex.I • W₁.J.map (B.emb w).1).det = 0 := by
      rw [Matrix.det_smul, show (W₁.J.map (B.emb w).1).det = (B.emb w).1 W₁.J.det from
        (RingHom.map_det (B.emb w).1 W₁.J).symm, h0, map_zero, mul_zero]
    let e : Fin r₁ ⊕ Fin s₁ ≃ Fin d₁ := finSumFinEquiv.trans (finCongr hrs)
    let A' : Matrix (Fin d₁) (Fin d₁) ℂ := A.submatrix id e.symm
    have hA' : A'ᵀ * (Complex.I • W₁.J.map (B.emb w).1) * A'.map star =
        (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r₁ ⊕ Fin s₁) (Fin r₁ ⊕ Fin s₁) ℂ).submatrix e.symm e.symm := by
      rw [← hAeq]; ext i j; rfl
    have hd := congrArg Matrix.det hA'
    rw [Matrix.det_mul, Matrix.det_mul, hMc, mul_zero, zero_mul, Matrix.det_submatrix_equiv_self,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg, Matrix.det_one] at hd
    simp only [one_mul, mul_one, Fintype.card_fin] at hd
    exact pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0) hd.symm
  have hιinj : ∀ u : Fin d₁ → E, H'.ι *ᵥ u = 0 → u = 0 := by
    intro u hu
    apply Matrix.eq_zero_of_vecMul_eq_zero hdet
    rw [← hA.gram, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hu,
      Matrix.zero_vecMul, Matrix.zero_vecMul]
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨z, y⟩ hp0
    have hy : y = 0 := by
      funext j
      obtain ⟨u, hu⟩ := hcol (z, y) j
      have h0 : (fun i => lagP n H'.ι H'.x (z, y) i j) = 0 := by funext i; simp [hp0]
      have := congrArg (fun v => form σ W.J v H'.y) (hu.symm.trans h0)
      simp only [fadd, fsmul, (hA.orth u).2, hA.xy] at this
      simpa [form] using this
    subst hy
    have hz : z = 0 := by
      ext m k
      have h1 : H'.ι *ᵥ (fun m => z m k) = 0 := by
        funext i
        have := congrFun (congrFun hp0 i) (Sum.inl k)
        rw [hinl] at this
        simpa using this
      exact congrFun (hιinj _ h1) m
    simp [hz]
  · rintro y ⟨p, hp2⟩
    funext k
    obtain ⟨u, hu⟩ := hcol p (Sum.inl k)
    have hc : (fun i => lagP n H'.ι H'.x p i (Sum.inl k)) = y k • H'.y := by
      rw [hp2]; funext i; simp [Matrix.vecMulVec_apply, mul_comm]
    have := congrArg (fun v => form σ W.J v H'.x) (hu.symm.trans hc)
    simp only [fadd, fsmul, (hA.orth u).1, hA.xx] at this
    rw [fswap H'.x H'.y, hA.xy, map_one] at this
    simpa using this

end GlobalTheory.SiegelConv

end
