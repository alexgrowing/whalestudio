import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.RealWeilF

section Unitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_tmul_one_F {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hσ : ∀ x, τ (σ x) = star (τ x))
    {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmbF τ θ) (a : Ainf F) :
    starRingEnd ℂ (θ (a ⊗ₜ[F] (1 : E))) = θ (a ⊗ₜ[F] (1 : E)) := by
  refine DenseRange.induction_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap F) a
    (isClosed_eq (Complex.continuous_conj.comp hθ.2) hθ.2) fun f => ?_
  have e : (algebraMap F (Ainf F) f) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] (algebraMap F E f) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [e, hθ.1, starRingEnd_apply, ← hσ, AlgHom.commutes]

theorem comp_cAF {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hσ : ∀ x, τ (σ x) = star (τ x))
    {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmbF τ θ) (z : AEF F E) :
    θ (infPartF F E (cAF σ z)) = starRingEnd ℂ (θ (infPartF F E z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a x =>
    have e : ∀ y : E, fstA F a ⊗ₜ[F] y = (fstA F a ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] y) := by
      intro y; simp
    have e2 : infPartF F E (cAF σ (a ⊗ₜ[F] x)) = fstA F a ⊗ₜ[F] (σ x) := rfl
    have e3 : infPartF F E (a ⊗ₜ[F] x) = fstA F a ⊗ₜ[F] x := rfl
    rw [e2, e3, e (σ x), e x, map_mul, map_mul, map_mul, conj_tmul_one_F hσ hθ, hθ.1, hθ.1, hσ]
    rfl

theorem compAtF_unitary {σ : E →ₐ[F] E} {tau : InfinitePlace F → (E →+* ℂ)}
    {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} (hσ : ∀ w x, tau w (σ x) = star (tau w x))
    (hθ : IsInfFamF tau θ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) (w : InfinitePlace F) :
    (compAtF θ w (mtF σ J g))ᴴ * J.map (tau w) * compAtF θ w (mtF σ J g) = J.map (tau w) := by
  have hg : ((mtF σ J g).map (cAF σ))ᵀ * JR (AF F) J * mtF σ J g = JR (AF F) J := g.2
  have hJ : (JR (AF F) J).map ((θ w).comp (infPartF F E)) = J.map (tau w) := by
    ext i j
    have : infPartF F E (inclR (AF F) (J i j)) = (1 : Ainf F) ⊗ₜ[F] J i j := rfl
    show θ w (infPartF F E (inclR (AF F) (J i j))) = _
    rw [this]
    exact (hθ w).1 (J i j)
  rw [← hJ]
  exact GlobalTheory.FockCompare.RealAction.unitary_map (cAF σ) ((θ w).comp (infPartF F E)) (comp_cAF (hσ w) (hθ w)) _ _ hg

theorem compAtF_mul_inv (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) {σ : E →ₐ[F] E} {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) (w : InfinitePlace F) :
    compAtF θ w (mtF σ J g) * compAtF θ w (mtF σ J g⁻¹) = 1 := by
  have h1 : mtF σ J 1 = 1 := by unfold mtF; rw [map_one]; rfl
  rw [compAtF, compAtF, ← Matrix.map_mul, ← GlobalTheory.WeilPartsF.mtF_mul, mul_inv_cancel, h1,
    Matrix.map_one _ (map_zero _) (map_one _)]

end Unitary

theorem mMF_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ p : GAF σ JS × GAF σ JT, (mMF σ JS JT θ p)ᴴ * HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) * mMF σ JS JT θ p = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ θ hθ ι _ p
  obtain ⟨g, h⟩ := p
  have hσ : ∀ w x, (B.emb w).1 (σ x) = star ((B.emb w).1 x) := fun w x => hB.cm.2.2.2 _ x
  unfold HMF
  rw [mMF_apply, blk_conjTranspose, blk_mul, blk_mul]
  congr 1 <;> funext w
  · rw [Matrix.mul_smul, Matrix.smul_mul, compAtF_unitary hσ hθ]
  · have h1 := compAtF_unitary hσ hθ JS g w
    have h2 := compAtF_mul_inv θ JS g w
    conv_rhs => rw [← h1, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv, inv_eq_right_inv h2]

end GlobalTheory.RealWeilF

end
