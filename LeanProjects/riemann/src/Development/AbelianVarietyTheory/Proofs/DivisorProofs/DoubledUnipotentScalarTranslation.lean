import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusMulVecX

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblUnipU

open Matrix GlobalTheory.DblUnip GlobalTheory.LeviTorus

variable {R : Type} [CommRing R] {d : ℕ}

section Props

variable {c : R →+* R} {J : Matrix (Fin d) (Fin d) R} {X Y : Fin d → R}
  (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j)
  (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0) (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0)

include hXX hYY in
theorem unip_mul_neg (β : R) : unipMat c J X Y β * unipMat c J X Y (-β) = 1 := by
  have e1 : (J *ᵥ fun i => c (Y i)) ⬝ᵥ Y = 0 := by rw [dotProduct_comm]; exact hYY
  have e2 : (J *ᵥ fun i => c (X i)) ⬝ᵥ X = 0 := by rw [dotProduct_comm]; exact hXX
  simp only [unipMat, fromBlocks_multiply, map_neg, neg_neg, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, vecMulVec_mul_vecMulVec, e1, e2, zero_smul, vecMulVec_zero, smul_zero, neg_smul, Matrix.neg_mul,
    Matrix.mul_neg, neg_zero, add_zero, neg_add_cancel, add_neg_cancel, zero_add, fromBlocks_one]

include hc hJ hXX hYY in
theorem unip_unitary (β : R) :
    (unipMat c J X Y β)ᵀ * fromBlocks J 0 0 (-J) * (unipMat c J X Y β).map c = fromBlocks J 0 0 (-J) := by
  have hu := conj_mulVec c J hJ Y hc
  have hw := conj_mulVec c J hJ X hc
  have d1 : (X ᵥ* J) ⬝ᵥ (fun i => c (X i)) = 0 := by rw [← dotProduct_mulVec]; exact hXX
  have d4 : (Y ᵥ* J) ⬝ᵥ (fun i => c (Y i)) = 0 := by rw [← dotProduct_mulVec]; exact hYY
  have hmap : (unipMat c J X Y β).map c = fromBlocks 1 (c β • vecMulVec (fun i => c (X i)) (-(Y ᵥ* J)))
      (-β • vecMulVec (fun i => c (Y i)) (-(X ᵥ* J))) 1 := by
    rw [← hu, ← hw]
    simp only [unipMat, fromBlocks_map]
    congr 1
    · exact Matrix.map_one c (map_zero c) (map_one c)
    · ext i j; simp [Matrix.map_apply, vecMulVec_apply]
    · ext i j; simp [Matrix.map_apply, vecMulVec_apply, hc]
    · exact Matrix.map_one c (map_zero c) (map_one c)
  have htr : (unipMat c J X Y β)ᵀ = fromBlocks 1 (-(c β) • vecMulVec (J *ᵥ fun i => c (X i)) Y)
      (β • vecMulVec (J *ᵥ fun i => c (Y i)) X) 1 := by
    simp [unipMat, fromBlocks_transpose, transpose_smul, transpose_vecMulVec]
  rw [hmap, htr]
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg, vecMulVec_mul, mul_vecMulVec,
    vecMulVec_mul_vecMulVec, vecMulVec_neg, dotProduct_neg, neg_dotProduct, d1, d4, neg_zero, zero_smul, vecMulVec_zero,
    smul_zero, smul_neg, neg_smul, neg_neg, smul_mulVec, vmv_mulVec, Matrix.neg_mulVec, neg_vecMulVec, zero_vecMulVec, neg_add_cancel, add_neg_cancel]

end Props

end GlobalTheory.DblUnipU

theorem GlobalTheory.DblUnipU.exists_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ β : AE F E, ∃ u : UG (cA σ) (dbl (incM F W.J)), (u.1.1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = GlobalTheory.DblUnip.unipMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) β := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hA β
  have hσ := GlobalTheory.LeviTorus.sigma_invol hP.base.cm
  have hc : ∀ a : AE F E, (cA σ).toRingHom ((cA σ).toRingHom a) = a := GlobalTheory.LeviTorus.cA_invol hσ
  have hJ : ∀ i j, (cA σ).toRingHom (incM F W.J j i) = -incM F W.J i j := by
    intro i j
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, incM, Matrix.map_apply, GlobalTheory.LeviTorus.cA_incl, hP.skew.skew i j, map_neg]
  have hXX : incV F H'.x ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.x i)) = 0 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H'.x i)) = fun i => cA σ (incV F H'.x i) from rfl,
      GlobalTheory.LeviTorus.form_incl, hA.xx, map_zero]
  have hYY : incV F H'.y ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.y i)) = 0 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl,
      GlobalTheory.LeviTorus.form_incl, hA.yy, map_zero]
  have h01 := GlobalTheory.DblUnipU.unip_mul_neg hXX hYY β
  have h10 : GlobalTheory.DblUnip.unipMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) (-β) *
      GlobalTheory.DblUnip.unipMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) β = 1 := by
    simpa only [neg_neg] using GlobalTheory.DblUnipU.unip_mul_neg hXX hYY (-β)
  exact ⟨⟨⟨_, _, h01, h10⟩, GlobalTheory.DblUnipU.unip_unitary hc hJ hXX hYY β⟩, rfl⟩
