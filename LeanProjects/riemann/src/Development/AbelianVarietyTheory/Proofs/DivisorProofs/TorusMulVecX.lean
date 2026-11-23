import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviTorus

open Matrix

variable {R : Type} [CommRing R] {n m : ℕ}

def torusMat (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (t : Rˣ) : Matrix (Fin n) (Fin n) R :=
  1 + ((t : R) - 1) • vecMulVec X (J *ᵥ fun i => c (Y i)) + (1 - c (↑t⁻¹ : R)) • vecMulVec Y (J *ᵥ fun i => c (X i))

section
variable (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R)

theorem conj_mulVec (hJ : ∀ i j, c (J j i) = -J i j) (V : Fin n → R) (hc : ∀ r, c (c r) = r) :
    (fun i => c ((J *ᵥ fun k => c (V k)) i)) = -(V ᵥ* J) := by
  funext i
  simp only [mulVec, vecMul, dotProduct, map_sum, map_mul, hc, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hJ k i]; ring

theorem conj_dot (a b : Fin n → R) : c (a ⬝ᵥ b) = (fun i => c (a i)) ⬝ᵥ (fun i => c (b i)) := by
  simp [dotProduct, map_sum, map_mul]

theorem vmv_mulVec (u v w : Fin n → R) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

end

section Props

variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R}
  (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j)
  (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0) (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0)
  (hXY : X ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 1)
include hc hJ hXY

theorem dot_yx : Y ⬝ᵥ J *ᵥ (fun i => c (X i)) = -1 := by
  rw [dotProduct_mulVec]
  have h := conj_mulVec c J hJ Y hc
  rw [show Y ᵥ* J = -(fun i => c ((J *ᵥ fun k => c (Y k)) i)) by rw [h, neg_neg]]
  rw [neg_dotProduct, ← conj_dot, dotProduct_comm (J *ᵥ _) X, hXY, map_one]

omit hc hJ in
theorem torus_mulVec_x (t : Rˣ) (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0) :
    torusMat c J X Y t *ᵥ X = (t : R) • X := by
  simp only [torusMat, add_mulVec, one_mulVec, smul_mulVec, vmv_mulVec]
  rw [dotProduct_comm (J *ᵥ _) X, dotProduct_comm (J *ᵥ _) X, hXY, hXX]
  module

theorem torus_mulVec_y (t : Rˣ) (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0) :
    torusMat c J X Y t *ᵥ Y = c (↑t⁻¹ : R) • Y := by
  have hyx := dot_yx hc hJ hXY
  simp only [torusMat, add_mulVec, one_mulVec, smul_mulVec, vmv_mulVec]
  rw [dotProduct_comm (J *ᵥ _) Y, dotProduct_comm (J *ᵥ _) Y, hyx, hYY]
  module

theorem torus_mul_of (t : Rˣ) (A : Matrix (Fin n) (Fin m) R) (hu : (J *ᵥ fun i => c (Y i)) ᵥ* A = 0)
    (hw : (J *ᵥ fun i => c (X i)) ᵥ* A = 0) : torusMat c J X Y t * A = A := by
  have hz : ∀ v : Fin n → R, vecMulVec v (0 : Fin m → R) = 0 := fun v => by ext; simp [vecMulVec]
  simp only [torusMat, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, vecMulVec_mul, hu, hw, hz, smul_zero, add_zero]

theorem torus_mul_inv (t : Rˣ) (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0)
    (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0) : torusMat c J X Y t * torusMat c J X Y t⁻¹ = 1 := by
  have hyx := dot_yx hc hJ hXY
  have ht : (t : R) * (↑t⁻¹ : R) = 1 := Units.mul_inv t
  have hct : c (t : R) * c (↑t⁻¹ : R) = 1 := by rw [← map_mul, ht, map_one]
  simp only [torusMat, inv_inv, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, vecMulVec_mul_vecMulVec]
  rw [dotProduct_comm (J *ᵥ fun i => c (Y i)) X, dotProduct_comm (J *ᵥ fun i => c (Y i)) Y,
    dotProduct_comm (J *ᵥ fun i => c (X i)) X, dotProduct_comm (J *ᵥ fun i => c (X i)) Y, hXY, hYY, hXX, hyx]
  simp only [vecMulVec_smul, vecMulVec_neg, zero_smul, vecMulVec_zero, smul_zero, add_zero, zero_add, one_smul, neg_smul, smul_neg,
    smul_smul]
  match_scalars <;> first | linear_combination ht | linear_combination -hct | ring1

theorem torus_unitary (t : Rˣ) (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0)
    (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0) :
    (torusMat c J X Y t)ᵀ * J * (torusMat c J X Y t).map c = J := by
  have hyx := dot_yx hc hJ hXY
  have ht : (t : R) * (↑t⁻¹ : R) = 1 := Units.mul_inv t
  have hct : c (t : R) * c (↑t⁻¹ : R) = 1 := by rw [← map_mul, ht, map_one]
  have hu := conj_mulVec c J hJ Y hc
  have hw := conj_mulVec c J hJ X hc
  have hmap : (torusMat c J X Y t).map c = 1 + c ((t : R) - 1) • vecMulVec (fun i => c (X i)) (-(Y ᵥ* J)) +
      c (1 - c (↑t⁻¹ : R)) • vecMulVec (fun i => c (Y i)) (-(X ᵥ* J)) := by
    rw [← hu, ← hw]
    ext i j
    by_cases h : i = j <;> simp [torusMat, Matrix.map_apply, vecMulVec_apply, one_apply, h]
  have htr : (torusMat c J X Y t)ᵀ = 1 + ((t : R) - 1) • vecMulVec (J *ᵥ fun i => c (Y i)) X +
      (1 - c (↑t⁻¹ : R)) • vecMulVec (J *ᵥ fun i => c (X i)) Y := by
    simp [torusMat, transpose_add, transpose_smul, transpose_vecMulVec]
  have d1 : (X ᵥ* J) ⬝ᵥ (fun i => c (X i)) = 0 := by rw [← dotProduct_mulVec]; exact hXX
  have d2 : (X ᵥ* J) ⬝ᵥ (fun i => c (Y i)) = 1 := by rw [← dotProduct_mulVec]; exact hXY
  have d3 : (Y ᵥ* J) ⬝ᵥ (fun i => c (X i)) = -1 := by rw [← dotProduct_mulVec]; exact hyx
  have d4 : (Y ᵥ* J) ⬝ᵥ (fun i => c (Y i)) = 0 := by rw [← dotProduct_mulVec]; exact hYY
  rw [hmap, htr]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_neg, Matrix.mul_neg, Matrix.neg_mul, smul_neg]
  simp only [vecMulVec_mul, mul_vecMulVec, vmv_mulVec, vecMul_vecMulVec, d1, d2, d3, d4, smul_vecMulVec, vecMulVec_smul,
    vecMulVec_neg, dotProduct_neg, dotProduct_smul, neg_dotProduct, smul_dotProduct]
  simp only [vecMulVec_smul, smul_vecMulVec, vecMulVec_neg, zero_smul, vecMulVec_zero, smul_zero, add_zero, zero_add, one_smul,
    neg_smul, smul_neg, smul_smul, neg_neg, map_sub, map_one, hc]
  match_scalars <;> first | linear_combination ht | linear_combination -ht | linear_combination hct |
    linear_combination -hct | ring1

end Props

end GlobalTheory.LeviTorus

namespace GlobalTheory.LeviTorus

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, h]
  | add a b ha hb => simp [map_add, ha, hb]

theorem cA_incl (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem form_incl (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    incV F x ⬝ᵥ incM F J *ᵥ (fun i => cA σ (incV F y i)) = inclR (F := F) (AF F) (form σ J x y) := by
  simp [form, incV, incM, cA_incl, dotProduct, mulVec, map_sum, map_mul]

theorem vecMul_incM (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin k) E) (y : Fin n → E) :
    (incM F J *ᵥ fun i => cA σ (incV F y i)) ᵥ* incM F A =
      fun j => inclR (F := F) (AF F) (form σ J (A *ᵥ Pi.single j 1) y) := by
  funext j
  rw [← form_incl]
  simp only [vecMul, dotProduct, incV, incM, Matrix.map_apply, mulVec_single_one]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]; rfl

end GlobalTheory.LeviTorus

theorem GlobalTheory.LeviTorus.exists_levi : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ t : (AE F E)ˣ, ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA _ t
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
  have hXY : incV F H'.x ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.y i)) = 1 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl,
      GlobalTheory.LeviTorus.form_incl, hA.xy, map_one]
  have h01 := GlobalTheory.LeviTorus.torus_mul_inv hc hJ hXY t hXX hYY
  have h10 : GlobalTheory.LeviTorus.torusMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) t⁻¹ *
      GlobalTheory.LeviTorus.torusMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) t = 1 :=
    by simpa only [inv_inv] using GlobalTheory.LeviTorus.torus_mul_inv hc hJ hXY t⁻¹ hXX hYY
  refine ⟨⟨⟨GlobalTheory.LeviTorus.torusMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) t, _, h01, h10⟩, ?_⟩, ?_, ?_, ?_⟩
  · exact GlobalTheory.LeviTorus.torus_unitary hc hJ hXY t hXX hYY
  · exact GlobalTheory.LeviTorus.torus_mulVec_x hXY t hXX
  · exact GlobalTheory.LeviTorus.torus_mulVec_y hc hJ hXY t hYY
  · have hu : (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F H'.y i)) ᵥ* incM F H'.ι = 0 := by
      rw [show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl,
        GlobalTheory.LeviTorus.vecMul_incM]
      funext j
      rw [(hA.orth _).2, map_zero]; rfl
    have hw : (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F H'.x i)) ᵥ* incM F H'.ι = 0 := by
      rw [show (fun i => (cA σ).toRingHom (incV F H'.x i)) = fun i => cA σ (incV F H'.x i) from rfl,
        GlobalTheory.LeviTorus.vecMul_incM]
      funext j
      rw [(hA.orth _).1, map_zero]; rfl
    show GlobalTheory.LeviTorus.torusMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) t * incM F H'.ι =
      incM F H'.ι * 1
    rw [Matrix.mul_one]
    exact GlobalTheory.LeviTorus.torus_mul_of hc hJ hXY t _ hu hw
