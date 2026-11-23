import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.AdelicPlaneLevi

open Matrix

section Gen

variable {R : Type} [CommRing R] {n : ℕ} (c : R →+* R) (J : Matrix (Fin n) (Fin n) R)

def fR (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ (fun i => c (v i))

theorem fR_add_left (u u' v : Fin n → R) : fR c J (u + u') v = fR c J u v + fR c J u' v := by
  simp [fR, add_dotProduct]

theorem fR_sub_left (u u' v : Fin n → R) : fR c J (u - u') v = fR c J u v - fR c J u' v := by
  simp [fR, sub_dotProduct]

theorem fR_smul_left (r : R) (u v : Fin n → R) : fR c J (r • u) v = r * fR c J u v := by
  simp [fR, smul_dotProduct]

theorem fR_add_right (u v v' : Fin n → R) : fR c J u (v + v') = fR c J u v + fR c J u v' := by
  have h : (fun i => c ((v + v') i)) = (fun i => c (v i)) + fun i => c (v' i) := by funext i; simp
  unfold fR; rw [h, Matrix.mulVec_add, dotProduct_add]

theorem fR_sub_right (u v v' : Fin n → R) : fR c J u (v - v') = fR c J u v - fR c J u v' := by
  have h : (fun i => c ((v - v') i)) = (fun i => c (v i)) - fun i => c (v' i) := by funext i; simp
  unfold fR; rw [h, Matrix.mulVec_sub, dotProduct_sub]

theorem fR_smul_right (r : R) (u v : Fin n → R) : fR c J u (r • v) = c r * fR c J u v := by
  have h : (fun i => c ((r • v) i)) = c r • fun i => c (v i) := by funext i; simp
  unfold fR; rw [h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem fR_skew (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j) (u v : Fin n → R) :
    c (fR c J u v) = -fR c J v u := by
  simp only [fR, dotProduct, Matrix.mulVec, map_sum, map_mul, hc, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem fR_mulVec (A : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) :
    fR c J (A *ᵥ u) (A *ᵥ v) = u ⬝ᵥ (Aᵀ * J * A.map c) *ᵥ (fun i => c (v i)) := by
  have h : (fun i => c ((A *ᵥ v) i)) = A.map c *ᵥ fun i => c (v i) := by
    funext i; exact RingHom.map_mulVec c A v i
  simp only [fR, h]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Aᵀ, Matrix.vecMul_transpose]

theorem eq_of_form (M N : Matrix (Fin n) (Fin n) R)
    (h : ∀ u v : Fin n → R, u ⬝ᵥ M *ᵥ (fun i => c (v i)) = u ⬝ᵥ N *ᵥ (fun i => c (v i))) : M = N := by
  ext i j
  have hs : (fun k => c ((Pi.single j (1 : R) : Fin n → R) k)) = Pi.single j 1 := by
    funext k; by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hs] at this
  simpa [Matrix.mulVec_single_one] using this

theorem eq_of_mulVec (M N : Matrix (Fin n) (Fin n) R) (h : ∀ u, M *ᵥ u = N *ᵥ u) : M = N := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

def lev (x y : Fin n → R) (t s : R) : Matrix (Fin n) (Fin n) R :=
  1 + (t - 1) • vecMulVec x (J *ᵥ fun i => c (y i)) - (s - 1) • vecMulVec y (J *ᵥ fun i => c (x i))

theorem lev_mulVec (x y : Fin n → R) (t s : R) (u : Fin n → R) :
    lev c J x y t s *ᵥ u = u + ((t - 1) * fR c J u y) • x - ((s - 1) * fR c J u x) • y := by
  simp only [lev, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul, fR]
  rw [dotProduct_comm (J *ᵥ _) u, dotProduct_comm (J *ᵥ _) u]

variable {c J}
variable {x y : Fin n → R} (hxx : fR c J x x = 0) (hyy : fR c J y y = 0) (hxy : fR c J x y = 1)
  (hyx : fR c J y x = -1)
include hxx hyy hxy hyx

theorem levi_element_fixes_first_vector (t s : R) : lev c J x y t s *ᵥ x = t • x := by
  rw [lev_mulVec, hxy, hxx]; module

theorem lev_y (t s : R) : lev c J x y t s *ᵥ y = s • y := by
  rw [lev_mulVec, hyy, hyx]; module

theorem lev_mul (t s t' s' : R) (h1 : t * t' = 1) (h2 : s * s' = 1) :
    lev c J x y t s * lev c J x y t' s' = 1 := by
  apply eq_of_mulVec; intro u
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec, lev_mulVec c J x y t' s' u, lev_mulVec c J x y t s]
  simp only [fR_add_left, fR_sub_left, fR_smul_left, hxx, hyy, hxy, hyx]
  linear_combination (norm := module) (fR c J u y) • h1 • x - (fR c J u x) • h2 • y

theorem lev_orth (t s : R) (z : Fin n → R) (hz : fR c J z x = 0) (hz' : fR c J z y = 0) :
    lev c J x y t s *ᵥ z = z := by
  rw [lev_mulVec, hz, hz']; simp

theorem lev_unitary (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j) (t s : R) (h1 : c t * s = 1) (h2 : t * c s = 1) :
    (lev c J x y t s)ᵀ * J * (lev c J x y t s).map c = J := by
  apply eq_of_form c; intro u v
  rw [← fR_mulVec]
  change fR c J (lev c J x y t s *ᵥ u) (lev c J x y t s *ᵥ v) = fR c J u v
  have hxv : fR c J x v = -c (fR c J v x) := by rw [fR_skew c J hc hJ]; ring
  have hyv : fR c J y v = -c (fR c J v y) := by rw [fR_skew c J hc hJ]; ring
  rw [lev_mulVec, lev_mulVec]
  simp only [fR_add_left, fR_sub_left, fR_smul_left, fR_add_right, fR_sub_right, fR_smul_right, hxx, hyy, hxy, hyx,
    hxv, hyv, map_mul, map_sub, map_one]
  linear_combination (c (fR c J v y) * fR c J u x) * h1 - (fR c J u y * c (fR c J v x)) * h2

end Gen

end GlobalTheory.AdelicPlaneLevi

namespace GlobalTheory.AdelicPlaneLevi

open Matrix

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_incl (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [cA, inclR]

theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [cA, hσ]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem sigma_invol {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]

theorem fR_inc (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) (a b : Fin d → E) :
    fR (cA σ).toRingHom (incM F J) (incV F a) (incV F b) = inclR (AF F) (form σ J a b) := by
  simp [fR, form, incV, incM, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_incl]

end Main

theorem exists_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ t : (AE F E)ˣ, ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m := by
  intro F E _ _ _ _ _ σ B d W r s d₁ W₁ H' i₀ i₁ hcm hW hH t
  have hσ : ∀ e, σ (σ e) = e := sigma_invol hcm
  let c : AE F E →+* AE F E := (cA σ).toRingHom
  have hc : ∀ a, c (c a) = a := cA_cA σ hσ
  have hJ : ∀ i j, c (incM F W.J j i) = -incM F W.J i j := by
    intro i j; simp [c, incM, cA_incl, hW.skew]
  have hxx : fR c (incM F W.J) (incV F H'.x) (incV F H'.x) = 0 := by rw [fR_inc, hH.xx, map_zero]
  have hyy : fR c (incM F W.J) (incV F H'.y) (incV F H'.y) = 0 := by rw [fR_inc, hH.yy, map_zero]
  have hxy : fR c (incM F W.J) (incV F H'.x) (incV F H'.y) = 1 := by rw [fR_inc, hH.xy, map_one]
  have hyx : fR c (incM F W.J) (incV F H'.y) (incV F H'.x) = -1 := by
    have := fR_skew c (incM F W.J) hc hJ (incV F H'.x) (incV F H'.y)
    rw [hxy, map_one] at this
    linear_combination this
  let s' : AE F E := c ((t⁻¹ : (AE F E)ˣ) : AE F E)
  let M := lev c (incM F W.J) (incV F H'.x) (incV F H'.y) t s'
  let M' := lev c (incM F W.J) (incV F H'.x) (incV F H'.y) ((t⁻¹ : (AE F E)ˣ) : AE F E) (c t)
  have e1 : s' * c t = 1 := by simp only [s', ← map_mul, Units.inv_mul, map_one]
  have e2 : c t * s' = 1 := by simp only [s', ← map_mul, Units.mul_inv, map_one]
  have hMM' : M * M' = 1 := lev_mul hxx hyy hxy hyx _ _ _ _ t.mul_inv e1
  have hM'M : M' * M = 1 := lev_mul hxx hyy hxy hyx _ _ _ _ t.inv_mul e2
  have hU : Mᵀ * incM F W.J * M.map c = incM F W.J := by
    refine lev_unitary hxx hyy hxy hyx hc hJ _ _ e2 ?_
    simp only [s', hc, Units.mul_inv]
  refine ⟨⟨⟨M, M', hMM', hM'M⟩, by exact hU⟩, ?_, ?_, ?_⟩
  · exact levi_element_fixes_first_vector hxx hyy hxy hyx _ _
  · exact lev_y hxx hyy hxy hyx _ _
  · show M * incM F H'.ι = incM F H'.ι * mat (1 : UA σ W₁.J)
    have h1 : mat (1 : UA σ W₁.J) = 1 := rfl
    rw [h1, Matrix.mul_one]
    ext i j
    have e : (fun k => incM F H'.ι k j) = incV F (H'.ι *ᵥ Pi.single j 1) := by
      funext k; simp [incV, incM, Matrix.mulVec_single_one]
    have hz : fR c (incM F W.J) (fun k => incM F H'.ι k j) (incV F H'.x) = 0 := by
      rw [e, fR_inc, (hH.orth _).1, map_zero]
    have hz' : fR c (incM F W.J) (fun k => incM F H'.ι k j) (incV F H'.y) = 0 := by
      rw [e, fR_inc, (hH.orth _).2, map_zero]
    have := congrFun (lev_orth hxx hyy hxy hyx t s' _ hz hz') i
    simpa [M, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

end GlobalTheory.AdelicPlaneLevi

end
