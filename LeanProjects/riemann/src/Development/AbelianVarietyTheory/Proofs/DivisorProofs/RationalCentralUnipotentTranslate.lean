import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.ThK.UnipDom.RatCentral

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := ⟨(IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom⟩
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin n → E) : form σ J y x = -σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

open Matrix in

def vc (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) : Fin n → E := J *ᵥ fun i => σ (x i)

def gam (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (s : E) : Matrix (Fin n) (Fin n) E :=
  1 - s • Matrix.vecMulVec x (vc σ J x)

theorem vc_dot {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : Fin n → E} (hxx : form σ J x x = 0) :
    vc σ J x ⬝ᵥ x = 0 := by
  rw [dotProduct_comm]; exact hxx

theorem gam_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : Fin n → E} (hxx : form σ J x x = 0) (s : E) :
    gam σ J x s * gam σ J x (-s) = 1 := by
  have hP : Matrix.vecMulVec x (vc σ J x) * Matrix.vecMulVec x (vc σ J x) = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, vc_dot hxx, zero_smul, Matrix.vecMulVec_zero]
  have hn : gam σ J x (-s) = 1 + s • Matrix.vecMulVec x (vc σ J x) := by simp [gam, neg_smul, sub_neg_eq_add]
  rw [hn, gam, sub_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, Matrix.mul_smul, hP, smul_zero, smul_zero, add_zero,
    add_sub_cancel_right]

theorem vecMul_vc {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (x : Fin n → E) : x ᵥ* J = -fun j => σ (vc σ J x j) := by
  funext j
  simp only [vc, Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, map_mul, hσ, Pi.neg_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hJ]; ring

theorem gam_unitary {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) {x : Fin n → E} (hxx : form σ J x x = 0) (q : F) :
    (gam σ J x (algebraMap F E q))ᵀ * J * (gam σ J x (algebraMap F E q)).map σ = J := by
  have hm : (gam σ J x (algebraMap F E q)).map σ =
      1 - algebraMap F E q • Matrix.vecMulVec (fun i => σ (x i)) (fun j => σ (vc σ J x j)) := by
    ext i j
    simp [gam, Matrix.one_apply, Matrix.vecMulVec_apply, apply_ite σ, AlgHom.map_smul_of_tower, map_mul]
  have e1 : J * Matrix.vecMulVec (fun i => σ (x i)) (fun j => σ (vc σ J x j)) =
      Matrix.vecMulVec (vc σ J x) (fun j => σ (vc σ J x j)) := by rw [Matrix.mul_vecMulVec]; rfl
  have e2 : Matrix.vecMulVec (vc σ J x) x * J = -Matrix.vecMulVec (vc σ J x) (fun j => σ (vc σ J x j)) := by
    rw [Matrix.vecMulVec_mul, vecMul_vc hσ hJ, Matrix.vecMulVec_neg]
  have e3 : x ᵥ* J ⬝ᵥ (fun i => σ (x i)) = 0 := by rw [← Matrix.dotProduct_mulVec]; exact hxx
  rw [hm]
  simp only [gam, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, Matrix.transpose_vecMulVec,
    sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, e1, e2, Matrix.mul_assoc]
  have e4 : Matrix.vecMulVec (vc σ J x) (fun j => σ (vc σ J x j)) * Matrix.vecMulVec (fun i => σ (x i)) (fun j => σ (vc σ J x j)) = 0 := by
    have : (fun j => σ (vc σ J x j)) = -(x ᵥ* J) := by rw [vecMul_vc hσ hJ, neg_neg]
    rw [Matrix.vecMulVec_mul_vecMulVec, this, neg_dotProduct, e3, neg_zero, zero_smul, Matrix.vecMulVec_zero]
  rw [Matrix.neg_mul, e4]
  simp

def gamGL (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (hxx : form σ J x x = 0) (s : E) :
    GL (Fin n) E :=
  ⟨gam σ J x s, gam σ J x (-s), gam_mul hxx s, by have := gam_mul hxx (-s); rwa [neg_neg] at this⟩

theorem mat_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_inv_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) : mat g⁻¹ * mat g = 1 :=
  Units.inv_mul g.1

theorem mat_unitary {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) :
    (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2

def stab (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Fin n → AE F E) : Subgroup (UA σ J) where
  carrier := {g | mat g *ᵥ v = v}
  one_mem' := by
    show ((1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ v = v
    simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [mat_mul, ← Matrix.mulVec_mulVec, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    calc mat a⁻¹ *ᵥ v = mat a⁻¹ *ᵥ (mat a *ᵥ v) := by rw [ha]
      _ = v := by rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]

theorem incM_mulVec_incV {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incM F M *ᵥ incV F v = incV F (M *ᵥ v) := by
  funext i
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) M v i).symm

theorem fA_incV_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (w : Fin n → AE F E) (x : Fin n → E) :
    fA σ J w (incV F x) = w ⬝ᵥ incV F (vc σ J x) := by
  have : (fun i => cA σ (incV F x i)) = incV F (fun i => σ (x i)) := by
    funext i; exact cA_inclR σ (x i)
  rw [fA, this, incM_mulVec_incV]; rfl

theorem incV_dot {n : ℕ} (a b : Fin n → E) : incV F a ⬝ᵥ incV F b = inclR (F := F) (AF F) (a ⬝ᵥ b) := by
  simp [incV, dotProduct, map_sum, map_mul]

theorem fA_incV (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    fA σ J (incV F a) (incV F b) = inclR (F := F) (AF F) (form σ J a b) := by
  rw [fA_incV_right, incV_dot]; rfl

theorem fA_sub_smul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v u w : Fin n → AE F E) (a : AE F E) :
    fA σ J (v - a • u) w = fA σ J v w - a * fA σ J u w := by
  simp [fA, sub_dotProduct, smul_dotProduct]

theorem fA_unitary {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (v w : Fin n → AE F E) :
    fA σ J (mat g *ᵥ v) (mat g *ᵥ w) = fA σ J v w := by
  have hc : (fun i => cA σ ((mat g *ᵥ w) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom (mat g) w i
  rw [fA, fA, hc, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, ← Matrix.mul_assoc,
    mat_unitary, ← Matrix.dotProduct_mulVec]

theorem gam_map_mulVec (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (s : E) (w : Fin n → AE F E) :
    (gam σ J x s).map (inclR (F := F) (AF F)) *ᵥ w =
      w - (inclR (F := F) (AF F) s * (incV F (vc σ J x) ⬝ᵥ w)) • incV F x := by
  funext i
  simp only [gam, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, map_sub, smul_eq_mul, map_mul, Pi.sub_apply, Pi.smul_apply, incV, sub_mul,
    Finset.sum_sub_distrib, apply_ite (inclR (F := F) (AF F)), map_one, map_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gam_map_unitary {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) {x : Fin n → E} (hxx : form σ J x x = 0) (q : F) :
    Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) (gamGL σ J x hxx (algebraMap F E q)) ∈
      UG (cA σ) (incM F J) := by
  show ((gam σ J x (algebraMap F E q)).map (inclR (F := F) (AF F)))ᵀ * incM F J *
      ((gam σ J x (algebraMap F E q)).map (inclR (F := F) (AF F))).map (cA σ) = incM F J
  have hc : (cA σ) ∘ (inclR (F := F) (E := E) (AF F)) = (inclR (F := F) (AF F)) ∘ σ := funext (cA_inclR σ)
  rw [Matrix.map_map, hc, ← Matrix.map_map, ← Matrix.transpose_map, incM, ← Matrix.map_mul, ← Matrix.map_mul,
    gam_unitary hσ hJ hxx q]

theorem inclR_algebraMap (q : F) :
    inclR (F := F) (AF F) (algebraMap F E q) = algebraMap (AF F) (AE F E) (algebraMap F (AF F) q) := by
  rw [← IsScalarTower.algebraMap_apply]; simp [inclR]

theorem exists_rat_translate_coC : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (r s i₀ i₁ : ℕ),
    IsCMExt F E σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ q : F,
    ∃ γ ∈ unip σ W H', γ ∈ ratU σ W.J ∧ ∀ u ∈ unip σ W H', coA σ W.J H' (γ * u) = coA σ W.J H' u ∧
      coC σ W.J H' (γ * u) = algebraMap (AF F) (AE F E) (algebraMap F (AF F) q) + coC σ W.J H' u := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' r s i₀ i₁ hCM hW hH q
  have hσ := sig_sig hCM
  have hJ := hW.skew
  let g : GL (Fin d) E := gamGL σ W.J H'.x hH.xx (algebraMap F E q)
  let γ : UA σ W.J := ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) g, gam_map_unitary hσ hJ hH.xx q⟩
  have hmat : ∀ w, mat γ *ᵥ w = w - (inclR (F := F) (AF F) (algebraMap F E q) *
      (incV F (vc σ W.J H'.x) ⬝ᵥ w)) • incV F H'.x := gam_map_mulVec σ W.J H'.x _
  have hcx : ∀ w, incV F (vc σ W.J H'.x) ⬝ᵥ w = fA σ W.J w (incV F H'.x) := fun w => by
    rw [fA_incV_right, dotProduct_comm]
  have hyx : form σ W.J H'.y H'.x = -1 := by rw [form_swap hσ hJ, hH.xy, map_one]
  have hxy : fA σ W.J (incV F H'.x) (incV F H'.y) = 1 := by rw [fA_incV, hH.xy, map_one]
  refine ⟨γ, Subgroup.subset_closure ⟨?_, fun z => ⟨_, by rw [hmat, sub_eq_add_neg, ← neg_smul]⟩⟩,
    Subgroup.mem_subgroupOf.mpr ⟨g, rfl⟩, fun u hu => ?_⟩
  · rw [hmat, hcx, fA_incV, hH.xx, map_zero, mul_zero, zero_smul, sub_zero]
  have hux : mat u *ᵥ incV F H'.x = incV F H'.x :=
    (Subgroup.closure_le (K := stab σ W.J (incV F H'.x))).mpr (fun g hg => hg.1) hu
  refine ⟨funext fun j => ?_, ?_⟩
  · have he : incM F H'.ι *ᵥ Pi.single j 1 = incV F (H'.ι *ᵥ Pi.single j 1) := by
      rw [← incM_mulVec_incV]; congr 1; funext k; by_cases h : k = j <;> simp [incV, Pi.single_apply, h]
    have k0 : fA σ W.J (mat u *ᵥ (incM F H'.ι *ᵥ Pi.single j 1)) (incV F H'.x) = 0 := by
      conv_lhs => rw [← hux]
      rw [fA_unitary, he, fA_incV, (hH.orth _).1, map_zero]
    show fA σ W.J (mat (γ * u) *ᵥ (incM F H'.ι *ᵥ Pi.single j 1)) (incV F H'.y) =
      fA σ W.J (mat u *ᵥ (incM F H'.ι *ᵥ Pi.single j 1)) (incV F H'.y)
    rw [mat_mul, ← Matrix.mulVec_mulVec, hmat, fA_sub_smul, hcx, k0, mul_zero, zero_mul, sub_zero]
  · have k1 : fA σ W.J (mat u *ᵥ incV F H'.y) (incV F H'.x) = -1 := by
      conv_lhs => rw [← hux]
      rw [fA_unitary, fA_incV, hyx, map_neg, map_one]
    show fA σ W.J (mat (γ * u) *ᵥ incV F H'.y) (incV F H'.y) =
      algebraMap (AF F) (AE F E) (algebraMap F (AF F) q) + fA σ W.J (mat u *ᵥ incV F H'.y) (incV F H'.y)
    rw [mat_mul, ← Matrix.mulVec_mulVec, hmat, fA_sub_smul, hcx, k1, hxy, inclR_algebraMap]
    ring

end GlobalTheory.ThK.UnipDom.RatCentral
