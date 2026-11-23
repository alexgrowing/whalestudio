import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinateAdditive
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.UnipDom
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.UnipDom.PlaneRatC

open GlobalTheory.ThK.UnipDom.Additive

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨_, _, _, hτ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  apply τ.injective
  rw [hτ, hτ, star_star]

theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → E) :
    form σ J w v = -σ (form σ J v w) := by
  unfold form
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

theorem entry_eq_form (σ : E →ₐ[F] E) {n : ℕ} (J M : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    (Mᵀ * J * M.map σ) i j = form σ J (fun k => M k i) (fun k => M k j) := by
  simp only [form, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

end GlobalTheory.ThK.UnipDom.PlaneRatC

namespace GlobalTheory.ThK.UnipDom.PlaneRatC

open GlobalTheory.ThK.UnipDom.Additive

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def nilM (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) : Matrix (Fin n) (Fin n) E :=
  Matrix.vecMulVec x (J *ᵥ fun i => σ (x i))

theorem nilM_mulVec (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x v : Fin n → E) :
    nilM σ J x *ᵥ v = form σ J v x • x := by
  funext i
  simp only [nilM, form, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem nilM_mul_self (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (hxx : form σ J x x = 0) : nilM σ J x * nilM σ J x = 0 := by
  ext i j
  have h : ∑ k, (J *ᵥ fun i => σ (x i)) k * x k = 0 := by
    rw [← hxx, form, dotProduct]; exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  simp only [nilM, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
  calc ∑ k, x i * (J *ᵥ fun i => σ (x i)) k * (x k * (J *ᵥ fun i => σ (x i)) j)
      = x i * (∑ k, (J *ᵥ fun i => σ (x i)) k * x k) * (J *ᵥ fun i => σ (x i)) j := by
        rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := by rw [h]; ring

def gam (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (c : E) : Matrix (Fin n) (Fin n) E :=
  1 - c • nilM σ J x

theorem gam_mulVec (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (c : E) (v : Fin n → E) :
    gam σ J x c *ᵥ v = v - (c * form σ J v x) • x := by
  rw [gam, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, nilM_mulVec, smul_smul]

theorem form_gam (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (x : Fin n → E) (hxx : form σ J x x = 0) (c : E) (hc : σ c = c)
    (v w : Fin n → E) :
    form σ J (v - (c * form σ J v x) • x) (w - (c * form σ J w x) • x) = form σ J v w := by
  have hl : ∀ (a : E) (p r : Fin n → E), form σ J (p - a • x) r = form σ J p r - a * form σ J x r := by
    intro a p r; simp [form, sub_dotProduct, smul_dotProduct]
  have hr : ∀ (a : E) (p r : Fin n → E), form σ J p (r - a • x) = form σ J p r - σ a * form σ J p x := by
    intro a p r
    have : (fun i => σ ((r - a • x) i)) = (fun i => σ (r i)) - σ a • fun i => σ (x i) := by
      funext i; simp
    simp only [form, this, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [hl, hr, hr, hxx, form_swap σ hσ J hJ w x, map_mul, hc]
  ring

end GlobalTheory.ThK.UnipDom.PlaneRatC

namespace GlobalTheory.ThK.UnipDom.PlaneRatC

open GlobalTheory.ThK.UnipDom.Additive

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem gam_unitary (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (x : Fin n → E) (hxx : form σ J x x = 0) (c : E) (hc : σ c = c) :
    (gam σ J x c)ᵀ * J * (gam σ J x c).map σ = J := by
  ext i j
  have hcol : ∀ i, (fun k => gam σ J x c k i) = gam σ J x c *ᵥ (fun k => (1 : Matrix (Fin n) (Fin n) E) k i) := by
    intro i; funext k; simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have h1 : J i j = form σ J (fun k => (1 : Matrix (Fin n) (Fin n) E) k i) (fun k => (1 : Matrix (Fin n) (Fin n) E) k j) := by
    rw [← entry_eq_form]; simp
  rw [entry_eq_form, hcol, hcol, gam_mulVec, gam_mulVec, form_gam σ hσ J hJ x hxx c hc, h1]

theorem gam_mul_inv (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (hxx : form σ J x x = 0) (c : E) : gam σ J x c * gam σ J x (-c) = 1 := by
  simp only [gam, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, nilM_mul_self σ J x hxx,
    smul_zero, sub_zero]
  rw [neg_smul]; abel

def gamGL (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E)
    (hxx : form σ J x x = 0) (c : E) : GL (Fin n) E :=
  ⟨gam σ J x c, gam σ J x (-c), gam_mul_inv σ J x hxx c, by simpa using gam_mul_inv σ J x hxx (-c)⟩

theorem gamGL_mem (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (x : Fin n → E) (hxx : form σ J x x = 0) (c : E) (hc : σ c = c) :
    Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)) (gamGL σ J x hxx c) ∈
      UG (cA σ) (incM F J) := by
  show ((gam σ J x c).map (inclR (F := F) (AF F)))ᵀ * incM F J * ((gam σ J x c).map (inclR (F := F) (AF F))).map (cA σ) = incM F J
  have hm : ((gam σ J x c).map (inclR (F := F) (AF F))).map (cA σ) = ((gam σ J x c).map σ).map (inclR (F := F) (AF F)) := by
    ext i j; simp only [Matrix.map_apply]; exact cA_inclR σ _
  rw [hm, incM, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, gam_unitary σ hσ J hJ x hxx c hc]

end GlobalTheory.ThK.UnipDom.PlaneRatC

namespace GlobalTheory.ThK.UnipDom.PlaneRatC

open GlobalTheory.ThK.UnipDom.Additive

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem fA_sub_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    fA σ J (v - v') w = fA σ J v w - fA σ J v' w := by
  simp [fA, sub_dotProduct]

theorem fA_unitary (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (v w : Fin n → AE F E) :
    fA σ J (mat g *ᵥ v) (mat g *ᵥ w) = fA σ J v w := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have hc : (fun i => cA σ ((mat g *ᵥ w) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom (mat g) w i
  unfold fA
  rw [hc, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.mul_assoc, hg, ← Matrix.dotProduct_mulVec]

theorem fA_incV_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Fin n → AE F E) (x : Fin n → E) :
    fA σ J v (incV F x) = v ⬝ᵥ incV F (J *ᵥ fun i => σ (x i)) := by
  have hb : (fun i => cA σ (incV F x i)) = incV F (fun i => σ (x i)) := funext fun i => cA_inclR σ _
  unfold fA
  rw [hb, incM_mulVec_incV]

theorem incM_gam_mulVec (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (c : E)
    (v : Fin n → AE F E) :
    incM F (gam σ J x c) *ᵥ v = v - (inclR (F := F) (AF F) c * fA σ J v (incV F x)) • incV F x := by
  rw [fA_incV_right]
  funext i
  simp only [incM, gam, nilM, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, map_sub, map_mul, smul_eq_mul, Pi.sub_apply, Pi.smul_apply, incV, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · simp [Matrix.one_apply]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

end GlobalTheory.ThK.UnipDom.PlaneRatC

open GlobalTheory.ThK.UnipDom.Additive GlobalTheory.ThK.UnipDom.PlaneRatC in

theorem GlobalTheory.ThK.UnipDom.exists_ratCentral_coC_translate_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁), IsCMExt F E σ → (∀ i j, σ (Y.J j i) = -Y.J i j) → IsIsoPlane σ B H Y Y₁ → ∀ q : F, ∃ γ ∈ unip σ Y H, γ ∈ ratU σ Y.J ∧ ∀ u ∈ unip σ Y H, coA σ Y.J H (γ * u) = coA σ Y.J H u ∧ coC σ Y.J H (γ * u) = algebraMap (AF F) (AE F E) (algebraMap F (AF F) q) + coC σ Y.J H u := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H hCM hJ hP q
  obtain ⟨-, hxx, -, hxy, horth, -, -, -⟩ := hP
  have hσ := sigma_sigma σ hCM
  have hc : σ (algebraMap F E q) = algebraMap F E q := σ.commutes q
  let γ : UA σ Y.J := ⟨_, gamGL_mem σ hσ Y.J hJ H.x hxx (algebraMap F E q) hc⟩
  have hmat : mat γ = incM F (gam σ Y.J H.x (algebraMap F E q)) := rfl
  have hγv : ∀ v, mat γ *ᵥ v =
      v - (inclR (F := F) (AF F) (algebraMap F E q) * fA σ Y.J v (incV F H.x)) • incV F H.x := fun v => by
    rw [hmat, incM_gam_mulVec]
  have hq : inclR (F := F) (AF F) (algebraMap F E q) = algebraMap (AF F) (AE F E) (algebraMap F (AF F) q) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact Algebra.TensorProduct.includeRight.commutes q
  have hxx' : fA σ Y.J (incV F H.x) (incV F H.x) = 0 := by rw [fA_incV, hxx, map_zero]
  have hxy' : fA σ Y.J (incV F H.x) (incV F H.y) = 1 := by rw [fA_incV, hxy, map_one]
  have hNι : nilM σ Y.J H.x * H.ι = 0 := by
    ext i j
    have h1 := congrFun (Matrix.mulVec_mulVec (Pi.single j (1 : E)) (nilM σ Y.J H.x) H.ι) i
    have ho := (horth (Pi.single j 1)).1
    rw [Matrix.mulVec_single_one] at ho
    rw [Matrix.mulVec_single_one, nilM_mulVec, ho, zero_smul] at h1
    simpa [Matrix.mulVec_single_one] using h1.symm
  have hγι : gam σ Y.J H.x (algebraMap F E q) * H.ι = H.ι := by
    rw [gam, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hNι, smul_zero, sub_zero]
  refine ⟨γ, Subgroup.subset_closure ⟨?_, fun z => ⟨0, ?_⟩⟩,
    Subgroup.mem_subgroupOf.mpr (MonoidHom.mem_range.mpr ⟨gamGL σ Y.J H.x hxx (algebraMap F E q), rfl⟩),
    fun u hu => ⟨?_, ?_⟩⟩
  · rw [hγv, hxx', mul_zero, zero_smul, sub_zero]
  · have hm : incM F (gam σ Y.J H.x (algebraMap F E q)) * incM F H.ι = incM F H.ι := by
      simp only [incM]; rw [← Matrix.map_mul, hγι]
    rw [zero_smul, add_zero, Matrix.mulVec_mulVec, hmat, hm]
  · funext j
    obtain ⟨a, ha⟩ := (unip_spec hu).2 (Pi.single j 1)
    have h0 : fA σ Y.J (mat u *ᵥ (incM F H.ι *ᵥ Pi.single j 1)) (incV F H.x) = 0 := by
      rw [ha, fA_add_left, fA_smul_left, hxx', mul_zero, add_zero, single_eq_incV, incM_mulVec_incV, fA_incV,
        (horth _).1, map_zero]
    simp only [coA]
    rw [mat_mul', ← Matrix.mulVec_mulVec, hγv, h0, mul_zero, zero_smul, sub_zero]
  · have h1 := fA_unitary σ u (incV F H.y) (incV F H.x)
    rw [(unip_spec hu).1, fA_incV, form_swap σ hσ Y.J hJ H.x H.y, hxy, map_one, map_neg, map_one] at h1
    simp only [coC]
    rw [mat_mul', ← Matrix.mulVec_mulVec, hγv, fA_sub_left, fA_smul_left, h1, hxy', hq]
    ring
