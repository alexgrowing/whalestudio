import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.ThK.UnipDom.Inverse

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨_, _, _, hτ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply τ.injective
  rw [hτ, hτ, star_star]

theorem cA_cA {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, hσ]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem mat_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a b : UA σ J) : mat (a * b) = mat a * mat b := rfl

theorem mat_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mulVec {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (v : Fin n → AE F E) :
    mat g⁻¹ *ᵥ (mat g *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mulVec]

theorem fA_mulVec (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) (v w : Fin n → AE F E) :
    fA σ J (mat g *ᵥ v) (mat g *ᵥ w) = fA σ J v w := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have hc : (fun i => cA σ ((mat g *ᵥ w) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom (mat g) w i
  unfold fA
  rw [hc, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem fA_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    fA σ J (v + v') w = fA σ J v w + fA σ J v' w := by
  simp [fA, add_dotProduct]

theorem fA_sub_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v v' w : Fin n → AE F E) :
    fA σ J (v - v') w = fA σ J v w - fA σ J v' w := by
  simp [fA, sub_dotProduct]

theorem fA_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : AE F E) (v w : Fin n → AE F E) :
    fA σ J (a • v) w = a * fA σ J v w := by
  simp [fA, smul_dotProduct]

theorem fA_incV (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    fA σ J (incV F x) (incV F y) = inclR (F := F) (AF F) (form σ J x y) := by
  simp only [fA, form, incV, incM, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul, cA_inclR]

theorem fA_swap {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → AE F E) :
    fA σ J w v = -cA σ (fA σ J v w) := by
  have hJ' : ∀ i k, cA σ (incM F J i k) = -incM F J k i := by
    intro i k; simp [incM, cA_inclR, hJ]
  simp only [fA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_cA hσ, hJ', Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory.ThK.UnipDom.Inverse

namespace GlobalTheory.ThK.UnipDom.Inverse

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def unipSet (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) : Subgroup (UA σ J) where
  carrier := {u | mat u *ᵥ incV F H'.x = incV F H'.x ∧
    ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}
  one_mem' := ⟨by rw [mat_one, Matrix.one_mulVec], fun z => ⟨0, by rw [mat_one, Matrix.one_mulVec, zero_smul, add_zero]⟩⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [mat_mul, ← Matrix.mulVec_mulVec, hb, ha], fun z => ?_⟩
    obtain ⟨s, hs⟩ := hb' z
    obtain ⟨t, ht⟩ := ha' z
    refine ⟨t + s, ?_⟩
    rw [mat_mul, ← Matrix.mulVec_mulVec, hs, Matrix.mulVec_add, Matrix.mulVec_smul, ht, ha, add_smul]
    abel
  inv_mem' := by
    rintro u ⟨hu, hu'⟩
    have hx : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu]
      exact mat_inv_mulVec u _
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu' z
    refine ⟨-a, ?_⟩
    have h := congrArg (mat u⁻¹ *ᵥ ·) ha
    simp only [mat_inv_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hx] at h
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, ← h]

theorem mem_unipSet {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁} {u : UA σ W.J}
    (hu : u ∈ unip σ W H') : u ∈ unipSet σ W.J H' :=
  (Subgroup.closure_le (unipSet σ W.J H')).mpr (fun _ h => h) hu

theorem coA_coC_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (r s i₀ i₁ : ℕ),
    IsCMExt F E σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ u ∈ unip σ W H', coA σ W.J H' u⁻¹ = -coA σ W.J H' u ∧ coC σ W.J H' u⁻¹ = -cA σ (coC σ W.J H' u) := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' r s i₀ i₁ hCM hW hH u hu
  have hσ := sigma_sigma hCM
  obtain ⟨hx, hz⟩ := mem_unipSet hu
  have hxinv : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := (mem_unipSet (Subgroup.inv_mem _ hu)).1
  have hxy : fA σ W.J (incV F H'.x) (incV F H'.y) = 1 := by rw [fA_incV, hH.xy, map_one]
  refine ⟨funext fun j => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hz (Pi.single j 1)
    have h0 : fA σ W.J (incM F H'.ι *ᵥ Pi.single j 1) (incV F H'.y) = 0 := by
      have : incM F H'.ι *ᵥ (Pi.single j 1 : Fin d₁ → AE F E) = incV F (H'.ι *ᵥ Pi.single j 1) := by
        funext i; simp [incM, incV, Matrix.mulVec_single_one, Matrix.transpose_apply]
      rw [this, fA_incV, (hH.orth _).2, map_zero]
    have hinv : mat u⁻¹ *ᵥ (incM F H'.ι *ᵥ Pi.single j 1) = incM F H'.ι *ᵥ Pi.single j 1 - a • incV F H'.x := by
      have h := congrArg (mat u⁻¹ *ᵥ ·) ha
      simp only [mat_inv_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hxinv] at h
      rw [eq_sub_iff_add_eq, ← h]
    simp only [coA, Pi.neg_apply]
    rw [hinv, ha, fA_sub_left, fA_add_left, fA_smul_left, h0, hxy]
    ring
  · have h := fA_mulVec σ W.J u (mat u⁻¹ *ᵥ incV F H'.y) (incV F H'.y)
    rw [Matrix.mulVec_mulVec, ← mat_mul, mul_inv_cancel, mat_one, Matrix.one_mulVec] at h
    simp only [coC]
    rw [← h, fA_swap hσ hW.skew]

end GlobalTheory.ThK.UnipDom.Inverse
