import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemImLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinatesInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHyperbolicPlaneRestrictedForm

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipChart

open GlobalTheory.ThK.UnipDom GlobalTheory.ThK.UnipDom.MatEq GlobalTheory.ThK.UnipDom.Inverse

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def pVec {d b : ℕ} (H : Plane E d b) (β : Fin b → AE F E) (c : AE F E) : Fin d → AE F E :=
  incM F H.ι *ᵥ β + c • incV F H.x

def uMat (σ : E →ₐ[F] E) {d b : ℕ} (J : Matrix (Fin d) (Fin d) E) (H : Plane E d b) (β : Fin b → AE F E)
    (c : AE F E) : Matrix (Fin d) (Fin d) (AE F E) :=
  1 + Matrix.vecMulVec (pVec H β c) (incM F J *ᵥ fun i => cA σ (incV F H.x i)) -
    Matrix.vecMulVec (incV F H.x) (incM F J *ᵥ fun i => cA σ ((incM F H.ι *ᵥ β) i))

theorem uMat_mulVec (σ : E →ₐ[F] E) {d b : ℕ} (J : Matrix (Fin d) (Fin d) E) (H : Plane E d b)
    (β : Fin b → AE F E) (c : AE F E) (v : Fin d → AE F E) :
    uMat σ J H β c *ᵥ v = v + fA σ J v (incV F H.x) • pVec H β c - fA σ J v (incM F H.ι *ᵥ β) • incV F H.x := by
  simp only [uMat, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, fA]
  funext i
  simp [dotProduct_comm, mul_comm]

theorem fA_flip {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (v w : Fin n → AE F E) : fA σ J w v = cA σ (fA σ J v w) := by
  have hJ' : ∀ i k, cA σ (incM F J i k) = incM F J k i := by
    intro i k; simp [incM, GlobalTheory.ThK.UnipDom.Inverse.cA_inclR, hJ]
  simp only [fA, dotProduct, Matrix.mulVec, map_sum, map_mul, GlobalTheory.ThK.UnipDom.Inverse.cA_cA hσ, hJ', Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem cA_incM_mulVec (σ : E →ₐ[F] E) {m n : ℕ} (N : Matrix (Fin m) (Fin n) E) (v : Fin n → AE F E) :
    (fun i => cA σ ((incM F N *ᵥ v) i)) = incM F (N.map σ) *ᵥ fun i => cA σ (v i) := by
  funext i
  simp [incM, Matrix.mulVec, dotProduct, map_sum, map_mul, GlobalTheory.ThK.UnipDom.Inverse.cA_inclR]

theorem fA_incM_incM (σ : E →ₐ[F] E) {d b : ℕ} (J : Matrix (Fin d) (Fin d) E) (N : Matrix (Fin d) (Fin b) E)
    (β γ : Fin b → AE F E) : fA σ J (incM F N *ᵥ β) (incM F N *ᵥ γ) = fA σ (Nᵀ * J * N.map σ) β γ := by
  simp only [fA, cA_incM_mulVec]
  rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 2
  simp [incM, Matrix.map_mul, Matrix.transpose_map, Matrix.mul_assoc]

theorem fA_sub_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w w' : Fin n → AE F E) :
    fA σ J v (w - w') = fA σ J v w - fA σ J v w' := by
  have : (fun i => cA σ ((w - w') i)) = (fun i => cA σ (w i)) - (fun i => cA σ (w' i)) := by
    funext i; simp
  simp only [fA, this, Matrix.mulVec_sub, dotProduct_sub]

theorem fA_neg_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → AE F E) :
    fA σ J v (-w) = -fA σ J v w := by
  have : (fun i => cA σ ((-w) i)) = -(fun i => cA σ (w i)) := by
    funext i; simp
  simp only [fA, this, Matrix.mulVec_neg, dotProduct_neg]

section Plane

variable {σ : E →ₐ[F] E} {d b : ℕ} {J : Matrix (Fin d) (Fin d) E} {H : Plane E d b}

theorem fA_iota_left (v : Fin d → E) (hv : ∀ u, form σ J (H.ι *ᵥ u) v = 0) (z : Fin b → AE F E) :
    fA σ J (incM F H.ι *ᵥ z) (incV F v) = 0 := by
  rw [fA_mulVec_left]
  have : ∀ j, fA σ J (incM F H.ι *ᵥ Pi.single j 1) (incV F v) = 0 := by
    intro j
    rw [Additive.single_eq_incV, Additive.incM_mulVec_incV, Additive.fA_incV, hv, map_zero]
  simp only [this]
  simp

structure Hyp (σ : E →ₐ[F] E) (J : Matrix (Fin d) (Fin d) E) (J₁ : Matrix (Fin b) (Fin b) E) (H : Plane E d b) : Prop where
  invol : ∀ e, σ (σ e) = e
  herm : ∀ i j, σ (J j i) = J i j
  xx : form σ J H.x H.x = 0
  yy : form σ J H.y H.y = 0
  xy : form σ J H.x H.y = 1
  orth : ∀ u, form σ J (H.ι *ᵥ u) H.x = 0 ∧ form σ J (H.ι *ᵥ u) H.y = 0
  gram : H.ιᵀ * J * H.ι.map σ = J₁

variable {J₁ : Matrix (Fin b) (Fin b) E}

theorem Hyp.ix (h : Hyp σ J J₁ H) (z : Fin b → AE F E) : fA σ J (incM F H.ι *ᵥ z) (incV F H.x) = 0 :=
  fA_iota_left _ (fun u => (h.orth u).1) z

theorem Hyp.iy (h : Hyp σ J J₁ H) (z : Fin b → AE F E) : fA σ J (incM F H.ι *ᵥ z) (incV F H.y) = 0 :=
  fA_iota_left _ (fun u => (h.orth u).2) z

theorem Hyp.xi (h : Hyp σ J J₁ H) (z : Fin b → AE F E) : fA σ J (incV F H.x) (incM F H.ι *ᵥ z) = 0 := by
  rw [fA_flip h.invol h.herm, h.ix, map_zero]

theorem Hyp.yi (h : Hyp σ J J₁ H) (z : Fin b → AE F E) : fA σ J (incV F H.y) (incM F H.ι *ᵥ z) = 0 := by
  rw [fA_flip h.invol h.herm, h.iy, map_zero]

theorem Hyp.fxx (h : Hyp σ J J₁ H) : fA σ J (incV F H.x) (incV F H.x) = 0 := by
  rw [Additive.fA_incV, h.xx, map_zero]

theorem Hyp.fyy (h : Hyp σ J J₁ H) : fA σ J (incV F H.y) (incV F H.y) = 0 := by
  rw [Additive.fA_incV, h.yy, map_zero]

theorem Hyp.fxy (h : Hyp σ J J₁ H) : fA σ J (incV F H.x) (incV F H.y) = 1 := by
  rw [Additive.fA_incV, h.xy, map_one]

theorem Hyp.fyx (h : Hyp σ J J₁ H) : fA σ J (incV F H.y) (incV F H.x) = 1 := by
  rw [fA_flip h.invol h.herm, h.fxy, map_one]

theorem Hyp.ii (h : Hyp σ J J₁ H) (β γ : Fin b → AE F E) :
    fA σ J (incM F H.ι *ᵥ β) (incM F H.ι *ᵥ γ) = fA σ J₁ β γ := by
  rw [fA_incM_incM, h.gram]

theorem fA_betaOf (hσ : ∀ e, σ (σ e) = e) (hJ₁ : ∀ i j, σ (J₁ j i) = J₁ i j) (hdet : IsUnit J₁.det)
    (a z : Fin b → AE F E) : fA σ J₁ (GlobalTheory.UnipConj.betaOf σ J₁ a) z = -cA σ (z ⬝ᵥ a) := by
  have hb : GlobalTheory.UnipConj.betaOf σ J₁ a = -(incM F (J₁⁻¹.map σ) *ᵥ fun i => cA σ (a i)) := by
    rw [← cA_incM_mulVec]
    funext i
    simp [GlobalTheory.UnipConj.betaOf]
  have hT : (J₁⁻¹.map σ)ᵀ * J₁ = 1 := by
    have h1 : J₁ * J₁⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
    have h2 : J₁.map σ * J₁⁻¹.map σ = 1 := by
      have := congrArg (RingHom.mapMatrix (σ : E →+* E)) h1
      rw [map_mul, map_one] at this
      exact this
    have h3 : (J₁.map σ)ᵀ = J₁ := by
      ext i j; simp [hJ₁]
    have h4 := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, h3, Matrix.transpose_one] at h4
    exact h4
  rw [hb, fA, neg_dotProduct, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have h5 : (incM F (J₁⁻¹.map σ))ᵀ * incM F J₁ = 1 := by
    rw [incM, incM, ← Matrix.transpose_map, ← Matrix.map_mul, hT]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [h5, Matrix.one_mulVec, dotProduct_comm]
  simp [dotProduct, map_sum, map_mul]

end Plane

example : Hyp (AlgHom.id ℚ ℚ) !![0, 1; 1, 0] (0 : Matrix (Fin 0) (Fin 0) ℚ)
    (⟨![1, 0], ![0, 1], 0, 1⟩ : Plane ℚ 2 0) := by
  refine ⟨fun e => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> rfl
  · simp [form, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  · simp [form, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  · simp [form, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  · intro u; simp [form]
  · ext i; exact i.elim0

section UMat

variable {σ : E →ₐ[F] E} {d b : ℕ} {J : Matrix (Fin d) (Fin d) E} {J₁ : Matrix (Fin b) (Fin b) E} {H : Plane E d b}

theorem Hyp.u_x (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) :
    uMat σ J H β c *ᵥ incV F H.x = incV F H.x := by
  rw [uMat_mulVec, h.fxx, h.xi, zero_smul, zero_smul, add_zero, sub_zero]

theorem Hyp.u_i (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) (z : Fin b → AE F E) :
    uMat σ J H β c *ᵥ (incM F H.ι *ᵥ z) =
      incM F H.ι *ᵥ z - fA σ J (incM F H.ι *ᵥ z) (incM F H.ι *ᵥ β) • incV F H.x := by
  rw [uMat_mulVec, h.ix, zero_smul, add_zero]

theorem Hyp.u_y (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) :
    uMat σ J H β c *ᵥ incV F H.y = incV F H.y + pVec H β c := by
  rw [uMat_mulVec, h.fyx, h.yi, one_smul, zero_smul, sub_zero]

theorem Hyp.px (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) : fA σ J (pVec H β c) (incV F H.x) = 0 := by
  rw [pVec, fA_add_left, fA_smul_left, h.ix, h.fxx, mul_zero, add_zero]

theorem Hyp.xp (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) : fA σ J (incV F H.x) (pVec H β c) = 0 := by
  rw [pVec, fA_add_right, fA_smul_right, h.xi, h.fxx, mul_zero, add_zero]

theorem Hyp.pi (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) (γ : Fin b → AE F E) :
    fA σ J (pVec H β c) (incM F H.ι *ᵥ γ) = fA σ J₁ β γ := by
  rw [pVec, fA_add_left, fA_smul_left, h.xi, h.ii, mul_zero, add_zero]

theorem Hyp.vp (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) (v : Fin d → AE F E) :
    fA σ J v (pVec H β c) = fA σ J v (incM F H.ι *ᵥ β) + cA σ c * fA σ J v (incV F H.x) := by
  rw [pVec, fA_add_right, fA_smul_right]

theorem Hyp.pw (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) (w : Fin d → AE F E) :
    fA σ J (pVec H β c) w = cA σ (fA σ J w (incM F H.ι *ᵥ β)) + c * cA σ (fA σ J w (incV F H.x)) := by
  rw [pVec, fA_add_left, fA_smul_left, fA_flip h.invol h.herm w (incM F H.ι *ᵥ β),
    fA_flip h.invol h.herm w (incV F H.x)]

theorem Hyp.pp (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) :
    fA σ J (pVec H β c) (pVec H β c) = fA σ J₁ β β := by
  rw [h.vp, h.pi, h.px, mul_zero, add_zero]

theorem Hyp.u_form (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) (hc : c + cA σ c = -fA σ J₁ β β)
    (v w : Fin d → AE F E) : fA σ J (uMat σ J H β c *ᵥ v) (uMat σ J H β c *ᵥ w) = fA σ J v w := by
  rw [uMat_mulVec, uMat_mulVec]
  simp only [fA_add_left, fA_sub_left, fA_smul_left, fA_add_right, fA_sub_right, fA_smul_right]
  simp only [h.pp]
  simp only [h.vp, h.pw, h.px, h.xp, h.fxx, h.ix, h.xi, fA_flip h.invol h.herm w (incV F H.x), map_zero]
  linear_combination (fA σ J v (incV F H.x) * cA σ (fA σ J w (incV F H.x))) * hc

theorem fA_mat (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin n) (Fin n) (AE F E))
    (v w : Fin n → AE F E) :
    fA σ J (M *ᵥ v) (M *ᵥ w) = v ⬝ᵥ ((Mᵀ * incM F J * M.map (cA σ)) *ᵥ fun i => cA σ (w i)) := by
  have hc : (fun i => cA σ ((M *ᵥ w) i)) = M.map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom M w i
  unfold fA
  rw [hc, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem unitary_of_fA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (M : Matrix (Fin n) (Fin n) (AE F E))
    (hM : ∀ v w, fA σ J (M *ᵥ v) (M *ᵥ w) = fA σ J v w) : Mᵀ * incM F J * M.map (cA σ) = incM F J := by
  have hs : ∀ l : Fin n, (fun i => cA σ ((Pi.single l (1 : AE F E) : Fin n → AE F E) i)) = Pi.single l 1 := by
    intro l; funext i
    by_cases hi : i = l
    · subst hi; simp
    · simp [hi]
  ext k l
  have := hM (Pi.single k 1) (Pi.single l 1)
  rw [fA_mat] at this
  simp only [fA, hs, single_dotProduct, one_mul, Matrix.mulVec_single_one] at this
  simpa using this

theorem Hyp.u_fx (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) (v : Fin d → AE F E) :
    fA σ J (uMat σ J H β c *ᵥ v) (incV F H.x) = fA σ J v (incV F H.x) := by
  rw [uMat_mulVec, fA_sub_left, fA_add_left, fA_smul_left, fA_smul_left, h.px, h.fxx]
  ring

theorem Hyp.u_fi (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) (v : Fin d → AE F E) (γ : Fin b → AE F E) :
    fA σ J (uMat σ J H β c *ᵥ v) (incM F H.ι *ᵥ γ) =
      fA σ J v (incM F H.ι *ᵥ γ) + fA σ J v (incV F H.x) * fA σ J₁ β γ := by
  rw [uMat_mulVec, fA_sub_left, fA_add_left, fA_smul_left, fA_smul_left, h.pi, h.xi]
  ring

theorem Hyp.u_mul_u (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) (hc : c + cA σ c = -fA σ J₁ β β) :
    uMat σ J H β c * uMat σ J H (-β) (cA σ c) = 1 := by
  have key : ∀ v, uMat σ J H β c *ᵥ (uMat σ J H (-β) (cA σ c) *ᵥ v) = v := by
    intro v
    rw [uMat_mulVec σ J H β c, h.u_fx, h.u_fi]
    rw [uMat_mulVec, pVec, pVec, Matrix.mulVec_neg, fA_neg_right]
    have h1 : fA σ J₁ (-β) β = -fA σ J₁ β β := by simp [fA, neg_dotProduct]
    rw [h1, show cA σ c = -fA σ J₁ β β - c by linear_combination hc]
    simp only [smul_add, smul_sub, smul_neg, add_smul, sub_smul, neg_smul, smul_smul, mul_neg, neg_neg]
    abel
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec] at this
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

end UMat

section Elt

variable {σ : E →ₐ[F] E} {d b : ℕ} {J : Matrix (Fin d) (Fin d) E} {J₁ : Matrix (Fin b) (Fin b) E} {H : Plane E d b}

theorem fA₁_neg_neg (σ : E →ₐ[F] E) {n : ℕ} (J₁ : Matrix (Fin n) (Fin n) E) (β : Fin n → AE F E) :
    fA σ J₁ (-β) (-β) = fA σ J₁ β β := by
  rw [fA_neg_right]; simp [fA, neg_dotProduct]

theorem Hyp.hc_inv (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) (hc : c + cA σ c = -fA σ J₁ β β) :
    cA σ c + cA σ (cA σ c) = -fA σ J₁ (-β) (-β) := by
  rw [cA_cA h.invol, fA₁_neg_neg]; linear_combination hc

theorem Hyp.u_mul_u' (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) (hc : c + cA σ c = -fA σ J₁ β β) :
    uMat σ J H (-β) (cA σ c) * uMat σ J H β c = 1 := by
  have := h.u_mul_u (-β) (cA σ c) (h.hc_inv β c hc)
  rwa [neg_neg, cA_cA h.invol] at this

def uElt (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) (hc : c + cA σ c = -fA σ J₁ β β) : UA σ J :=
  ⟨⟨uMat σ J H β c, uMat σ J H (-β) (cA σ c), h.u_mul_u β c hc, h.u_mul_u' β c hc⟩,
    unitary_of_fA σ J _ (h.u_form β c hc)⟩

theorem mat_uElt (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) (hc : c + cA σ c = -fA σ J₁ β β) :
    mat (uElt h β c hc) = uMat σ J H β c := rfl

theorem inv_uElt (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) (hc : c + cA σ c = -fA σ J₁ β β) :
    Units.val ((uElt h β c hc).1⁻¹) = uMat σ J H (-β) (cA σ c) := rfl

theorem uElt_mem {W : Spc F E d} (h : Hyp σ W.J J₁ H) (β : Fin b → AE F E) (c : AE F E)
    (hc : c + cA σ c = -fA σ J₁ β β) : uElt h β c hc ∈ unip σ W H := by
  refine Subgroup.subset_closure ⟨h.u_x β c, fun z => ⟨-fA σ W.J (incM F H.ι *ᵥ z) (incM F H.ι *ᵥ β), ?_⟩⟩
  rw [mat_uElt, h.u_i, neg_smul, sub_eq_add_neg]

theorem coA_uElt (h : Hyp σ J J₁ H) (hJ₁ : ∀ i j, σ (J₁ j i) = J₁ i j) (hdet₁ : IsUnit J₁.det)
    (a : Fin b → AE F E) (c : AE F E) (hc : c + cA σ c = -fA σ J₁ (GlobalTheory.UnipConj.betaOf σ J₁ a) (GlobalTheory.UnipConj.betaOf σ J₁ a)) :
    coA σ J H (uElt h _ c hc) = a := by
  funext j
  simp only [coA, mat_uElt]
  rw [h.u_i, fA_sub_left, fA_smul_left, h.iy, h.fxy, h.ii, fA_flip h.invol hJ₁,
    fA_betaOf h.invol hJ₁ hdet₁, map_neg, cA_cA h.invol]
  simp [single_dotProduct]

theorem coC_uElt (h : Hyp σ J J₁ H) (β : Fin b → AE F E) (c : AE F E) (hc : c + cA σ c = -fA σ J₁ β β) :
    coC σ J H (uElt h β c hc) = c := by
  simp only [coC, mat_uElt]
  rw [h.u_y, fA_add_left, pVec, fA_add_left, fA_smul_left, h.fyy, h.iy, h.fxy]
  ring

end Elt

section Span

variable {σ : E →ₐ[F] E} {d b : ℕ} {J : Matrix (Fin d) (Fin d) E} {J₁ : Matrix (Fin b) (Fin b) E} {H : Plane E d b}

theorem Hyp.eq_zero (h : Hyp σ J J₁ H)
    (hspan : ∀ w : Fin d → E, ∃ (s t : E) (u : Fin b → E), w = s • H.x + H.ι *ᵥ u + t • H.y)
    (hdet : IsUnit J.det) (v : Fin d → AE F E) (h1 : fA σ J v (incV F H.x) = 0)
    (h2 : fA σ J v (incV F H.y) = 0) (h3 : ∀ z, fA σ J v (incM F H.ι *ᵥ z) = 0) : v = 0 := by
  have hall : ∀ w : Fin d → E, fA σ J v (incV F w) = 0 := by
    intro w
    obtain ⟨s, t, u, rfl⟩ := hspan w
    rw [incV_add, incV_add, incV_smul, incV_smul, ← Additive.incM_mulVec_incV, fA_add_right, fA_add_right,
      fA_smul_right, fA_smul_right, h1, h2, h3]
    simp
  have hJv : incM F Jᵀ *ᵥ v = 0 := by
    have e : (fun l => fA σ J v (incV F (Pi.single l 1))) = incM F Jᵀ *ᵥ v := by
      funext l
      simp [fA, incV, incM, dotProduct, Matrix.mulVec, Additive.cA_inclR, Pi.single_apply, mul_comm]
    rw [← e]
    funext l
    exact hall _
  have hT : IsUnit Jᵀ.det := by rwa [Matrix.det_transpose]
  calc v = (incM F (Jᵀ)⁻¹ * incM F Jᵀ) *ᵥ v := by
        rw [incM, incM, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hT,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hJv, Matrix.mulVec_zero]

theorem mat_ext (hspan : ∀ w : Fin d → E, ∃ (s t : E) (u : Fin b → E), w = s • H.x + H.ι *ᵥ u + t • H.y)
    (M N : Matrix (Fin d) (Fin d) (AE F E)) (hx : M *ᵥ incV F H.x = N *ᵥ incV F H.x)
    (hy : M *ᵥ incV F H.y = N *ᵥ incV F H.y)
    (hi : ∀ z : Fin b → AE F E, M *ᵥ (incM F H.ι *ᵥ z) = N *ᵥ (incM F H.ι *ᵥ z)) : M = N := by
  have hall : ∀ w : Fin d → E, M *ᵥ incV F w = N *ᵥ incV F w := by
    intro w
    obtain ⟨s, t, u, rfl⟩ := hspan w
    rw [incV_add, incV_add, incV_smul, incV_smul, ← Additive.incM_mulVec_incV]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hx, hy, hi]
  ext r i
  have := congrFun (hall (Pi.single i 1)) r
  rw [← Additive.single_eq_incV, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
  simpa using this

end Span

section Shape

variable {σ : E →ₐ[F] E} {d b : ℕ} {W : Spc F E d} {J₁ : Matrix (Fin b) (Fin b) E} {H : Plane E d b}

theorem Hyp.unip_iota (h : Hyp σ W.J J₁ H) {n : UA σ W.J} (hn : n ∈ unip σ W H) (z : Fin b → AE F E) :
    mat n *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + (z ⬝ᵥ coA σ W.J H n) • incV F H.x := by
  obtain ⟨e, he⟩ := (Additive.unip_spec hn).2 z
  have h1 : fA σ W.J (mat n *ᵥ (incM F H.ι *ᵥ z)) (incV F H.y) = e := by
    rw [he, fA_add_left, fA_smul_left, h.iy, h.fxy]; ring
  have h2 : fA σ W.J (mat n *ᵥ (incM F H.ι *ᵥ z)) (incV F H.y) = z ⬝ᵥ coA σ W.J H n := by
    rw [Matrix.mulVec_mulVec, fA_mulVec_left]
    congr 1
    funext j
    simp only [coA, Matrix.mulVec_mulVec]
  rw [he, ← h1, h2]

theorem Hyp.unip_y (h : Hyp σ W.J J₁ H)
    (hspan : ∀ w : Fin d → E, ∃ (s t : E) (u : Fin b → E), w = s • H.x + H.ι *ᵥ u + t • H.y)
    (hdet : IsUnit W.J.det) (hJ₁ : ∀ i j, σ (J₁ j i) = J₁ i j) (hdet₁ : IsUnit J₁.det)
    {n : UA σ W.J} (hn : n ∈ unip σ W H) :
    mat n *ᵥ incV F H.y = incV F H.y + pVec H (GlobalTheory.UnipConj.betaOf σ J₁ (coA σ W.J H n)) (coC σ W.J H n) := by
  have hnx := (Additive.unip_spec hn).1
  have hyx : fA σ W.J (mat n *ᵥ incV F H.y) (incV F H.x) = 1 := by
    conv_lhs => rw [← hnx]
    rw [fA_unitary, h.fyx]
  apply sub_eq_zero.mp
  apply h.eq_zero hspan hdet
  · rw [fA_sub_left, hyx, fA_add_left, h.fyx, h.px]; ring
  · rw [fA_sub_left, fA_add_left, h.fyy, pVec, fA_add_left, fA_smul_left, h.iy, h.fxy]
    simp [coC]
  · intro z
    have e1 : incM F H.ι *ᵥ z = mat n *ᵥ (incM F H.ι *ᵥ z) - (z ⬝ᵥ coA σ W.J H n) • incV F H.x := by
      rw [h.unip_iota hn]; abel
    have : fA σ W.J (mat n *ᵥ incV F H.y) (incM F H.ι *ᵥ z) = -cA σ (z ⬝ᵥ coA σ W.J H n) := by
      rw [e1, fA_sub_right, fA_smul_right, fA_unitary, h.yi, hyx]; ring
    rw [fA_sub_left, fA_add_left, h.yi, h.pi, fA_betaOf h.invol hJ₁ hdet₁, this]
    ring

theorem Hyp.unip_c (h : Hyp σ W.J J₁ H)
    (hspan : ∀ w : Fin d → E, ∃ (s t : E) (u : Fin b → E), w = s • H.x + H.ι *ᵥ u + t • H.y)
    (hdet : IsUnit W.J.det) (hJ₁ : ∀ i j, σ (J₁ j i) = J₁ i j) (hdet₁ : IsUnit J₁.det)
    {n : UA σ W.J} (hn : n ∈ unip σ W H) :
    coC σ W.J H n + cA σ (coC σ W.J H n) =
      -fA σ J₁ (GlobalTheory.UnipConj.betaOf σ J₁ (coA σ W.J H n)) (GlobalTheory.UnipConj.betaOf σ J₁ (coA σ W.J H n)) := by
  have := fA_unitary n (incV F H.y) (incV F H.y)
  rw [h.unip_y hspan hdet hJ₁ hdet₁ hn, h.fyy, fA_add_left, fA_add_right, fA_add_right, h.fyy, h.vp, h.pw, h.pp] at this
  simp only [h.yi, h.fyx, map_zero, map_one] at this
  linear_combination this

end Shape

section Adapted

open GlobalTheory.LeviElem in

theorem span_det (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) (B : Base F E) {b : ℕ} {Y : Spc F E (b + 2)}
    {Y₁ : Spc F E b} (herm : ∀ i j, σ (Y.J j i) = Y.J i j) {H : Plane E (b + 2) b} {i₀ i₁ : ℕ}
    (hA : H.IsAdapted σ B Y Y₁ i₀ i₁) (hdet₁ : Y₁.J.det ≠ 0) :
    (∀ w : Fin (b + 2) → E, ∃ (s t : E) (u : Fin b → E), w = s • H.x + H.ι *ᵥ u + t • H.y) ∧ IsUnit Y.J.det := by
  set P := Matrix.fromCols H.ι (cols2 H.x H.y) with hP
  have hK : Pᵀ * Y.J * P.map σ = Matrix.fromBlocks Y₁.J 0 0 swap2 := gram_block σ hσ B herm hA
  set K : Matrix (Fin b ⊕ Fin 2) (Fin b ⊕ Fin 2) E := Matrix.fromBlocks Y₁.J 0 0 swap2 with hKdef
  have hKdet : IsUnit K.det := by
    rw [hKdef, Matrix.det_fromBlocks_zero₂₁]
    simp [swap2, Matrix.det_fin_two, hdet₁]
  set X := Y.J * P.map σ * K⁻¹ with hX
  have hPX : Pᵀ * X = 1 := by
    rw [hX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hK, Matrix.mul_nonsing_inv _ hKdet]
  have hXP : X * Pᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hPX
  have hXtP : Xᵀ * P = 1 := by
    have := congrArg Matrix.transpose hPX
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have hPXt : P * Xᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 hXtP
  refine ⟨fun w => ?_, ?_⟩
  · refine ⟨(Xᵀ *ᵥ w) (Sum.inr 0), (Xᵀ *ᵥ w) (Sum.inr 1), fun j => (Xᵀ *ᵥ w) (Sum.inl j), ?_⟩
    have hw : w = P *ᵥ (Xᵀ *ᵥ w) := by rw [Matrix.mulVec_mulVec, hPXt, Matrix.one_mulVec]
    conv_lhs => rw [hw]
    funext i
    simp [hP, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromCols, cols2, Fin.sum_univ_two]
    ring
  · have h1 : Y.J * (P.map σ * K⁻¹ * Pᵀ) = 1 := by
      rw [← hXP, hX]; simp only [Matrix.mul_assoc]
    exact Matrix.isUnit_det_of_right_inverse h1

end Adapted

section Cont

variable {σ : E →ₐ[F] E} {d b : ℕ}

theorem cont_cA (σ : E →ₐ[F] E) : Continuous (cA σ : AE F E → AE F E) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap

theorem cont_fA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Continuous fun p : (Fin n → AE F E) × (Fin n → AE F E) => fA σ J p.1 p.2 := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hcA := cont_cA σ
  unfold fA
  refine continuous_fst.dotProduct (continuous_const.matrix_mulVec (continuous_pi fun i => ?_))
  exact hcA.comp ((continuous_apply i).comp continuous_snd)

theorem cont_uMat (σ : E →ₐ[F] E) (J : Matrix (Fin d) (Fin d) E) (H : Plane E d b) {X : Type} [TopologicalSpace X]
    {f : X → Fin b → AE F E} {g : X → AE F E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => uMat σ J H (f x) (g x) := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hcA := cont_cA σ
  unfold uMat pVec
  have h1 : Continuous fun x => incM F H.ι *ᵥ f x + g x • incV F H.x :=
    (continuous_const.matrix_mulVec hf).add (hg.smul continuous_const)
  have h2 : Continuous fun x => incM F J *ᵥ fun i => cA σ ((incM F H.ι *ᵥ f x) i) :=
    continuous_const.matrix_mulVec (continuous_pi fun i =>
      hcA.comp ((continuous_apply i).comp (continuous_const.matrix_mulVec hf)))
  exact (continuous_const.add (h1.matrix_vecMulVec continuous_const)).sub
    ((continuous_const (y := incV F H.x)).matrix_vecMulVec h2)

end Cont

open GlobalTheory.LeviElem in

theorem unip_homeo_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∃ χ : unip σ G.V H ≃ₜ (Fin b → AE F E) × GlobalTheory.UnipConj.imLine σ, ∀ n,
      (χ n).1 = GlobalTheory.ThK.UnipDom.coA σ G.V.J H n ∧ ((χ n).2 : AE F E) = GlobalTheory.UnipConj.coT σ G.V.J H n := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ z, σ (σ z) = z := fun z => (B.emb w).1.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hdet₁ : G₁.V.J.det ≠ 0 := by
    have h := det_ne_of_sig _ (hG₁.hV.sig w)
    intro h0
    apply h
    have : (G₁.V.J.map (B.emb w).1).det = (B.emb w).1 G₁.V.J.det := (RingHom.map_det (B.emb w).1 _).symm
    rw [this, h0, map_zero]
  obtain ⟨hspan, hdet⟩ := span_det σ hσ B hG.hV.herm hC.hH hdet₁
  have h : Hyp σ G.V.J G₁.V.J H := ⟨hσ, hG.hV.herm, hC.hH.xx, hC.hH.yy, hC.hH.xy, hC.hH.orth, hC.hH.gram⟩
  have hJ₁ := hG₁.hV.herm
  have hu₁ : IsUnit G₁.V.J.det := isUnit_iff_ne_zero.mpr hdet₁
  have hcA := cont_cA σ
  set J₁ := G₁.V.J with hJ₁def
  obtain ⟨β, hβdef⟩ : ∃ f : (Fin b → AE F E) → Fin b → AE F E, f = GlobalTheory.UnipConj.betaOf σ J₁ := ⟨_, rfl⟩
  obtain ⟨cOf, hcOf⟩ : ∃ f : (Fin b → AE F E) × GlobalTheory.UnipConj.imLine σ → AE F E,
      f = fun p => ⅟(2 : AF F) • ((p.2 : AE F E) - fA σ J₁ (β p.1) (β p.1)) := ⟨_, rfl⟩
  have hreal : ∀ γ, cA σ (fA σ J₁ γ γ) = fA σ J₁ γ γ := fun γ => (fA_flip hσ hJ₁ γ γ).symm
  have hc : ∀ p, cOf p + cA σ (cOf p) = -fA σ J₁ (β p.1) (β p.1) := by
    intro p
    have ht := GlobalTheory.UnipConj.mem_imLine.mp p.2.2
    simp only [hcOf, map_smul, map_sub, hreal]
    rw [← smul_add, show (p.2 : AE F E) - fA σ J₁ (β p.1) (β p.1) + (cA σ (p.2 : AE F E) - fA σ J₁ (β p.1) (β p.1)) =
      (2 : AF F) • (-fA σ J₁ (β p.1) (β p.1)) by rw [two_smul]; linear_combination ht]
    rw [smul_smul, invOf_mul_self, one_smul]
  have hct : ∀ p, cOf p - cA σ (cOf p) = p.2 := by
    intro p
    have ht := GlobalTheory.UnipConj.mem_imLine.mp p.2.2
    simp only [hcOf, map_smul, map_sub, hreal]
    rw [← smul_sub, show (p.2 : AE F E) - fA σ J₁ (β p.1) (β p.1) - (cA σ (p.2 : AE F E) - fA σ J₁ (β p.1) (β p.1)) =
      (2 : AF F) • (p.2 : AE F E) by rw [two_smul]; linear_combination -ht]
    rw [smul_smul, invOf_mul_self, one_smul]
  have hT : ∀ n : UA σ G.V.J, GlobalTheory.UnipConj.coT σ G.V.J H n ∈ GlobalTheory.UnipConj.imLine σ := by
    intro n
    rw [GlobalTheory.UnipConj.mem_imLine]
    simp only [GlobalTheory.UnipConj.coT, map_sub, cA_cA hσ]
    abel
  let fwd : unip σ G.V H → (Fin b → AE F E) × GlobalTheory.UnipConj.imLine σ :=
    fun n => (coA σ G.V.J H n, ⟨GlobalTheory.UnipConj.coT σ G.V.J H n, hT n⟩)
  obtain ⟨bwdGL, hU⟩ : ∃ U : (Fin b → AE F E) × GlobalTheory.UnipConj.imLine σ → UA σ G.V.J,
      ∀ p, U p = uElt h (β p.1) (cOf p) (hc p) := ⟨_, fun _ => rfl⟩
  have hUmat : ∀ p, mat (bwdGL p) = uMat σ G.V.J H (β p.1) (cOf p) := fun p => by rw [hU, mat_uElt]
  have hUinv : ∀ p, Units.val ((bwdGL p).1⁻¹) = uMat σ G.V.J H (-β p.1) (cA σ (cOf p)) :=
    fun p => by rw [hU, inv_uElt]
  have hUmem : ∀ p, bwdGL p ∈ unip σ G.V H := fun p => by rw [hU]; exact uElt_mem h _ _ _
  let bwd : (Fin b → AE F E) × GlobalTheory.UnipConj.imLine σ → unip σ G.V H :=
    fun p => ⟨bwdGL p, hUmem p⟩
  have hl : ∀ n, bwd (fwd n) = n := by
    intro n
    have hn := n.2
    have hcn : cOf (fwd n) = coC σ G.V.J H n := by
      have := h.unip_c hspan hdet hJ₁ hu₁ hn
      simp only [hcOf, fwd, GlobalTheory.UnipConj.coT, hβdef]
      rw [show coC σ G.V.J H n - cA σ (coC σ G.V.J H n) - fA σ J₁ (GlobalTheory.UnipConj.betaOf σ J₁ (coA σ G.V.J H n)) (GlobalTheory.UnipConj.betaOf σ J₁ (coA σ G.V.J H n)) =
        (2 : AF F) • coC σ G.V.J H n by rw [two_smul]; linear_combination (-1 : AE F E) * this]
      rw [smul_smul, invOf_mul_self, one_smul]
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    show mat (bwdGL (fwd n)) = mat (n : UA σ G.V.J)
    rw [hUmat]
    show uMat σ G.V.J H (β (coA σ G.V.J H n)) (cOf (fwd n)) = mat (n : UA σ G.V.J)
    rw [hcn, hβdef]
    symm
    apply mat_ext hspan
    · rw [(Additive.unip_spec hn).1, h.u_x]
    · rw [h.unip_y hspan hdet hJ₁ hu₁ hn, h.u_y]
    · intro z
      rw [h.unip_iota hn, h.u_i, h.ii, fA_flip hσ hJ₁, fA_betaOf hσ hJ₁ hu₁, map_neg, cA_cA hσ, neg_smul,
        sub_neg_eq_add]
  have hr : ∀ p, fwd (bwd p) = p := by
    intro p
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show coA σ G.V.J H (bwdGL p) = p.1
      rw [hU]
      subst hβdef
      exact coA_uElt h hJ₁ hu₁ p.1 (cOf p) (hc p)
    show GlobalTheory.UnipConj.coT σ G.V.J H (bwdGL p) = p.2
    simp only [GlobalTheory.UnipConj.coT, hU, coC_uElt]
    exact hct p
  have hmat : Continuous fun n : unip σ G.V H => mat (n : UA σ G.V.J) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hcoA : Continuous fun n : unip σ G.V H => coA σ G.V.J H n := by
    refine continuous_pi fun j => ?_
    exact (cont_fA σ G.V.J).comp ((hmat.matrix_mulVec continuous_const).prodMk continuous_const)
  have hcoC : Continuous fun n : unip σ G.V H => coC σ G.V.J H n :=
    (cont_fA σ G.V.J).comp ((hmat.matrix_mulVec continuous_const).prodMk continuous_const)
  have hfwd : Continuous fwd :=
    hcoA.prodMk ((hcoC.sub (hcA.comp hcoC)).subtype_mk _)
  have hβ : Continuous β := by
    rw [hβdef]
    refine continuous_pi fun i => ?_
    exact (hcA.comp ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id))).neg
  have hcc : Continuous cOf := by
    rw [hcOf]
    have hin : Continuous fun p : (Fin b → AE F E) × GlobalTheory.UnipConj.imLine σ =>
        (p.2 : AE F E) - fA σ J₁ (β p.1) (β p.1) :=
      (continuous_subtype_val.comp continuous_snd).sub
        ((cont_fA σ J₁).comp ((hβ.comp continuous_fst).prodMk (hβ.comp continuous_fst)))
    exact hin.const_smul (⅟(2 : AF F))
  have hm1 : Continuous fun p : (Fin b → AE F E) × GlobalTheory.UnipConj.imLine σ => uMat σ G.V.J H (β p.1) (cOf p) :=
    cont_uMat σ G.V.J H (hβ.comp continuous_fst) hcc
  have hm2 : Continuous fun p : (Fin b → AE F E) × GlobalTheory.UnipConj.imLine σ => uMat σ G.V.J H (-β p.1) (cA σ (cOf p)) :=
    cont_uMat σ G.V.J H (hβ.comp continuous_fst).neg (hcA.comp hcc)
  have hGL : Continuous fun p => (bwdGL p).1 := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have e : (Units.val ∘ fun p => (bwdGL p).1) = fun p => uMat σ G.V.J H (β p.1) (cOf p) := funext hUmat
      rw [e]; exact hm1
    · have e : (fun p => Units.val ((bwdGL p).1⁻¹)) = fun p => uMat σ G.V.J H (-β p.1) (cA σ (cOf p)) := funext hUinv
      rw [e]; exact hm2
  have hbwd : Continuous bwd := (hGL.subtype_mk _).subtype_mk _
  exact ⟨⟨⟨fwd, bwd, hl, hr⟩, hfwd, hbwd⟩, fun n => ⟨rfl, rfl⟩⟩

end GlobalTheory.UnipChart
