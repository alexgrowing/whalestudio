import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDualGram

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PlaneProj
open Matrix
variable {A : Type} [CommRing A] {m n k : Type} [Fintype m] [Fintype n] [Fintype k]

theorem mul_vmv (M : Matrix m n A) (u : n → A) (w : k → A) : M * vecMulVec u w = vecMulVec (M *ᵥ u) w := by
  ext i j; simp [vecMulVec_apply, mul_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem vmv_transpose (u : m → A) (w : n → A) : (vecMulVec u w)ᵀ = vecMulVec w u := by
  ext i j; simp [vecMulVec_apply, mul_comm]

theorem vmv_map (c : A →+* A) (u : m → A) (w : n → A) : (vecMulVec u w).map c = vecMulVec (c ∘ u) (c ∘ w) := by
  ext i j; simp [vecMulVec_apply]

theorem vmv_mul_vmv (a : m → A) (b : n → A) (u : n → A) (w : k → A) :
    vecMulVec a b * vecMulVec u w = (b ⬝ᵥ u) • vecMulVec a w := by
  ext i j; simp [vecMulVec_apply, mul_apply, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem vmv_mulVec (u : m → A) (w : n → A) (z : n → A) : vecMulVec u w *ᵥ z = (w ⬝ᵥ z) • u := by
  ext i; simp [vecMulVec_apply, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem proj_core {d d₁ : Type} [Fintype d] [Fintype d₁] [DecidableEq d] [DecidableEq d₁] (c : A →+* A)
    (P J : Matrix d d A) (J₁ : Matrix d₁ d₁ A) (ι : Matrix d d₁ A) (π : Matrix d₁ d A) (x y : d → A)
    (hP : Pᵀ * J * P.map c = J) (hPx : P *ᵥ x = x)
    (hframe : vecMulVec x (J *ᵥ (c ∘ y)) + ι * π - vecMulVec y (J *ᵥ (c ∘ x)) = 1)
    (hgram : ιᵀ * J * ι.map c = J₁) (hιx : (ιᵀ * J) *ᵥ (c ∘ x) = 0) (hxι : x ᵥ* (J * ι.map c) = 0)
    (hxx : x ⬝ᵥ (J *ᵥ (c ∘ x)) = 0) (hJ₁ : IsUnit J₁.det) :
    (π * P * ι)ᵀ * J₁ * (π * P * ι).map c = J₁ ∧ IsUnit (π * P * ι).det ∧
      ∀ z, P *ᵥ (ι *ᵥ z) = ι *ᵥ ((π * P * ι) *ᵥ z) + ((J *ᵥ (c ∘ y)) ⬝ᵥ (P *ᵥ (ι *ᵥ z))) • x := by
  set α : d₁ → A := (J *ᵥ (c ∘ y)) ᵥ* (P * ι) with hα
  have hcx : c ∘ x = P.map c *ᵥ (c ∘ x) := by
    funext i; rw [Function.comp_apply, ← RingHom.map_mulVec, hPx]
  have hxP : x ᵥ* Pᵀ = x := by rw [vecMul_transpose, hPx]
  have hwx : (J *ᵥ (c ∘ x)) ᵥ* (P * ι) = 0 := by
    rw [← mulVec_transpose, transpose_mul, hcx, mulVec_mulVec, mulVec_mulVec,
      show ιᵀ * Pᵀ * J * P.map c = ιᵀ * (Pᵀ * J * P.map c) by simp only [Matrix.mul_assoc], hP, hιx]
  have hιπ : ι * π = 1 - vecMulVec x (J *ᵥ (c ∘ y)) + vecMulVec y (J *ᵥ (c ∘ x)) := by
    rw [← hframe]; abel
  have hιh : ι * (π * P * ι) = P * ι - vecMulVec x α := by
    rw [show ι * (π * P * ι) = (ι * π) * (P * ι) by simp only [Matrix.mul_assoc], hιπ, Matrix.add_mul, Matrix.sub_mul,
      Matrix.one_mul, vecMulVec_mul, vecMulVec_mul, hwx]
    ext i j; simp [vecMulVec_apply, α]
  have k1 : (P * ι)ᵀ * J * (P * ι).map c = J₁ := by
    calc (P * ι)ᵀ * J * (P * ι).map c = ιᵀ * (Pᵀ * J * P.map c) * ι.map c := by
          rw [Matrix.map_mul, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = J₁ := by rw [hP, hgram]
  have k2 : (P * ι)ᵀ * J * (vecMulVec x α).map c = 0 := by
    have : ((P * ι)ᵀ * J) *ᵥ (c ∘ x) = 0 := by
      rw [hcx, mulVec_mulVec, transpose_mul,
        show ιᵀ * Pᵀ * J * P.map c = ιᵀ * (Pᵀ * J * P.map c) by simp only [Matrix.mul_assoc], hP, hιx]
    rw [vmv_map, mul_vmv, this]; ext i j; simp [vecMulVec_apply]
  have k3 : (vecMulVec x α)ᵀ * J * (P * ι).map c = 0 := by
    have : x ᵥ* (J * (P * ι).map c) = 0 := by
      calc x ᵥ* (J * (P * ι).map c) = (x ᵥ* Pᵀ) ᵥ* (J * (P.map c * ι.map c)) := by rw [hxP, Matrix.map_mul]
        _ = x ᵥ* (Pᵀ * J * P.map c * ι.map c) := by rw [vecMul_vecMul]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hP, hxι]
    rw [vmv_transpose, Matrix.mul_assoc, vecMulVec_mul, this]; ext i j; simp [vecMulVec_apply]
  have k4 : (vecMulVec x α)ᵀ * J * (vecMulVec x α).map c = 0 := by
    rw [vmv_transpose, vmv_map, vecMulVec_mul, vmv_mul_vmv, ← dotProduct_mulVec, hxx, zero_smul]
  have hms : (P * ι - vecMulVec x α).map c = (P * ι).map c - (vecMulVec x α).map c := by
    ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  have hU : (π * P * ι)ᵀ * J₁ * (π * P * ι).map c = J₁ := by
    have e0 : (π * P * ι)ᵀ * J₁ * (π * P * ι).map c = (ι * (π * P * ι))ᵀ * J * (ι * (π * P * ι)).map c := by
      simp only [← hgram, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e0, hιh, transpose_sub, hms, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, k1, k2, k3, k4]; abel
  set h := π * P * ι with hh
  refine ⟨hU, ?_, fun z => ?_⟩
  · have e := congrArg Matrix.det hU
    rw [det_mul, det_mul, det_transpose, show h.map c = c.mapMatrix h from rfl, ← RingHom.map_det] at e
    have e' : (h.det * c h.det) * J₁.det = 1 * J₁.det := by linear_combination e
    have h1 : h.det * c h.det = 1 := hJ₁.mul_right_cancel e'
    exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  · have e3 : (ι * h) *ᵥ z = (P * ι) *ᵥ z - (α ⬝ᵥ z) • x := by rw [hιh, sub_mulVec, vmv_mulVec]
    have e4 : α ⬝ᵥ z = (J *ᵥ (c ∘ y)) ⬝ᵥ (P *ᵥ (ι *ᵥ z)) := by rw [hα, ← dotProduct_mulVec, mulVec_mulVec]
    rw [← mulVec_mulVec z ι h, ← mulVec_mulVec z P ι, e4] at e3
    rw [e3]; abel

end GlobalTheory.PlaneProj

namespace GlobalTheory.PlaneProj
open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR' (σ : E →ₐ[F] E) (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  show Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] a) = (1 : AF F) ⊗ₜ[F] σ a
  simp

theorem cA_incV (σ : E →ₐ[F] E) {n : ℕ} (v : Fin n → E) :
    ⇑((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) ∘ incV F v = incV F (⇑σ ∘ v) := by
  funext i; exact cA_inclR' σ (v i)

theorem incM_map (σ : E →ₐ[F] E) {m n : Type} (M : Matrix m n E) :
    (incM F M).map ⇑((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) = incM F (M.map σ) := by
  ext i j; exact cA_inclR' σ (M i j)

theorem incM_mulVec' {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incM F M *ᵥ incV F v = incV F (M *ᵥ v) := by
  funext i; exact (RingHom.map_mulVec (inclR (F := F) (AF F)) M v i).symm

theorem incV_vecMul {m n : ℕ} (v : Fin m → E) (M : Matrix (Fin m) (Fin n) E) :
    incV F v ᵥ* incM F M = incV F (v ᵥ* M) := by
  funext j; exact (RingHom.map_vecMul (inclR (F := F) (AF F)) M v j).symm

theorem incV_dot {n : ℕ} (u w : Fin n → E) : incV F u ⬝ᵥ incV F w = inclR (F := F) (AF F) (u ⬝ᵥ w) := by
  simp only [incV, dotProduct, map_sum, map_mul]

theorem incM_mul {m n k : Type} [Fintype n] (M : Matrix m n E) (N : Matrix n k E) :
    incM F M * incM F N = incM F (M * N) := (Matrix.map_mul (f := inclR (F := F) (AF F))).symm

theorem incM_vmv {m n : ℕ} (u : Fin m → E) (w : Fin n → E) :
    vecMulVec (incV F u) (incV F w) = incM F (vecMulVec u w) := by
  ext i j; simp [incM, incV, vecMulVec_apply]

theorem incM_transpose {m n : Type} (M : Matrix m n E) : (incM F M)ᵀ = incM F Mᵀ := rfl

theorem incV_zero {n : ℕ} : incV F (0 : Fin n → E) = 0 := by funext i; simp [incV]

end GlobalTheory.PlaneProj

open GlobalTheory.PlaneProj Matrix in

theorem GlobalTheory.PlaneProj.exists_levi_proj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ p : UA σ W.J, mat p *ᵥ incV F H'.x = incV F H'.x → ∃ h₁ : UA σ W₁.J,
      ∀ z : Fin d₁ → AE F E, ∃ a : AE F E, mat p *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ (mat h₁ *ᵥ z) + a • incV F H'.x := by
  intro F E _ _ _ _ _ σ B d W r s d₁ W₁ H' i₀ i₁ hσ hW hH p hp
  obtain ⟨π, -, hfr, hJ₁⟩ := GlobalTheory.PlaneFrame.frame_dual_gram F E σ B d W r s d₁ W₁ H' i₀ i₁ hσ hW hH
  have hsk := GlobalTheory.PlaneFrame.form_skew hσ hW.skew
  set c : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hc

  have eιx : (H'.ιᵀ * W.J) *ᵥ (⇑σ ∘ H'.x) = 0 := by
    funext j
    have h0 := (hH.orth (Pi.single j 1)).1
    rw [form, dotProduct_comm, dotProduct_mulVec, dotProduct_single_one] at h0
    rw [Pi.zero_apply, ← h0, ← mulVec_mulVec, mulVec_transpose]; rfl
  have exι : H'.x ᵥ* (W.J * H'.ι.map σ) = 0 := by
    funext j
    have h0 : form σ W.J H'.x (H'.ι *ᵥ Pi.single j 1) = 0 := by
      rw [hsk, (hH.orth _).1, map_zero, neg_zero]
    rw [Pi.zero_apply, ← h0, form, ← dotProduct_single_one (H'.x ᵥ* _) j, ← dotProduct_mulVec, ← mulVec_mulVec]
    congr 2
    funext i; simp [mulVec, dotProduct, Pi.single_apply]
  have hframe : vecMulVec (incV F H'.x) (incM F W.J *ᵥ (c ∘ incV F H'.y)) + incM F H'.ι * incM F π -
      vecMulVec (incV F H'.y) (incM F W.J *ᵥ (c ∘ incV F H'.x)) = 1 := by
    rw [cA_incV, cA_incV, incM_mulVec', incM_mulVec', incM_vmv, incM_vmv, incM_mul]
    have e1 : incM F (vecMulVec H'.x (W.J *ᵥ (⇑σ ∘ H'.y))) + incM F (H'.ι * π) - incM F (vecMulVec H'.y (W.J *ᵥ (⇑σ ∘ H'.x))) =
        incM F (vecMulVec H'.x (W.J *ᵥ (⇑σ ∘ H'.y)) + H'.ι * π - vecMulVec H'.y (W.J *ᵥ (⇑σ ∘ H'.x))) := by
      ext i j; simp only [incM, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, map_add, map_sub]
    rw [e1]
    have e2 : vecMulVec H'.x (W.J *ᵥ (⇑σ ∘ H'.y)) + H'.ι * π - vecMulVec H'.y (W.J *ᵥ (⇑σ ∘ H'.x)) = 1 := hfr
    rw [e2]; ext i j; simp [incM, Matrix.one_apply]
  have hgram : (incM F H'.ι)ᵀ * incM F W.J * (incM F H'.ι).map c = incM F W₁.J := by
    rw [incM_map, incM_transpose, incM_mul, incM_mul, hH.gram]
  have hιx : ((incM F H'.ι)ᵀ * incM F W.J) *ᵥ (c ∘ incV F H'.x) = 0 := by
    rw [cA_incV, incM_transpose, incM_mul, incM_mulVec', eιx, incV_zero]
  have hxι : incV F H'.x ᵥ* (incM F W.J * (incM F H'.ι).map c) = 0 := by
    rw [incM_map, incM_mul, incV_vecMul, exι, incV_zero]
  have hxx : incV F H'.x ⬝ᵥ (incM F W.J *ᵥ (c ∘ incV F H'.x)) = 0 := by
    rw [cA_incV, incM_mulVec', incV_dot]
    have : H'.x ⬝ᵥ (W.J *ᵥ (⇑σ ∘ H'.x)) = 0 := hH.xx
    rw [this, map_zero]
  have hJ₁' : IsUnit (incM F W₁.J).det := by
    rw [show incM F W₁.J = (inclR (F := F) (AF F)).mapMatrix W₁.J from rfl, ← RingHom.map_det]
    exact hJ₁.map _
  obtain ⟨hU, hdet, hz⟩ := proj_core c (mat p) (incM F W.J) (incM F W₁.J) (incM F H'.ι) (incM F π) (incV F H'.x) (incV F H'.y)
    p.2 hp hframe hgram hιx hxι hxx hJ₁'
  exact ⟨⟨Matrix.GeneralLinearGroup.mk'' _ hdet, hU⟩, fun z => ⟨_, hz z⟩⟩
