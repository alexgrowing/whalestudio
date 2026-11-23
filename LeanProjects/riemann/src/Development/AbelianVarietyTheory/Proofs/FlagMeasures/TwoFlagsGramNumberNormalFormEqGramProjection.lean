import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.Rad
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NormGram

variable {k r : ℕ}

def rE (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin r → ℂ := fun a => v (eI k r a)

def rW (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)

def rS (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin r → ℂ := fun a => v (esI k r a)

def iW (k r : ℕ) (w : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := ∑ j, w j • bvec (wI k r j)

theorem iW_e (w : Fin (k + 1) → ℂ) (a : Fin r) : iW k r w (eI k r a) = 0 := by
  simp [iW, Finset.sum_apply, bvec_apply, eI_ne_wI]
theorem middleSpaceEmbedding_apply_dualIsotropicIndex (w : Fin (k + 1) → ℂ) (a : Fin r) : iW k r w (esI k r a) = 0 := by
  simp [iW, Finset.sum_apply, bvec_apply, esI_ne_wI]
theorem iW_w (w : Fin (k + 1) → ℂ) (j : Fin (k + 1)) : iW k r w (wI k r j) = w j := by
  simp [iW, Finset.sum_apply, bvec_apply, wI_inj]

theorem H_e (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  simp [Matrix.mulVec, dotProduct, sum3, H_ee, H_ew, H_es]
theorem H_w (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (k + 1)) :
    (Hpk k r *ᵥ v) (wI k r j) = sg k j * v (wI k r j) := by
  simp [Matrix.mulVec, dotProduct, sum3, H_we, H_ww, H_ws]
theorem besselHermForm_mulVec_dualIsotropicIndex (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  simp [Matrix.mulVec, dotProduct, sum3, H_se, H_sw, H_ss]

theorem herm3 (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) v w =
    star (rE k r w) ⬝ᵥ rS k r v + herm (Hb k) (rW k r v) (rW k r w) + star (rS k r w) ⬝ᵥ rE k r v := by
  rw [herm_Hb]
  unfold herm
  rw [dotProduct, sum3]
  simp [H_e, H_w, besselHermForm_mulVec_dualIsotropicIndex, rE, rW, rS, dotProduct]

theorem herm_e (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  unfold herm
  rw [← H_e v a]
  simp [bvec, dotProduct, Pi.single_apply, apply_ite]

theorem HH : Hpk k r * Hpk k r = 1 := by
  ext x y
  rw [Matrix.mul_apply, sum3]
  induction x using cases3 <;> induction y using cases3 <;>
    simp [H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss, Matrix.one_apply,
      eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]
  unfold sg; split_ifs <;> simp_all

theorem HbHb : Hb k * Hb k = 1 := by
  unfold Hb; rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext j; split_ifs <;> simp

theorem unit_of_UH {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) (hg : g ∈ UH H) : IsUnit g.det := by
  have hm' : gᴴ * H * g = H := hg
  have h1 : (H * gᴴ * H) * g = 1 := by
    rw [← hH]; nth_rewrite 4 [← hm']; simp only [Matrix.mul_assoc]
  exact Matrix.isUnit_det_of_left_inverse h1

theorem herm_iso {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  have hm' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm']

theorem herm_inv {g : Mat k r} (hg : g ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (g⁻¹ *ᵥ w) = herm (Hpk k r) (g *ᵥ v) w := by
  rw [← herm_iso hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (unit_of_UH HH hg), Matrix.one_mulVec]

theorem herm_inv' {g : Mat k r} (hg : g ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g⁻¹ *ᵥ v) w = herm (Hpk k r) v (g *ᵥ w) := by
  rw [← herm_iso hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (unit_of_UH HH hg), Matrix.one_mulVec]

theorem of_Xst {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ Xst k r) : rE k r v = 0 ∧ rW k r v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    constructor <;> funext j <;> simp [rE, rW, bvec_apply, eI_ne_esI, wI_ne_esI]
  | zero => exact ⟨rfl, rfl⟩
  | add x y _ _ hx hy =>
    constructor <;> funext j
    · have := congrFun hx.1 j; have := congrFun hy.1 j; simp_all [rE]
    · have := congrFun hx.2 j; have := congrFun hy.2 j; simp_all [rW]
  | smul c x _ hx =>
    constructor <;> funext j
    · have := congrFun hx.1 j; simp_all [rE]
    · have := congrFun hx.2 j; simp_all [rW]

theorem mem_Xsp {v : Fin (2 * r + k + 1) → ℂ} : v ∈ Xsp k r ↔ rW k r v = 0 ∧ rS k r v = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      constructor <;> funext j <;> simp [rS, rW, bvec_apply, esI_ne_eI, wI_ne_eI]
    | zero => exact ⟨rfl, rfl⟩
    | add x y _ _ hx hy =>
      constructor <;> funext j
      · have := congrFun hx.1 j; have := congrFun hy.1 j; simp_all [rW]
      · have := congrFun hx.2 j; have := congrFun hy.2 j; simp_all [rS]
    | smul c x _ hx =>
      constructor <;> funext j
      · have := congrFun hx.1 j; simp_all [rW]
      · have := congrFun hx.2 j; simp_all [rS]
  · rintro ⟨h1, h2⟩
    have : v = ∑ a, v (eI k r a) • bvec (eI k r a) := by
      funext x
      induction x using cases3 with
      | h1 a => simp [Finset.sum_apply, bvec_apply, eI_inj]
      | h2 j => simpa [Finset.sum_apply, bvec_apply, wI_ne_eI, rW] using congrFun h1 j
      | h3 a => simpa [Finset.sum_apply, bvec_apply, esI_ne_eI, rS] using congrFun h2 a
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem of_inWb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : rE k r z = 0 ∧ rS k r z = 0 := by
  constructor <;> funext a
  · exact hz _ (Or.inl a.2)
  · have := a.2
    exact hz _ (Or.inr (by simp only [esI]; omega))

theorem rW_u (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rW k r (uEmb k r u *ᵥ v) = rW k r v := by
  funext j
  have := j.2
  have h : ∀ y, uEmb k r u (wI k r j) y = if wI k r j = y then 1 else 0 := fun y => by
    unfold uEmb; rw [dif_neg (by simp only [wI]; omega), dif_neg (by simp only [wI]; omega)]
  simp [rW, Matrix.mulVec, dotProduct, h]

theorem rS_u (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rS k r (uEmb k r u *ᵥ v) = (u⁻¹)ᴴ *ᵥ rS k r v := by
  funext a
  have := a.2
  have hb : ∀ (b : Fin r) h, (⟨2 * r + k - (esI k r b).val, h⟩ : Fin r) = b := fun b h =>
    Fin.ext (by have := b.2; simp only [esI]; omega)
  have h1 : ∀ b, uEmb k r u (esI k r a) (eI k r b) = 0 := fun b => by
    have := b.2
    unfold uEmb; rw [dif_neg (by simp only [esI]; omega), dif_neg (by simp only [eI]; omega), if_neg (esI_ne_eI _ _)]
  have h2 : ∀ b, uEmb k r u (esI k r a) (wI k r b) = 0 := fun b => by
    have := b.2
    unfold uEmb; rw [dif_neg (by simp only [esI]; omega), dif_neg (by simp only [wI]; omega), if_neg (esI_ne_wI _ _)]
  have h3 : ∀ b, uEmb k r u (esI k r a) (esI k r b) = star (u⁻¹ b a) := fun b => by
    have := b.2
    unfold uEmb; rw [dif_neg (by simp only [esI]; omega), dif_pos (by simp only [esI]; omega)]
    simp only [hb]
  simp [rS, Matrix.mulVec, dotProduct, sum3, h1, h2, h3]

theorem rW_p (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rW k r (pEl k r B S *ᵥ v) = rW k r v + ∑ b, rS k r v b • B b := by
  funext j
  simp [rW, rS, Matrix.mulVec, dotProduct, sum3, pEl_we, pEl_ww, pEl_ws, Finset.sum_apply, mul_comm]

theorem rS_p (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rS k r (pEl k r B S *ᵥ v) = rS k r v := by
  funext j
  simp [rS, Matrix.mulVec, dotProduct, sum3, pEl_se, pEl_sw, pEl_ss]

theorem rW_m (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rW k r (mEmb k r m *ᵥ v) = m *ᵥ rW k r v := by
  funext j
  simp [rW, Matrix.mulVec, dotProduct, sum3, m_we, m_ww, m_ws]

theorem rS_m (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rS k r (mEmb k r m *ᵥ v) = rS k r v := by
  funext j
  simp [rS, Matrix.mulVec, dotProduct, middleSpaceLeviEmbedding_apply_es_row]

theorem gramProj_mid (P : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * r + k + 1))))
    (P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))))
    (hP : ∀ p, p ∈ P ↔ rE k r p.ofLp = 0 ∧ rS k r p.ofLp = 0 ∧ WithLp.toLp 2 (rW k r p.ofLp) ∈ P₀)
    {n : ℕ} (v : Fin n → Fin (2 * r + k + 1) → ℂ) : gramProj P v = gramProj P₀ fun a => rW k r (v a) := by
  have hin : ∀ x p : EuclideanSpace ℂ (Fin (2 * r + k + 1)), rE k r p.ofLp = 0 → rS k r p.ofLp = 0 →
      ⟪x, p⟫_ℂ = ⟪(WithLp.toLp 2 (rW k r x.ofLp) : EuclideanSpace ℂ _), WithLp.toLp 2 (rW k r p.ofLp)⟫_ℂ := by
    intro x p h1 h2
    have h1' : ∀ a, p.ofLp (eI k r a) = 0 := congrFun h1
    have h2' : ∀ a, p.ofLp (esI k r a) = 0 := congrFun h2
    simp [PiLp.inner_apply, sum3, h1', h2', rW]
  have hW : ∀ w, rW k r (iW k r w) = w := fun w => funext (iW_w w)
  have hE : ∀ w, rE k r (iW k r w) = 0 := fun w => funext (iW_e w)
  have hS : ∀ w, rS k r (iW k r w) = 0 := fun w => funext (middleSpaceEmbedding_apply_dualIsotropicIndex w)
  have hpr : ∀ x : Fin (2 * r + k + 1) → ℂ, P.starProjection (WithLp.toLp 2 x) =
      WithLp.toLp 2 (iW k r (P₀.starProjection (WithLp.toLp 2 (rW k r x))).ofLp) := by
    intro x
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [hP]; refine ⟨hE _, hS _, ?_⟩
      simp only [hW]
      exact Submodule.starProjection_apply_mem _ _
    · intro w hw
      obtain ⟨h1, h2, h3⟩ := (hP w).1 hw
      rw [inner_sub_left, hin _ _ h1 h2, hin _ _ h1 h2, ← inner_sub_left]
      simp only [hW]
      exact Submodule.starProjection_inner_eq_zero _ _ h3
  unfold gramProj
  congr 3
  ext a b
  simp only [Matrix.gram_apply, hpr]
  rw [hin _ (WithLp.toLp 2 (iW k r _)) (hE _) (hS _)]
  simp only [hW]

theorem gramProj_comb {n : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (T : Matrix (Fin r) (Fin r) ℂ)
    (w : Fin r → Fin n → ℂ) : gramProj P (fun c => ∑ b, T b c • w b) = ‖T.det‖ * gramProj P w := by
  unfold gramProj
  have : (Matrix.gram ℂ fun c => P.starProjection (WithLp.toLp 2 (∑ b, T b c • w b))) =
      Tᴴ * (Matrix.gram ℂ fun a => P.starProjection (WithLp.toLp 2 (w a))) * T := by
    ext a b
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, WithLp.toLp_sum, WithLp.toLp_smul,
      map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp; ring
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_mul, norm_star,
    mul_right_comm, Real.sqrt_mul (by positivity), Real.sqrt_mul_self (norm_nonneg _)]

def Cm (k r : ℕ) (g : Mat k r) : Matrix (Fin r) (Fin r) ℂ := fun b c => (g⁻¹ *ᵥ bvec (eI k r c)) (esI k r b)

section normal
variable {z z' : Fin (2 * r + k + 1) → ℂ} {g : Mat k r} {β : Fin r → ℕ}

theorem herm_Cm (hn : IsNormal k r β g) (w : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    herm (Hpk k r) w (g⁻¹ *ᵥ bvec (eI k r c)) = ((Cm k r g)ᴴ *ᵥ rE k r w) c := by
  obtain ⟨h1, h2⟩ := of_Xst (hn.2.1 c).1
  rw [herm3, h1, h2]
  simp [herm, Matrix.mulVec, dotProduct, Cm, rS]

theorem fvec_cast (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : fvec k r z a.castSucc = bvec (eI k r a) := by
  simp [fvec]
theorem fvec_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

theorem Dmin_r (hn : IsNormal k r β g) : Dmin k r z z' g ⟨r, by omega⟩ = ((Cm k r g)ᴴ).det := by
  unfold Dmin
  congr 1
  ext a b
  show herm (Hpk k r) (g *ᵥ fvec k r z' (Fin.castSucc b)) (fvec k r z (Fin.castSucc a)) = _
  rw [fvec_cast, fvec_cast, ← herm_inv hn.1, herm_Cm hn]
  simp [Matrix.mulVec, dotProduct, rE, bvec_apply, eI_inj]

theorem Dmin_last (hn : IsNormal k r β g) (hz : inWb k r z) : Dmin k r z z' g (Fin.last (r + 1)) =
    herm (Hpk k r) (g *ᵥ z') z * Dmin k r z z' g ⟨r, by omega⟩ := by
  have h1 : Dmin k r z z' g (Fin.last (r + 1)) = (Zhat k r z z' g).det := rfl
  have h2 : Dmin k r z z' g ⟨r, by omega⟩ = ((Zhat k r z z' g).submatrix Fin.castSucc Fin.castSucc).det := rfl
  have h3 : ∀ b : Fin r, Zhat k r z z' g (Fin.last r) b.castSucc = 0 := by
    intro b
    obtain ⟨h1, h2⟩ := of_Xst (hn.2.1 b).2
    obtain ⟨h3, h4⟩ := of_inWb hz
    unfold Zhat
    rw [fvec_cast, fvec_last, herm3, h1, h2, h3]
    simp [herm]
  rw [h1, h2, Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  simp only [h3, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last, Fin.val_last]
  rw [← two_mul, pow_mul]
  simp [Zhat, fvec_last]

theorem mem_Hcom (hn : IsNormal k r β g) (hC : (Cm k r g).det ≠ 0) (w : Fin (2 * r + k + 1) → ℂ) :
    w ∈ Hcom k r z z' g ↔ rE k r w = 0 ∧ rS k r w = 0 ∧ herm (Hb k) (rW k r w) (rW k r z') = 0 ∧
      herm (Hb k) (rW k r w) (rW k r (g⁻¹ *ᵥ z)) = 0 := by
  show (∀ a : Fin (r + 1), _ ∧ _) ↔ _
  rw [Fin.forall_fin_succ']
  simp only [fvec_cast, fvec_last, herm_e, herm_Cm hn]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hS : rS k r w = 0 := funext fun a => (h1 a).1
    have hE : rE k r w = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero (M := (Cm k r g)ᴴ)
      · rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hC
      · exact funext fun a => (h1 a).2
    rw [herm3, hS, hE] at h2 h3
    exact ⟨hE, hS, by simpa using h2, by simpa using h3⟩
  · rintro ⟨hE, hS, h2, h3⟩
    refine ⟨fun a => ⟨congrFun hS a, by simp [hE]⟩, ?_, ?_⟩ <;> rw [herm3, hS, hE] <;> simpa

theorem mem_sup (hn : IsNormal k r β g) (hC : (Cm k r g).det ≠ 0) (v : Fin (2 * r + k + 1) → ℂ) :
    v ∈ Hcom k r z z' g ⊔ Xsp k r ↔ rS k r v = 0 ∧ herm (Hb k) (rW k r v) (rW k r z') = 0 ∧
      herm (Hb k) (rW k r v) (rW k r (g⁻¹ *ᵥ z)) = 0 := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨w, hw, x, hx, rfl⟩
    obtain ⟨-, h2, h3, h4⟩ := (mem_Hcom hn hC w).1 hw
    obtain ⟨h5, h6⟩ := mem_Xsp.1 hx
    have e1 : rW k r (w + x) = rW k r w + rW k r x := rfl
    have e2 : rS k r (w + x) = rS k r w + rS k r x := rfl
    rw [e1, e2, h2, h5, h6, add_zero, add_zero]
    exact ⟨rfl, h3, h4⟩
  · rintro ⟨h1, h2, h3⟩
    have hW : ∀ w, rW k r (iW k r w) = w := fun w => funext (iW_w w)
    have hE : ∀ w, rE k r (iW k r w) = 0 := fun w => funext (iW_e w)
    have hS : ∀ w, rS k r (iW k r w) = 0 := fun w => funext (middleSpaceEmbedding_apply_dualIsotropicIndex w)
    refine ⟨iW k r (rW k r v), (mem_Hcom hn hC _).2 ⟨hE _, hS _, by rwa [hW], by rwa [hW]⟩,
      v - iW k r (rW k r v), mem_Xsp.2 ⟨?_, ?_⟩, by abel⟩
    · show rW k r v - rW k r (iW k r (rW k r v)) = 0
      rw [hW, sub_self]
    · show rS k r v - rS k r (iW k r (rW k r v)) = 0
      rw [hS, h1, sub_self]

theorem Cm_det (ht : TwoFl k r z z' g) (hn : IsNormal k r β g) :
    Dr k r z z' g = ‖(Cm k r g).det‖ ∧ (Cm k r g).det ≠ 0 := by
  have h : Dr k r z z' g = ‖(Cm k r g).det‖ := by
    unfold Dr; rw [Dmin_r hn, Matrix.det_conjTranspose, norm_star]
  exact ⟨h, fun h0 => ht.2.2.2.2.2.2 (by rw [h, h0, norm_zero])⟩

theorem gram_ne (ht : TwoFl k r z z' g) (hn : IsNormal k r β g) :
    herm (Hb k) (rW k r z') (rW k r z') * herm (Hb k) (rW k r (g⁻¹ *ᵥ z)) (rW k r (g⁻¹ *ᵥ z)) -
      herm (Hb k) (rW k r z') (rW k r (g⁻¹ *ᵥ z)) * herm (Hb k) (rW k r (g⁻¹ *ᵥ z)) (rW k r z') ≠ 0 := by
  obtain ⟨hz, hz', -, -, hg, hG, -⟩ := ht
  obtain ⟨z1, z2⟩ := of_inWb hz
  obtain ⟨z1', z2'⟩ := of_inWb hz'
  have hy : rS k r (g⁻¹ *ᵥ z) = 0 := by
    funext a
    obtain ⟨h1, h2⟩ := of_Xst (hn.2.1 a).2
    show (g⁻¹ *ᵥ z) (esI k r a) = 0
    rw [← herm_e (g⁻¹ *ᵥ z) a, herm_inv' hg, herm3, h1, h2, z1]
    simp [herm]
  have real : ∀ v : Fin (k + 1) → ℂ, herm (Hb k) v v = ((herm (Hb k) v v).re : ℂ) := fun v =>
    (Complex.conj_eq_iff_re.1 (herm_star v v)).symm
  have e1 : herm (Hb k) (rW k r z') (rW k r z') = -(Tz k r z' : ℂ) := by
    rw [real, Tz, herm3, z1', z2']; simp
  have e2 : herm (Hb k) (rW k r (g⁻¹ *ᵥ z)) (rW k r (g⁻¹ *ᵥ z)) = -(Tz k r z : ℂ) := by
    have : herm (Hpk k r) z z = herm (Hpk k r) (g⁻¹ *ᵥ z) (g⁻¹ *ᵥ z) := by
      rw [herm_inv hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (unit_of_UH HH hg), Matrix.one_mulVec]
    rw [real, Tz, this, herm3, hy]; simp
  have e3 : herm (Hb k) (rW k r z') (rW k r (g⁻¹ *ᵥ z)) = herm (Hpk k r) (g *ᵥ z') z := by
    rw [← herm_inv hg, herm3, z1', z2']; simp
  rw [← herm_star (rW k r z') (rW k r (g⁻¹ *ᵥ z)), e1, e2, e3]
  intro h0
  apply hG
  unfold Gf
  rw [Dmin_last hn hz, map_mul]
  have : Complex.normSq (herm (Hpk k r) (g *ᵥ z') z) = Tz k r z * Tz k r z' := by
    apply Complex.ofReal_injective
    rw [← Complex.mul_conj]
    push_cast
    simp only [Complex.star_def] at h0
    linear_combination -h0
  rw [this, sub_self]

end normal

def pair2 (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (s t : Fin (k + 1) → ℂ) :
    EuclideanSpace ℂ (Fin (k + 1)) →ₗ[ℂ] ℂ × ℂ where
  toFun p := (herm (Hb k) (m *ᵥ p.ofLp) s, herm (Hb k) (m *ᵥ p.ofLp) t)
  map_add' p q := by simp [herm, Matrix.mulVec_add]
  map_smul' c p := by simp [herm, Matrix.mulVec_smul]

def Pz (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (s t : Fin (k + 1) → ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))) :=
  LinearMap.ker ((pair2 m s t).prod (EuclideanSpace.projₗ (Fin.last k)))

theorem mem_Pz (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (s t p : Fin (k + 1) → ℂ) :
    WithLp.toLp 2 p ∈ Pz m s t ↔ (herm (Hb k) (m *ᵥ p) s = 0 ∧ herm (Hb k) (m *ᵥ p) t = 0) ∧ p (Fin.last k) = 0 := by
  simp [Pz, pair2]

theorem finrank_Pz {m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hm : IsUnit m.det) {s t : Fin (k + 1) → ℂ}
    (h : herm (Hb k) s s * herm (Hb k) t t - herm (Hb k) s t * herm (Hb k) t s ≠ 0) :
    Module.finrank ℂ (Pz m s t) = k - 2 ∨ Module.finrank ℂ (Pz m s t) = k - 1 := by
  have hsurj : LinearMap.range (pair2 m s t) = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨x, y⟩
    set D := herm (Hb k) s s * herm (Hb k) t t - herm (Hb k) s t * herm (Hb k) t s with hD
    refine ⟨WithLp.toLp 2 (m⁻¹ *ᵥ (((x * herm (Hb k) t t - y * herm (Hb k) t s) / D) • s +
      ((y * herm (Hb k) s s - x * herm (Hb k) s t) / D) • t)), ?_⟩
    have hs : ∀ (c : ℂ) v w, herm (Hb k) (c • v) w = c * herm (Hb k) v w := fun c v w => by
      simp [herm, Matrix.mulVec_smul]
    simp only [pair2, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hm,
      Matrix.one_mulVec, herm_add_left, hs, Prod.mk.injEq]
    constructor <;> field_simp <;> rw [hD] <;> ring
  have h1 := LinearMap.finrank_range_add_finrank_ker (pair2 m s t)
  rw [hsurj] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker ((pair2 m s t).prod (EuclideanSpace.projₗ (Fin.last k)))
  have h3 := Submodule.finrank_le (LinearMap.range ((pair2 m s t).prod (EuclideanSpace.projₗ (Fin.last k))))
  have h4 : Module.finrank ℂ (Pz m s t) ≤ Module.finrank ℂ (LinearMap.ker (pair2 m s t)) := by
    apply Submodule.finrank_mono
    unfold Pz; rw [LinearMap.ker_prod]; exact inf_le_left
  simp only [finrank_top, Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace, Fintype.card_fin]
    at h1 h2 h3
  unfold Pz at *
  omega

theorem mem_pos (p : Fin (2 * r + k + 1) → ℂ) : p ∈ LinearMap.ker (Matrix.toLin' (Hpk k r - 1)) ↔
    rE k r p = rS k r p ∧ rW k r p (Fin.last k) = 0 := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  constructor
  · intro h
    refine ⟨funext fun a => ?_, ?_⟩
    · have := congrFun h (esI k r a); rwa [besselHermForm_mulVec_dualIsotropicIndex] at this
    · have := congrFun h (wI k r (Fin.last k)); rw [H_w] at this
      simp only [sg, if_true] at this
      show p _ = 0
      linear_combination (-1 / 2 : ℂ) * this
  · rintro ⟨h1, h2⟩
    funext x
    induction x using cases3 with
    | h1 a => rw [H_e]; exact (congrFun h1 a).symm
    | h2 j =>
      rw [H_w]; unfold sg; split_ifs with h
      · subst h; have : p (wI k r (Fin.last k)) = 0 := h2
        simp [this]
      · simp
    | h3 a => rw [besselHermForm_mulVec_dualIsotropicIndex]; exact congrFun h1 a

theorem Yv_normal : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ), 2 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → ∀ m ∈ UH (Hb k), ∃ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) ∧ ∀ (u : UT r → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Yv k r z z' g₀ (uEmb k r (upper u) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) = gramProj P₀ fun b => m⁻¹ *ᵥ q.1 b := by
  intro k r z z' g β _ ht hn m hm
  have hmu := unit_of_UH HbHb hm
  obtain ⟨hD, hC⟩ := Cm_det ht hn
  refine ⟨Pz m (rW k r z') (rW k r (g⁻¹ *ᵥ z)), finrank_Pz hmu (gram_ne ht hn), fun u q a ha => ?_⟩
  obtain ⟨-, -, hU, hup⟩ := GlobalTheory.Amp.UEmb.uEmb_hom k r
  set U := upper u with hUdef
  set A : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun b => (a b : ℂ) with hA
  have hUd : U.det = 1 := (hup u).1
  have hUu : IsUnit U.det := by rw [hUd]; exact isUnit_one
  have hAu : IsUnit A.det := by
    rw [hA, Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun b _ => Complex.ofReal_ne_zero.2 (ha b).ne'
  set x := uEmb k r U * pOf k r q * uEmb k r A * mEmb k r m with hx
  have hxu : IsUnit x.det := by
    simp only [hx, Matrix.det_mul]
    exact (((unit_of_UH HH (hU U hUu).1).mul (unit_of_UH HH (pEl_mem_UH _ _ (skewM_skew _ _)))).mul
      (unit_of_UH HH (hU A hAu).1)).mul (unit_of_UH HH (mEmb_mem m hm))
  have xS : ∀ v, rS k r (x *ᵥ v) = (U⁻¹)ᴴ *ᵥ ((A⁻¹)ᴴ *ᵥ rS k r v) := fun v => by
    simp only [hx, ← Matrix.mulVec_mulVec, pOf, rS_u, rS_p, rS_m]
  have xW : ∀ v, rW k r (x *ᵥ v) = m *ᵥ rW k r v + ∑ b, ((A⁻¹)ᴴ *ᵥ rS k r v) b • q.1 b := fun v => by
    simp only [hx, ← Matrix.mulVec_mulVec, pOf, rW_u, rW_p, rW_m, rS_u, rS_m]
  have hinv : ∀ M : Matrix (Fin r) (Fin r) ℂ, IsUnit M.det → ((M⁻¹)ᴴ).det ≠ 0 := fun M hM => by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.2 (Matrix.isUnit_nonsing_inv_det M hM).ne_zero
  have hP : ∀ p, p ∈ Ppos k r z z' g x ↔ rE k r p.ofLp = 0 ∧ rS k r p.ofLp = 0 ∧
      WithLp.toLp 2 (rW k r p.ofLp) ∈ Pz m (rW k r z') (rW k r (g⁻¹ *ᵥ z)) := by
    intro p
    show (p.ofLp ∈ LinearMap.ker (Matrix.toLin' (Hpk k r - 1)) ∧
      Matrix.toLin' x p.ofLp ∈ Hcom k r z z' g ⊔ Xsp k r) ↔ _
    rw [mem_pos, Matrix.toLin'_apply, mem_sup hn hC, mem_Pz, xS, xW]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      have h5 := Matrix.eq_zero_of_mulVec_eq_zero (hinv A hAu)
        (Matrix.eq_zero_of_mulVec_eq_zero (hinv U hUu) h3)
      rw [h5] at h4 h1
      exact ⟨h1, h5, by simpa using h4, h2⟩
    · rintro ⟨h1, h2, h3, h4⟩
      rw [h1, h2]
      exact ⟨⟨rfl, h4⟩, by simp, by simpa using h3⟩
  set T : Matrix (Fin r) (Fin r) ℂ := -(Uᴴ * Cm k r g) with hT
  have hv : ∀ c, rW k r (x⁻¹ *ᵥ (g⁻¹ *ᵥ bvec (eI k r c))) = ∑ b, T b c • (m⁻¹ *ᵥ q.1 b) := by
    intro c
    set v := g⁻¹ *ᵥ bvec (eI k r c) with hv
    set y := x⁻¹ *ᵥ v with hy
    have hxy : x *ᵥ y = v := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hxu, Matrix.one_mulVec]
    have h1 := xS y
    have h2 := xW y
    rw [hxy] at h1 h2
    rw [(of_Xst (hn.2.1 c).1).2] at h2
    have h3 : (A⁻¹)ᴴ *ᵥ rS k r y = Uᴴ *ᵥ rS k r v := by
      rw [h1, Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hUu]
      simp
    have h4 : ∀ b, (Uᴴ *ᵥ rS k r v) b = -T b c := fun b => by
      simp [hT, Matrix.mul_apply, Matrix.mulVec, dotProduct, Cm, rS, hv]
    rw [h3] at h2
    have h5 : m *ᵥ rW k r y = ∑ b, T b c • q.1 b := by
      simp only [h4, neg_smul, Finset.sum_neg_distrib] at h2
      exact (eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact h2.symm))
    have h6 : rW k r y = m⁻¹ *ᵥ (m *ᵥ rW k r y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hmu, Matrix.one_mulVec]
    rw [h6, h5, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
  have hTd : ‖T.det‖ = ‖(Cm k r g).det‖ := by
    rw [hT, Matrix.det_neg, Matrix.det_mul, Matrix.det_conjTranspose, hUd]
    simp
  unfold Yv
  rw [gramProj_mid _ _ hP]
  simp only [hv]
  rw [gramProj_comb, hTd, hD]
  have := norm_ne_zero_iff.2 hC
  field_simp

end GlobalTheory.Amp.NormGram
