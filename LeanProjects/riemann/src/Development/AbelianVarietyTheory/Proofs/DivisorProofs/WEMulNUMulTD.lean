import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory.PrinTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def bor (a d : kˣ) (x : k) : GL (Fin (1 + 1)) k :=
  GeneralLinearGroup.mkOfDetNeZero !![(a : k), x; 0, (d : k)] (by simp)

def nU (x : k) : GL (Fin (1 + 1)) k := bor 1 1 x

def nL (x : k) : GL (Fin (1 + 1)) k := GeneralLinearGroup.mkOfDetNeZero !![1, 0; x, 1] (by simp)

def wE : GL (Fin (1 + 1)) k := GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp)

def tD (a d : kˣ) : GL (Fin (1 + 1)) k := bor a d 0

@[simp] theorem val_bor (a d : kˣ) (x : k) :
    ((bor a d x : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![(a : k), x; 0, (d : k)] := rfl

@[simp] theorem val_nL (x : k) :
    ((nL x : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![1, 0; x, 1] := rfl

@[simp] theorem val_wE :
    ((wE : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![0, 1; 1, 0] := rfl

@[simp] theorem val_nU (x : k) :
    ((nU x : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![1, x; 0, 1] := by
  simp [nU]

@[simp] theorem val_tD (a d : kˣ) :
    ((tD a d : GL (Fin (1 + 1)) k) : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) = !![(a : k), 0; 0, (d : k)] := by
  simp [tD]

theorem nU_mul_nU (x y : k) : (nU x : GL (Fin (1 + 1)) k) * nU y = nU (x + y) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem wE_mul_wE : (wE : GL (Fin (1 + 1)) k) * wE = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem nL_eq (x : k) : (nL x : GL (Fin (1 + 1)) k) = wE * nU x * wE := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem wE_mul_nU_eq (x : kˣ) :
    (wE : GL (Fin (1 + 1)) k) * nU (x : k) = bor (-x⁻¹) x 1 * nL ((x⁻¹ : kˣ) : k) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem wE_mul_nU_mul_tD (x : k) (a d : kˣ) :
    (wE : GL (Fin (1 + 1)) k) * nU x * tD a d = tD d a * wE * nU (x * d * ((a⁻¹ : kˣ) : k)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem tD_inv_eq (a : kˣ) : (tD a a⁻¹ : GL (Fin (1 + 1)) k) =
    nU (a : k) * nL (-((a⁻¹ : kˣ) : k)) * nU (a : k) * (nU (-1) * nL 1 * nU (-1)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

abbrev PSp (μ₁ μ₂ : kˣ →* ℂˣ) : Type :=
  IndSp (two (stdSum (rfl : 1 + 1 = 1 + 1)))
    ((extTensor (detRep (Fin 1) μ₁) (detRep (Fin 1) μ₂)).comp (leviTwo k (Fin 1) (Fin 1)).symm.toMonoidHom)

abbrev psRep (μ₁ μ₂ : kˣ →* ℂˣ) : Representation ℂ (GL (Fin (1 + 1)) k) (PSp μ₁ μ₂) :=
  prod₂ (detRep (Fin 1) μ₁) (detRep (Fin 1) μ₂)

def ev {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) : ℂ := TensorProduct.lid ℂ ℂ (f.1.1 g)

def coord {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (x : k) : ℂ := ev f (wE * nU x)

def bchar (μ₁ μ₂ : kˣ →* ℂˣ) (a d : kˣ) : ℂ :=
  ((μ₁ a * μ₂ d * absPow k (1 / 2) a * absPow k (-1 / 2) d : ℂˣ) : ℂ)

theorem ev_add {μ₁ μ₂ : kˣ →* ℂˣ} (f f' : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (f + f') g = ev f g + ev f' g := by
  show TensorProduct.lid ℂ ℂ (f.1.1 g + f'.1.1 g) = _
  rw [map_add]; rfl

theorem ev_smul {μ₁ μ₂ : kˣ →* ℂˣ} (c : ℂ) (f : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (c • f) g = c * ev f g := by
  show TensorProduct.lid ℂ ℂ (c • f.1.1 g) = _
  rw [map_smul]; rfl

theorem ev_sub {μ₁ μ₂ : kˣ →* ℂˣ} (f f' : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (f - f') g = ev f g - ev f' g := by
  show TensorProduct.lid ℂ ℂ (f.1.1 g - f'.1.1 g) = _
  rw [map_sub]; rfl

theorem ev_act {μ₁ μ₂ : kˣ →* ℂˣ} (h : GL (Fin (1 + 1)) k) (f : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (psRep μ₁ μ₂ h f) g = ev f (g * h) := rfl

theorem ext_ev {μ₁ μ₂ : kˣ →* ℂˣ} {f f' : PSp μ₁ μ₂} (h : ∀ g, ev f g = ev f' g) : f = f' := by
  apply Subtype.ext; apply Subtype.ext; funext g
  exact (TensorProduct.lid ℂ ℂ).injective (h g)

theorem bor_mem_parab (a d : kˣ) (x : k) :
    bor a d x ∈ parab k (two (stdSum (rfl : 1 + 1 = 1 + 1))) := by
  refine mem_parab_iff.2 fun b c i j hbc => ?_
  cases b <;> cases c
  · exact absurd hbc (by decide)
  · exact absurd hbc (by decide)
  swap
  · exact absurd hbc (by decide)
  show (bor a d x : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨true, i⟩)
    ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨false, j⟩) = 0
  rw [two_true, two_false, Subsingleton.elim i 0, Subsingleton.elim j 0]
  have h1 : stdSum (rfl : 1 + 1 = 1 + 1) (Sum.inr (0 : Fin 1)) = 1 := by decide
  have h0 : stdSum (rfl : 1 + 1 = 1 + 1) (Sum.inl (0 : Fin 1)) = 0 := by decide
  rw [h1, h0, val_bor]
  rfl

theorem ev_bor {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (a d : kˣ) (x : k) (g : GL (Fin (1 + 1)) k) :
    ev f (bor a d x * g) = bchar μ₁ μ₂ a d * ev f g := by
  have h := f.1.2 ⟨_, bor_mem_parab a d x⟩ g
  simp only [ev]
  rw [show (bor a d x * g) = ((⟨_, bor_mem_parab a d x⟩ : parab k _) : GL (Fin (1 + 1)) k) * g from rfl, h]
  generalize f.1.1 g = v
  set p : parab k (two (stdSum (rfl : 1 + 1 = 1 + 1))) := ⟨_, bor_mem_parab a d x⟩
  have h1 : stdSum (rfl : 1 + 1 = 1 + 1) (Sum.inr (0 : Fin 1)) = 1 := by decide
  have h0 : stdSum (rfl : 1 + 1 = 1 + 1) (Sum.inl (0 : Fin 1)) = 0 := by decide
  have e1 : GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : 1 + 1 = 1 + 1))) p false) = a := by
    ext
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    show (bor a d x : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨false, default⟩)
      ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨false, default⟩) = a
    rw [two_false, Subsingleton.elim (default : Fin 1) 0, h0, val_bor]
    rfl
  have e2 : GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : 1 + 1 = 1 + 1))) p true) = d := by
    ext
    rw [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    show (bor a d x : Matrix (Fin (1 + 1)) (Fin (1 + 1)) k) ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨true, default⟩)
      ((two (stdSum (rfl : 1 + 1 = 1 + 1))) ⟨true, default⟩) = d
    rw [two_true, Subsingleton.elim (default : Fin 1) 0, h1, val_bor]
    rfl
  have hd : (deltaHalf k (Two (Fin 1) (Fin 1)) (leviProj k (two (stdSum (rfl : 1 + 1 = 1 + 1))) p) : ℂ) =
      ((absPow k (1 / 2) a * absPow k (-1 / 2) d : ℂˣ) : ℂ) := by
    rw [← MulEquiv.apply_symm_apply (leviTwo k (Fin 1) (Fin 1)) (leviProj k _ p), deltaHalf_two]
    simp only [Fintype.card_fin, Nat.cast_one]
    rw [show ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)).1 = leviProj k _ p false from rfl,
      show ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)).2 = leviProj k _ p true from rfl, e1, e2]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul y z =>
    show TensorProduct.lid ℂ ℂ ((deltaHalf k _ (leviProj k _ p) : ℂ) • extTensor (detRep (Fin 1) μ₁)
      (detRep (Fin 1) μ₂) ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)) (y ⊗ₜ z)) = _
    rw [extTensor_tmul, hd]
    rw [show ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)).1 = leviProj k _ p false from rfl,
      show ((leviTwo k (Fin 1) (Fin 1)).symm (leviProj k _ p)).2 = leviProj k _ p true from rfl]
    simp only [detRep, ofChar_apply, detChar_apply, e1, e2, map_smul, TensorProduct.lid_tmul, bchar,
      Units.val_mul, smul_eq_mul]
    ring
  | add y z hy hz =>
    rw [map_add, map_add, map_add, hy, hz, mul_add]

def evL (μ₁ μ₂ : kˣ →* ℂˣ) (g : GL (Fin (1 + 1)) k) : PSp μ₁ μ₂ →ₗ[ℂ] ℂ where
  toFun f := ev f g
  map_add' f f' := ev_add f f' g
  map_smul' c f := ev_smul c f g

def coordL (μ₁ μ₂ : kˣ →* ℂˣ) : PSp μ₁ μ₂ →ₗ[ℂ] (k → ℂ) where
  toFun f := coord f
  map_add' f f' := funext fun x => ev_add f f' _
  map_smul' c f := funext fun x => ev_smul c f _

@[simp] theorem evL_apply (μ₁ μ₂ : kˣ →* ℂˣ) (g : GL (Fin (1 + 1)) k) (f : PSp μ₁ μ₂) :
    evL μ₁ μ₂ g f = ev f g := rfl

@[simp] theorem coordL_apply (μ₁ μ₂ : kˣ →* ℂˣ) (f : PSp μ₁ μ₂) : coordL μ₁ μ₂ f = coord f := rfl

theorem coord_nU {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (y x : k) :
    coord (psRep μ₁ μ₂ (nU y) f) x = coord f (x + y) := by
  simp only [coord, ev_act, mul_assoc, nU_mul_nU]

theorem coord_tD {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (a d : kˣ) (x : k) :
    coord (psRep μ₁ μ₂ (tD a d) f) x = bchar μ₁ μ₂ d a * coord f (x * d * ((a⁻¹ : kˣ) : k)) := by
  simp only [coord, ev_act]
  rw [wE_mul_nU_mul_tD, tD, mul_assoc, mul_assoc, ev_bor, ← mul_assoc]

theorem bchar_ne_zero (μ₁ μ₂ : kˣ →* ℂˣ) (a d : kˣ) : bchar μ₁ μ₂ a d ≠ 0 := Units.ne_zero _

@[simp] theorem bchar_one (μ₁ μ₂ : kˣ →* ℂˣ) : bchar μ₁ μ₂ 1 1 = 1 := by simp [bchar]

theorem ev_act_bor_one {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (a d : kˣ) (x : k) :
    ev (psRep μ₁ μ₂ (bor a d x) f) 1 = bchar μ₁ μ₂ a d * ev f 1 := by
  rw [ev_act, one_mul, ← mul_one (bor a d x), ev_bor]

def ball (c : k) (r : kˣ) : Set k := {z | valuation k (z - c) ≤ valuation k (r : k)}

def elemDiff (c c' : k) (r : kˣ) : k → ℂ := (ball c r).indicator 1 - (ball c' r).indicator 1

variable (k) in

def elemSpan : Submodule ℂ (k → ℂ) :=
  Submodule.span ℂ (Set.range fun p : k × k × kˣ => elemDiff p.1 p.2.1 p.2.2)

def IsLC (Φ : k → ℂ) : Prop := ∃ r : kˣ, ∀ x y : k, valuation k y ≤ valuation k (r : k) → Φ (x + y) = Φ x

def IsCS (Φ : k → ℂ) : Prop := ∃ R : kˣ, ∀ x : k, valuation k (R : k) < valuation k x → Φ x = 0

def IsEvRad (Φ : k → ℂ) : Prop :=
  ∃ R : kˣ, ∀ x y : k, valuation k (R : k) < valuation k x → valuation k x = valuation k y → Φ x = Φ y

end GlobalTheory.PrinTwo
