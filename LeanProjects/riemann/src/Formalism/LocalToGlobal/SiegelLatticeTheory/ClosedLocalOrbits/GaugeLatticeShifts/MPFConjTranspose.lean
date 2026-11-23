import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.VolumeZeroFintype
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj

noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

section PFm

variable {ι : Type*}

theorem PF_add {f g : (ι → ℝ) → ℂ} (hf : f ∈ PF ι) (hg : g ∈ PF ι) : (fun y => f y + g y) ∈ PF ι :=
  Subalgebra.add_mem _ hf hg

theorem PF_sub {f g : (ι → ℝ) → ℂ} (hf : f ∈ PF ι) (hg : g ∈ PF ι) : (fun y => f y - g y) ∈ PF ι :=
  Subalgebra.sub_mem _ hf hg

theorem PF_mul {f g : (ι → ℝ) → ℂ} (hf : f ∈ PF ι) (hg : g ∈ PF ι) : (fun y => f y * g y) ∈ PF ι :=
  Subalgebra.mul_mem _ hf hg

theorem PF_sum {κ : Type*} (s : Finset κ) {f : κ → (ι → ℝ) → ℂ} (h : ∀ k ∈ s, f k ∈ PF ι) :
    (fun y => ∑ k ∈ s, f k y) ∈ PF ι := by
  have := Subalgebra.sum_mem (PF ι) h
  convert this using 1
  funext y
  simp [Finset.sum_apply]

theorem PF_prod {κ : Type*} (s : Finset κ) {f : κ → (ι → ℝ) → ℂ} (h : ∀ k ∈ s, f k ∈ PF ι) :
    (fun y => ∏ k ∈ s, f k y) ∈ PF ι := by
  have := Subalgebra.prod_mem (PF ι) h
  convert this using 1
  funext y
  simp [Finset.prod_apply]

def MPF {α β : Type*} (M : (ι → ℝ) → Matrix α β ℂ) : Prop := ∀ i j, (fun y => M y i j) ∈ PF ι

variable {α β γ : Type*}

theorem MPF_const (A : Matrix α β ℂ) : MPF (ι := ι) (fun _ => A) := fun _ _ => PF_const _

theorem MPF_add {M N : (ι → ℝ) → Matrix α β ℂ} (hM : MPF M) (hN : MPF N) : MPF (fun y => M y + N y) :=
  fun i j => PF_add (hM i j) (hN i j)

theorem MPF_sub {M N : (ι → ℝ) → Matrix α β ℂ} (hM : MPF M) (hN : MPF N) : MPF (fun y => M y - N y) :=
  fun i j => PF_sub (hM i j) (hN i j)

theorem MPF_mul [Fintype β] {M : (ι → ℝ) → Matrix α β ℂ} {N : (ι → ℝ) → Matrix β γ ℂ} (hM : MPF M) (hN : MPF N) :
    MPF (fun y => M y * N y) := fun i j => by
  simp only [Matrix.mul_apply]
  exact PF_sum _ fun k _ => PF_mul (hM i k) (hN k j)

theorem MPF_smul {f : (ι → ℝ) → ℂ} {M : (ι → ℝ) → Matrix α β ℂ} (hf : f ∈ PF ι) (hM : MPF M) :
    MPF (fun y => f y • M y) := fun i j => by
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact PF_mul hf (hM i j)

theorem MPF_conjTranspose {M : (ι → ℝ) → Matrix α β ℂ} (hM : MPF M) : MPF (fun y => (M y)ᴴ) := fun i j => by
  simp only [conjTranspose_apply]
  exact PF_conj (hM j i)

theorem MPF_submatrix {α' β' : Type*} {M : (ι → ℝ) → Matrix α β ℂ} (hM : MPF M) (f : α' → α) (g : β' → β) :
    MPF (fun y => (M y).submatrix f g) := fun i j => hM (f i) (g j)

theorem PF_det [Fintype α] [DecidableEq α] {M : (ι → ℝ) → Matrix α α ℂ} (hM : MPF M) :
    (fun y => (M y).det) ∈ PF ι := by
  have h : (fun y => (M y).det) =
      fun y => ∑ σ : Equiv.Perm α, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M y (σ i) i := by
    funext y
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [h]
  exact PF_sum _ fun σ _ => PF_mul (PF_const _) (PF_prod _ fun i _ => hM _ _)

theorem MPF_updateRow [DecidableEq α] {M : (ι → ℝ) → Matrix α β ℂ} (hM : MPF M) (j : α) (v : β → ℂ) :
    MPF (fun y => (M y).updateRow j v) := fun i k => by
  by_cases h : i = j
  · subst h
    simp only [updateRow_self]
    exact PF_const _
  · simp only [updateRow_ne h]
    exact hM i k

theorem MPF_adjugate [Fintype α] [DecidableEq α] {M : (ι → ℝ) → Matrix α α ℂ} (hM : MPF M) :
    MPF (fun y => (M y).adjugate) := fun i j => by
  simp only [adjugate_apply]
  exact PF_det (MPF_updateRow hM j _)

end PFm

section Coords

variable {ι : Type*} {n r : ℕ}

theorem PF_Dl {Z : (ι → ℝ) → Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hZ : MPF Z) (l : ℕ) :
    (fun y => Dl (Z y) l) ∈ PF ι := by
  by_cases h : l ≤ r + 1
  · simp only [Dl, dif_pos h]
    exact PF_det (MPF_submatrix hZ _ _)
  · simp only [Dl, dif_neg h]
    exact PF_const 0

theorem hJ_eq_sum (ε : Fin n → Bool) (x v : Fin n → ℂ) :
    hJ ε x v = ∑ i, (star x ᵥ* Formalism.REAL.Jm ε) i * v i := by
  unfold hJ
  rw [Matrix.dotProduct_mulVec]
  rfl

theorem MPF_Zhat (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) {M : (ι → ℝ) → Matrix (Fin n) (Fin n) ℂ}
    (hM : MPF M) : MPF (fun y => Zhat ε f f' (M y)) := fun a b => by
  simp only [Zhat, hJ_eq_sum, mulVec, dotProduct]
  exact PF_sum _ fun i _ => PF_mul (PF_const _) (PF_sum _ fun k _ => PF_mul (hM i k) (PF_const _))

theorem Zhat_smul (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (c : ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Zhat ε f f' (c • g) = c • Zhat ε f f' g := by
  funext a b
  simp only [Zhat, Matrix.smul_apply, smul_eq_mul, Matrix.smul_mulVec, UnitaryIsometries.hJ_smul_right]

theorem Dl_smul (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (c : ℂ) (l : ℕ) (hl : l ≤ r + 1) :
    Dl (c • Z) l = c ^ l * Dl Z l := by
  simp only [Dl, dif_pos hl]
  rw [show (c • Z).submatrix (Fin.castLE hl) (Fin.castLE hl) = c • Z.submatrix (Fin.castLE hl) (Fin.castLE hl)
    from rfl, Matrix.det_smul, Fintype.card_fin]

def Fval (T T' : ℝ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ℂ :=
  (∏ l ∈ Finset.Icc 1 r, Dl Z l) * (Gv T T' Z : ℂ)

theorem isReg_iff (T T' : ℝ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : IsReg T T' Z ↔ Fval T T' Z ≠ 0 := by
  simp only [IsReg, Fval, ne_eq, mul_eq_zero, not_or, Finset.prod_eq_zero_iff, Finset.mem_Icc, not_exists,
    not_and, Complex.ofReal_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun l hl => h1 l hl.1 hl.2, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun l hl1 hl2 => h1 l ⟨hl1, hl2⟩, h2⟩

def Qexpr (T T' : ℝ) (Z0 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (d : ℂ) : ℂ :=
  (∏ l ∈ Finset.Icc 1 r, Dl Z0 l) *
    (Dl Z0 (r + 1) * conj (Dl Z0 (r + 1)) - ((T * T' : ℝ) : ℂ) * (d * conj d) * (Dl Z0 r * conj (Dl Z0 r)))

theorem Qexpr_smul (T T' : ℝ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (d : ℂ) :
    Qexpr T T' (d • Z) d = ((∏ l ∈ Finset.Icc 1 r, d ^ l) * (d * conj d) ^ (r + 1)) * Fval T T' Z := by
  have hprod : ∏ l ∈ Finset.Icc 1 r, Dl (d • Z) l =
      (∏ l ∈ Finset.Icc 1 r, d ^ l) * ∏ l ∈ Finset.Icc 1 r, Dl Z l := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l hl => Dl_smul Z d l ?_
    have := (Finset.mem_Icc.1 hl).2
    omega
  rw [Qexpr, Fval, hprod, Dl_smul Z d (r + 1) le_rfl, Dl_smul Z d r (Nat.le_succ r), Gv]
  push_cast
  rw [← Complex.mul_conj', ← Complex.mul_conj']
  simp only [map_mul, map_pow]
  ring

theorem continuous_Fval (T T' : ℝ) : Continuous (Fval (r := r) T T') := by
  have hD : ∀ l, Continuous fun Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ => Dl Z l := by
    intro l
    by_cases h : l ≤ r + 1
    · simp only [Dl, dif_pos h]
      exact (continuous_id.matrix_submatrix _ _).matrix_det
    · simp only [Dl, dif_neg h]
      exact continuous_const
  unfold Fval Gv
  refine (continuous_finset_prod _ fun l _ => hD l).mul (Complex.continuous_ofReal.comp ?_)
  exact (((hD _).norm.pow 2).sub (continuous_const.mul ((hD _).norm.pow 2)))

end Coords

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
