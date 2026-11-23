import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.BesselMapUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply

open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms

abbrev Ix (k r : ℕ) := Fin (2 * r + k + 1)

abbrev Mx (k r : ℕ) := Matrix (Ix k r) (Ix k r) ℂ

def Kmax (k r : ℕ) : Set (Mx k r) := UH (Hpk k r) ∩ (Matrix.unitaryGroup (Ix k r) ℂ : Set _)

structure HRep (k r : ℕ) : Type 1 where

  H : Type
  [instNorm : NormedAddCommGroup H]
  [instInner : InnerProductSpace ℂ H]
  [instComplete : CompleteSpace H]

  σ : Mx k r → (H →L[ℂ] H)
  isURep : IsURepOn (UH (Hpk k r)) σ

attribute [instance] HRep.instNorm HRep.instInner HRep.instComplete

variable {k r : ℕ}

def HRep.smooth (R : HRep k r) : Set R.H := smoothVecs (k := k) (r := r) R.σ

def HRep.IsDiscrete (R : HRep k r) (ε : Ix k r → Bool) (μ : Ix k r → ℝ) : Prop :=
  IsHCParam μ ∧ IsDSHpk k r ε μ R.σ

def LieWord (k r : ℕ) (w : List (Mx k r)) : Prop := ∀ X ∈ w, InLieHpk k r X

def HRep.semi (R : HRep k r) (Ws : List (List (Mx k r))) (v : R.H) : ℝ :=
  (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum

structure IsSmoothMap (R₁ R₂ : HRep k r) (A : R₁.H → R₂.H) : Prop where
  maps : ∀ v ∈ R₁.smooth, A v ∈ R₂.smooth
  map_add : ∀ v ∈ R₁.smooth, ∀ w ∈ R₁.smooth, A (v + w) = A v + A w
  map_smul : ∀ (a : ℂ), ∀ v ∈ R₁.smooth, A (a • v) = a • A v
  cont : ∀ w, LieWord k r w → ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ w' ∈ Ws, LieWord k r w') ∧
    ∀ v ∈ R₁.smooth, ‖dsigW (k := k) (r := r) R₂.σ w (A v)‖ ≤ C * R₁.semi Ws v

section Tensor

variable {ι : Type} [Fintype ι]

def tensSmooth (ι : Type) (R : HRep k r) : Set (ι → R.H) := {x | ∀ c, x c ∈ R.smooth}

def tensAct (ρ : Mx k r → Matrix ι ι ℂ) (R : HRep k r) (g : Mx k r) (x : ι → R.H) : ι → R.H :=
  fun c => ∑ d, ρ g c d • R.σ g (x d)

def pureT {E : Type} [AddCommGroup E] [Module ℂ E] (a : ι → ℂ) (v : E) : ι → E := fun c => a c • v

def tensForm (A : Matrix ι ι ℂ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : ι → H) : ℂ :=
  ∑ c, ∑ d, A c d * ⟪y c, x d⟫_ℂ

def flat (A : Matrix ι ι ℂ) (y : ι → ℂ) : ι → ℂ := star y ᵥ* A

def contr (A : Matrix ι ι ℂ) (ω : ι → ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] (x : ι → E) : E :=
  ∑ d, flat A ω d • x d

def IsSmoothMapInto (R₁ R : HRep k r) (A : R₁.H → ι → R.H) : Prop :=
  ∀ c, IsSmoothMap R₁ R fun v => A v c

structure IsSmoothMapFrom (R R₂ : HRep k r) (A : (ι → R.H) → R₂.H) : Prop where
  maps : ∀ x ∈ tensSmooth ι R, A x ∈ R₂.smooth
  map_add : ∀ x ∈ tensSmooth ι R, ∀ y ∈ tensSmooth ι R, A (x + y) = A x + A y
  map_smul : ∀ (a : ℂ), ∀ x ∈ tensSmooth ι R, A (a • x) = a • A x
  cont : ∀ w, LieWord k r w → ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ w' ∈ Ws, LieWord k r w') ∧
    ∀ x ∈ tensSmooth ι R, ‖dsigW (k := k) (r := r) R₂.σ w (A x)‖ ≤ C * ∑ c, R.semi Ws (x c)

structure IsSmoothDecomp (ρ : Mx k r → Matrix ι ι ℂ) (R : HRep k r) {J : Type} [Fintype J] (Rs : J → HRep k r)
    (io : ∀ j, (Rs j).H → ι → R.H) (p : ∀ j, (ι → R.H) → (Rs j).H) : Prop where
  io_cont : ∀ j, IsSmoothMapInto (Rs j) R (io j)
  p_cont : ∀ j, IsSmoothMapFrom R (Rs j) (p j)
  io_equiv : ∀ j, ∀ g ∈ UH (Hpk k r), ∀ v ∈ (Rs j).smooth, io j ((Rs j).σ g v) = tensAct ρ R g (io j v)
  p_equiv : ∀ j, ∀ g ∈ UH (Hpk k r), ∀ x ∈ tensSmooth ι R, p j (tensAct ρ R g x) = (Rs j).σ g (p j x)
  p_io : ∀ j, ∀ v ∈ (Rs j).smooth, p j (io j v) = v
  p_io_ne : ∀ i j, i ≠ j → ∀ v ∈ (Rs j).smooth, p i (io j v) = 0
  sum_io_p : ∀ x ∈ tensSmooth ι R, ∑ j, io j (p j x) = x

structure IsSignedDecomp (ρ : Mx k r → Matrix ι ι ℂ) (A : Matrix ι ι ℂ) (R : HRep k r) {J : Type} [Fintype J]
    (Rs : J → HRep k r) (io : ∀ j, (Rs j).H → ι → R.H) (p : ∀ j, (ι → R.H) → (Rs j).H) (ep : J → ℝ) : Prop
    extends IsSmoothDecomp ρ R Rs io p where
  sign : ∀ j, ep j = 1 ∨ ep j = -1
  form_eq : ∀ j, ∀ x ∈ (Rs j).smooth, ∀ y ∈ (Rs j).smooth, tensForm A (io j x) (io j y) = (ep j : ℂ) * ⟪y, x⟫_ℂ
  orth : ∀ i j, i ≠ j → ∀ x ∈ (Rs i).smooth, ∀ y ∈ (Rs j).smooth, tensForm A (io i x) (io j y) = 0

variable [DecidableEq ι]

structure IsFormRep (k r : ℕ) (ρ : Mx k r → Matrix ι ι ℂ) (A : Matrix ι ι ℂ) (l : ℕ) : Prop where
  map_one : ρ 1 = 1
  map_mul : ∀ g ∈ UH (Hpk k r), ∀ g' ∈ UH (Hpk k r), ρ (g * g') = ρ g * ρ g'
  smooth : ∀ c d, SmoothOnH (Hpk k r) fun g => ρ g c d
  herm : Aᴴ = A
  sq : A * A = 1
  inv : ∀ g ∈ UH (Hpk k r), (ρ g)ᴴ * A * ρ g = A
  unitK : ∀ g ∈ Kmax k r, ρ g ∈ Matrix.unitaryGroup ι ℂ
  growth : ∃ C : ℝ, ∀ g ∈ UH (Hpk k r), ∀ c d, ‖ρ g c d‖ ≤ C * Real.sqrt (hs g) ^ l

def dualRep (ρ : Mx k r → Matrix ι ι ℂ) (g : Mx k r) : Matrix ι ι ℂ := (ρ g⁻¹)ᵀ

def dualGram (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := (A⁻¹)ᵀ

end Tensor

def stdRep (k r : ℕ) (g : Mx k r) : Mx k r := g

def stdDualRep (k r : ℕ) : Mx k r → Mx k r := dualRep (stdRep k r)

abbrev Sub (n l : ℕ) := {I : Finset (Fin n) // I.card = l}

def Sub.enum {n l : ℕ} (I : Sub n l) : Fin l → Fin n := I.1.orderEmbOfFin I.2

def wedgeMat {n : ℕ} (l : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n l) (Sub n l) ℂ :=
  Matrix.of fun I I' => (g.submatrix I.enum I'.enum).det

def wedgeVec {n l : ℕ} (x : Fin l → Fin n → ℂ) : Sub n l → ℂ :=
  fun I => (Matrix.of fun a b : Fin l => x b (I.enum a)).det

def wedgeRep (k r l : ℕ) (g : Mx k r) : Matrix (Sub (2 * r + k + 1) l) (Sub (2 * r + k + 1) l) ℂ := wedgeMat l g

def wedgeGram (k r l : ℕ) : Matrix (Sub (2 * r + k + 1) l) (Sub (2 * r + k + 1) l) ℂ := wedgeMat l (Hpk k r)

def flagVec (k r : ℕ) (z : Ix k r → ℂ) (a : Fin (r + 1)) : Ix k r → ℂ :=
  if h : a.val < r then bvec (eI k r ⟨a.val, h⟩) else z

def flagWedge {k r l : ℕ} (hl : l ≤ r + 1) (f : Fin (r + 1) → Ix k r → ℂ) : Sub (2 * r + k + 1) l → ℂ :=
  wedgeVec fun a => f (Fin.castLE hl a)

def flatV (k r : ℕ) (f : Ix k r → ℂ) : Ix k r → ℂ := flat (Hpk k r) f

def shiftUp {n : ℕ} (μ : Fin n → ℝ) (I : Finset (Fin n)) : Fin n → ℝ := fun a => μ a + if a ∈ I then 1 else 0

def shiftDown {n : ℕ} (μ : Fin n → ℝ) (I : Finset (Fin n)) : Fin n → ℝ := fun a => μ a - if a ∈ I then 1 else 0

section Checks

variable {ι : Type} [Fintype ι]

theorem flat_dotProduct (A : Matrix ι ι ℂ) (y a : ι → ℂ) : flat A y ⬝ᵥ a = herm A a y := by
  simp [flat, herm, Matrix.dotProduct_mulVec]

theorem tensForm_pure (A : Matrix ι ι ℂ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b : ι → ℂ) (v w : H) : tensForm A (pureT a v) (pureT b w) = herm A a b * ⟪w, v⟫_ℂ := by
  simp only [tensForm, pureT, herm, dotProduct, Matrix.mulVec, inner_smul_left, inner_smul_right, Finset.sum_mul,
    Finset.mul_sum, Pi.star_apply, Complex.star_def]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem contr_pure (A : Matrix ι ι ℂ) (ω a : ι → ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] (v : E) :
    contr A ω (pureT a v) = herm A a ω • v := by
  simp only [contr, pureT, smul_smul, ← Finset.sum_smul, ← flat_dotProduct, dotProduct]

theorem tensAct_pure (ρ : Mx k r → Matrix ι ι ℂ) (R : HRep k r) (g : Mx k r) (a : ι → ℂ) (v : R.H) :
    tensAct ρ R g (pureT a v) = pureT (ρ g *ᵥ a) (R.σ g v) := by
  funext c
  simp only [tensAct, pureT, map_smul, smul_smul, ← Finset.sum_smul, Matrix.mulVec, dotProduct]

theorem herm_dualGram_flat [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : Aᴴ = A) (h2 : A * A = 1) (y y' : ι → ℂ) :
    herm (dualGram A) (flat A y) (flat A y') = herm A y' y := by
  have hinv : A⁻¹ = A := Matrix.inv_eq_left_inv h2
  have h1 : star (star y' ᵥ* A) = A *ᵥ y' := by
    rw [Matrix.star_vecMul, hA, star_star]
  unfold herm dualGram flat
  rw [hinv, h1, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, h2, Matrix.vecMul_one, dotProduct_comm]

theorem norm_det_of_mem {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : ‖g.det‖ = 1 := by
  have h0 : (Hpk k r).det ≠ 0 := by
    intro h
    have := congrArg Matrix.det (PI.HwUniqW.Hpk_mul_self (k := k) (r := r))
    simp [h] at this
  have h1 := congrArg Matrix.det (show gᴴ * Hpk k r * g = Hpk k r from hg)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h1
  have h2 : star g.det * g.det = 1 := by
    apply mul_right_cancel₀ h0
    linear_combination h1
  have h3 := congrArg norm h2
  rw [norm_mul, norm_star, norm_one] at h3
  nlinarith [norm_nonneg g.det]

def detRep (k r : ℕ) : HRep k r where
  H := ℂ
  σ g := g.det • ContinuousLinearMap.id ℂ ℂ
  isURep := by
    refine ⟨⟨?_, fun a _ b _ => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
    · ext; simp
    · ext; simp [mul_comm]
    · simp [norm_det_of_mem hg]
    · refine Continuous.continuousOn ?_
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      exact (continuous_id.matrix_det).mul continuous_const

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem isFormRep_std (k r : ℕ) : IsFormRep k r (stdRep k r) (Hpk k r) 1 where
  map_one := rfl
  map_mul _ _ _ _ := rfl
  smooth c d g₀ _ := ⟨Set.univ, fun g => g c d, isOpen_univ, Set.mem_univ _,
    (contDiff_pi.1 (contDiff_pi.1 (contDiff_id (E := Ix k r → Ix k r → ℂ)) c) d).contDiffOn, fun _ _ _ => rfl⟩
  herm := PI.HwUniqW.Hpk_conjTranspose
  sq := PI.HwUniqW.Hpk_mul_self
  inv _ hg := hg
  unitK _ hg := hg.2
  growth := ⟨1, fun g _ c d => by
    rw [one_mul, pow_one]
    apply Real.le_sqrt_of_sq_le
    unfold hs stdRep
    calc ‖g c d‖ ^ 2 ≤ ∑ j, ‖g c j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖g c j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ d)
      _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ j, ‖g i j‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ c)⟩

theorem dsigW_zero (R : HRep k r) (w : List (Mx k r)) : dsigW (k := k) (r := r) R.σ w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons X w ih => simp [dsigW, ih, dsig]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem zero_mem_smooth (R : HRep k r) : (0 : R.H) ∈ R.smooth := fun g₀ _ =>
  ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => by simp⟩

theorem isSignedDecomp_trivial [DecidableEq ι] (R : HRep k r) (ep : ι → ℝ) (hep : ∀ c, ep c = 1 ∨ ep c = -1) :
    IsSignedDecomp (fun _ => (1 : Matrix ι ι ℂ)) (Matrix.diagonal fun c => (ep c : ℂ)) R (fun _ : ι => R)
      (fun j v => Pi.single j v) (fun j x => x j) ep := by
  have hact : ∀ g (x : ι → R.H), tensAct (fun _ => (1 : Matrix ι ι ℂ)) R g x = fun c => R.σ g (x c) := by
    intro g x; funext c
    simp [tensAct, Matrix.one_apply]
  have hform : ∀ x y : ι → R.H, tensForm (Matrix.diagonal fun c => (ep c : ℂ)) x y =
      ∑ c, (ep c : ℂ) * ⟪y c, x c⟫_ℂ := by
    intro x y
    simp [tensForm, Matrix.diagonal_apply]
  refine ⟨⟨fun j c => ?_, fun j => ⟨fun x hx => hx j, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun w hw => ?_⟩,
    fun j g _ v _ => ?_, fun j g _ x _ => by rw [hact], fun j v _ => by simp, fun i j h v _ => by simp [h],
    fun x _ => Finset.univ_sum_single x⟩, hep, fun j x _ y _ => ?_, fun i j h x _ y _ => ?_⟩
  · by_cases h : c = j
    · subst h
      simp only [Pi.single_eq_same]
      exact ⟨fun _ hv => hv, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
        fun w hw => ⟨1, [w], by simpa using hw, fun v _ => by simp [HRep.semi]⟩⟩
    · simp only [Pi.single_eq_of_ne h]
      exact ⟨fun _ _ => zero_mem_smooth R, fun _ _ _ _ => by simp, fun _ _ _ => by simp,
        fun w _ => ⟨0, [], by simp, fun v _ => by simp [dsigW_zero]⟩⟩
  · refine ⟨1, [w], by simpa using hw, fun x _ => ?_⟩
    simp only [HRep.semi, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
    exact Finset.single_le_sum (f := fun c => ‖dsigW (k := k) (r := r) R.σ w (x c)‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)
  · rw [hact]; funext c
    by_cases h : c = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · rw [hform, Finset.sum_eq_single j (fun c _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]
    simp
  · rw [hform]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c = i
    · subst hc; simp [Pi.single_eq_of_ne h]
    · simp [Pi.single_eq_of_ne hc]

end Checks

end GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms

end
