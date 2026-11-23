import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.BasicNotions.Examples₂ NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ext

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def extZ (n n' : ℕ) : (Fin n → E) →ₗ[E] (Fin n' → E) where
  toFun x := fun i => if h : i.1 < n then x ⟨i.1, h⟩ else 0
  map_add' x y := by
    funext i
    by_cases h : i.1 < n <;> simp [h]
  map_smul' c x := by
    funext i
    by_cases h : i.1 < n <;> simp [h]

theorem sum_extZ (n n' : ℕ) (hn : n ≤ n') (g : Fin n → E) :
    ∑ i : Fin n', (if h : i.1 < n then g ⟨i.1, h⟩ else 0) = ∑ i, g i := by
  have h1 := Fin.sum_univ_eq_sum_range (fun i : ℕ => if h : i < n then g ⟨i, h⟩ else 0) n'
  have h2 := Fin.sum_univ_eq_sum_range (fun i : ℕ => if h : i < n then g ⟨i, h⟩ else 0) n
  rw [h1, ← Finset.sum_subset (Finset.range_subset_range.2 hn), ← h2]
  · exact Finset.sum_congr rfl fun i _ => by rw [dif_pos i.2]
  · intro i _ hi
    rw [dif_neg (by simpa using hi)]

theorem extZ_form (n n' : ℕ) (hn : n ≤ n') (x y : Fin n → E) :
    diagForm n' (fun _ => false) (extZ n n' x) (extZ n n' y) = diagForm n (fun _ => false) x y := by
  rw [diagForm_apply, diagForm_apply, ← sum_extZ n n' hn]
  refine Finset.sum_congr rfl fun i _ => ?_
  show star (if h : i.1 < n then x ⟨i.1, h⟩ else 0) * _ * (if h : i.1 < n then y ⟨i.1, h⟩ else 0) = _
  by_cases h : i.1 < n <;> simp [h]

theorem extZ_isom (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (n n' : ℕ) (hn : n ≤ n') :
    HSpace.IsIsomEmb (posSpace hstar n) (posSpace hstar n') (extZ n n') :=
  fun x y => extZ_form n n' hn x y

end Ext

structure Tow (D : D7) (t : ℕ) where
  Xs : ℕ → HSp D
  Xs_rank : ∀ j, j ≤ D.R.m → (Xs j).rank = D.R.k + j * (t + 1)
  Xs_sig : ∀ j, j ≤ D.R.m → (Xs j).SigOK ∧ (Xs j).IsDefinite
  Ys : ℕ → HSp D
  Ys_rank : ∀ j, j ≤ D.R.m → (Ys j).rank = D.R.r + j * t
  Ys_sig : ∀ j, j ≤ D.R.m → (Ys j).SigOK
  iXYs : ∀ j, (Xs j).V →ₗ[D.host.E] (Ys j).V
  iXYs_isom : ∀ j, j < D.R.m → HSpace.IsIsomEmb (Xs j) (Ys j) (iXYs j)
  iYXm : (Ys D.R.m).V →ₗ[D.host.E] (Xs D.R.m).V
  iYXm_isom : HSpace.IsIsomEmb (Ys D.R.m) (Xs D.R.m) iYXm

def recTow (D : D7) : Tow D D.R.t where
  Xs := D.sp.X
  Xs_rank := fun j hj => D.sp.X_rank j hj
  Xs_sig := fun j hj => ⟨D.sp.X_sig j, D.sp.X_def j hj⟩
  Ys := D.sp.Y
  Ys_rank := fun j hj => D.sp.Y_rank j hj
  Ys_sig := fun j _ => D.sp.Y_sig j
  iXYs := D.sp.iXY
  iXYs_isom := D.sp.iXY_isom
  iYXm := D.sp.iX'.comp D.sp.eYm.symm.toLinearMap
  iYXm_isom := fun x y => by
    have h1 := D.sp.iX'_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    have h2 := D.sp.eYm_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    exact h1.trans h2.symm

def stdTow (D : D7) (t : ℕ) : Tow D t where
  Xs := fun j => posSpace star_isIntegral (D.R.k + j * (t + 1))
  Xs_rank := fun _ _ => rfl
  Xs_sig := fun _ _ => ⟨posSpace_sigOK _ _, fun _ => Or.inl rfl⟩
  Ys := fun j => posSpace star_isIntegral (D.R.r + j * t)
  Ys_rank := fun _ _ => rfl
  Ys_sig := fun _ _ => posSpace_sigOK _ _
  iXYs := fun _ => extZ _ _
  iXYs_isom := fun j hj => extZ_isom _ _ _ (by
    have := D.R.two_le_m
    unfold Ranks.r
    rw [Nat.mul_succ]
    omega)
  iYXm := extZ _ _
  iYXm_isom := extZ_isom _ _ _ (by
    have := D.R.two_le_m
    unfold Ranks.r
    rw [Nat.mul_succ]
    omega)

open Classical in

def tow (D : D7) (t : ℕ) : Tow D t := if h : t = D.R.t then h ▸ recTow D else stdTow D t

theorem tow_rec (D : D7) : tow D D.R.t = recTow D := by
  unfold tow
  rw [dif_pos rfl]

def chrExp (D : D7) (j : ℕ) : D.what₂.Tau → ℚ := fun τ =>
  if h : 1 ≤ j ∧ j ≤ D.R.m then -(D.hc τ).e ⟨j - 1, by omega⟩ else 0

def thetaZero (D : D7) : ThetaX D where
  AF := fun _ => PUnit
  cusp := fun _ => ⊤
  pet := fun _ _ _ => 0
  pet_add_left := fun _ _ _ _ => by simp
  pet_smul_left := fun _ _ _ _ => by simp
  pet_right := fun _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  pet_symm := fun _ _ _ => by simp
  pet_pos := fun _ F hF => absurd (Subsingleton.elim F 0) hF
  actR := fun _ _ _ => 1
  actR_one := fun _ _ => rfl
  actR_mul := fun _ _ _ _ _ _ => (one_mul _).symm
  actR_cusp := fun _ _ _ _ _ _ => Submodule.mem_top
  Gf := fun _ => PUnit
  actF := fun _ => 1
  actF_cusp := fun _ _ _ _ => Submodule.mem_top
  actF_actR := fun _ _ _ _ => rfl
  Ksph := fun _ _ => ⊤
  Ksph_mono := fun _ _ _ _ => le_refl _
  typ := fun _ _ => ⊤
  Chr := Multiplicative (D.what₂.Tau → ℚ)
  infTy := fun χ τ => Multiplicative.toAdd χ τ
  infTy_mul := fun _ _ _ => rfl
  chrOf := fun _ j => Multiplicative.ofAdd (chrExp D j)
  chrOf_inf := fun _ j τ => by
    show chrExp D (j.1 + 1) τ = _
    unfold chrExp
    rw [dif_pos ⟨Nat.le_add_left _ _, j.2⟩]
    rfl
  etaT := Multiplicative.ofAdd fun _ => 1 / 2
  etaT_inf := fun _ => Or.inl rfl
  etaT_pos := fun _ => rfl
  Sch := fun _ _ => PUnit
  fact := fun _ _ => Set.univ
  kfin := fun _ _ => ⊤
  th := fun _ _ _ _ => 0
  Xs := fun t => (tow D t).Xs
  Xs_rank := fun t => (tow D t).Xs_rank
  Xs_sig := fun t => (tow D t).Xs_sig
  Ys := fun t => (tow D t).Ys
  Ys_rank := fun t => (tow D t).Ys_rank
  Ys_sig := fun t => (tow D t).Ys_sig
  iXYs := fun t => (tow D t).iXYs
  iXYs_isom := fun t => (tow D t).iXYs_isom
  iYXm := fun t => (tow D t).iYXm
  iYXm_isom := fun t => (tow D t).iYXm_isom
  YsLow := fun t j _ => (tow D t).Ys j
  YsLow_zero := fun _ _ => rfl
  Xs_rec := fun j _ => by rw [tow_rec]; rfl
  Ys_rec := fun j _ => by rw [tow_rec]; rfl
  conjAF := fun _ F => F
  conjAF_add := fun _ _ _ => rfl
  conjAF_smul := fun _ _ _ => rfl
  conjAF_conjAF := fun _ _ => rfl
  conjAF_cusp := fun _ _ h => h
  Pos := fun _ _ _ => PUnit
  FJd := fun _ _ _ => PUnit
  Bper := fun _ _ _ _ _ _ _ => 0
  Bper_right := fun _ _ _ _ _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  Bper_add_left := fun _ _ _ _ _ _ _ _ => by simp
  Bper_smul_left := fun _ _ _ _ _ _ _ _ => by simp
  Bper_odd := fun _ _ _ _ _ _ _ _ _ => rfl
  Btop := fun _ _ _ _ _ => 0
  Btop_right := fun _ _ _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  Btop_add_left := fun _ _ _ _ _ _ => by simp
  Btop_smul_left := fun _ _ _ _ _ _ => by simp
  pos1 := fun _ => PUnit.unit
  posSym := fun _ => PUnit.unit
  colAF := fun _ _ _ => 0
  rowAF := fun _ _ => 0
  PhiY := fun _ _ => PUnit.unit
  PhiYup := fun _ _ => PUnit.unit
  mY := fun _ _ => 1
  mY_pos := fun _ _ => one_pos
  adelicDataRowMeasureScale_trivialTuple := fun _ => rfl
  mY_zero := fun _ => rfl

theorem thetaZero_row (D : D7) [∀ μ j, Subsingleton (D.what₂.Mult μ j)] : (thetaZero D).TieRowIsom :=
  fun μ j _ x y => by
    rw [Subsingleton.elim x 0, inner_zero_left]
    exact mul_zero _

theorem thetaZero_io (D : D7) [∀ μ j, Subsingleton (D.what₂.Mult μ j)] : (thetaZero D).TieIo :=
  fun μ j _ y x => by
    rw [Subsingleton.elim x 0, inner_zero_right]
    exact mul_zero _

theorem thetaZero_bm (D : D7) (h : ∀ u μ φ F, D.what₂.perCol u μ φ F = 0) : (thetaZero D).TieBm :=
  fun u μ φ F => (h u μ φ F).trans (mul_zero _).symm

end Formalism.MainNotions.Inhab

end
