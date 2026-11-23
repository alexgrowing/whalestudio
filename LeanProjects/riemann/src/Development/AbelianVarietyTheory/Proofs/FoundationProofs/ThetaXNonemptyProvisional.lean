import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta MeasureTheory

namespace GlobalTheory

namespace ThetaProv

section Incl

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def coordIncl (a b : ℕ) : (Fin a → E) →ₗ[E] (Fin b → E) where
  toFun x := fun i => if h : (i : ℕ) < a then x ⟨i, h⟩ else 0
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem coordIncl_isom {a b : ℕ} (h : a ≤ b) (x y : Fin a → E) :
    Examples₂.diagForm b (fun _ => false) (coordIncl a b x) (coordIncl a b y) =
      Examples₂.diagForm a (fun _ => false) x y := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Examples₂.diagForm_apply, Examples₂.diagForm_apply, Fin.sum_univ_add]
  simp [coordIncl]

end Incl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_spaces (D : D7) (t : ℕ) :
    ∃ (X Y : ℕ → HSp D) (i : ∀ j, (X j).V →ₗ[D.host.E] (Y j).V)
      (i' : (Y D.R.m).V →ₗ[D.host.E] (X D.R.m).V),
      (∀ j, j ≤ D.R.m → (X j).rank = D.R.k + j * (t + 1)) ∧
      (∀ j, j ≤ D.R.m → (X j).SigOK ∧ (X j).IsDefinite) ∧
      (∀ j, j ≤ D.R.m → (Y j).rank = D.R.r + j * t) ∧
      (∀ j, j ≤ D.R.m → (Y j).SigOK) ∧
      (∀ j, j < D.R.m → HSpace.IsIsomEmb (X j) (Y j) (i j)) ∧
      HSpace.IsIsomEmb (Y D.R.m) (X D.R.m) i' ∧
      (t = D.R.t → (∀ j, X j = D.sp.X j) ∧ ∀ j, Y j = D.sp.Y j) := by
  by_cases ht : t = D.R.t
  · subst ht
    refine ⟨D.sp.X, D.sp.Y, D.sp.iXY, D.sp.iX'.comp D.sp.eYm.symm.toLinearMap,
      fun j hj => D.sp.X_rank j hj, fun j hj => ⟨D.sp.X_sig j, D.sp.X_def j hj⟩,
      fun j hj => D.sp.Y_rank j hj, fun j _ => D.sp.Y_sig j, fun j hj => D.sp.iXY_isom j hj, ?_,
      fun _ => ⟨fun _ => rfl, fun _ => rfl⟩⟩
    intro x y
    have h1 := D.sp.iX'_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    have h2 := D.sp.eYm_isom (D.sp.eYm.symm x) (D.sp.eYm.symm y)
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    exact h1.trans h2.symm
  · have hs : ∀ x : D.host.E, IsIntegral ℤ x → IsIntegral ℤ (star x) := Examples₂.star_isIntegral
    have hm := D.R.two_le_m
    refine ⟨fun j => Examples₂.posSpace hs (D.R.k + j * (t + 1)), fun j => Examples₂.posSpace hs (D.R.r + j * t),
      fun j => coordIncl _ _, coordIncl _ _, fun _ _ => rfl,
      fun j _ => ⟨Examples₂.posSpace_sigOK hs _, fun _ => Or.inl rfl⟩, fun _ _ => rfl,
      fun j _ => Examples₂.posSpace_sigOK hs _, fun j hj x y => coordIncl_isom ?_ x y,
      fun x y => coordIncl_isom ?_ x y, fun h => absurd h ht⟩
    · rw [mul_add, mul_one]; unfold Ranks.r; omega
    · rw [mul_add, mul_one]; unfold Ranks.r; omega

end ThetaProv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem thetaX_nonempty_provisional : ∀ D : D7, Nonempty (ThetaX D) := by
  intro D
  choose X Y i i' hXr hXs hYr hYs hi hi' hrec using ThetaProv.exists_spaces D
  exact ⟨{
    AF := fun _ => PUnit
    cusp := fun _ => ⊤
    pet := fun _ _ _ => 0
    pet_add_left := by intros; simp
    pet_smul_left := by intros; simp
    pet_right := fun _ _ => ⟨by intros; simp, by intros; simp⟩
    pet_symm := by intros; simp
    pet_pos := fun _ F h => absurd (Subsingleton.elim _ _) h
    actR := fun _ _ _ => 1
    actR_one := fun _ _ => rfl
    actR_mul := by intros; simp
    actR_cusp := by intros; trivial
    Gf := fun _ => PUnit
    actF := fun _ => 1
    actF_cusp := by intros; trivial
    actF_actR := by intros; simp
    Ksph := fun _ _ => ⊤
    Ksph_mono := fun _ _ _ _ => le_rfl
    typ := fun _ _ => ⊤
    Chr := Multiplicative (D.what₂.Tau → ℚ)
    infTy := fun χ => Multiplicative.toAdd χ
    infTy_mul := fun _ _ _ => rfl
    chrOf := fun _ n => Multiplicative.ofAdd fun τ =>
      if h : n - 1 < D.R.m then -(D.hc τ).e ⟨n - 1, h⟩ else 0
    chrOf_inf := by intro μ j τ; simp
    etaT := Multiplicative.ofAdd fun _ => 1 / 2
    etaT_inf := fun _ => Or.inl rfl
    etaT_pos := fun _ => rfl
    Sch := fun _ _ => PUnit
    fact := fun _ _ => Set.univ
    kfin := fun _ _ => ⊤
    th := fun _ _ _ _ => 0
    Xs := X
    Xs_rank := hXr
    Xs_sig := hXs
    Ys := Y
    Ys_rank := hYr
    Ys_sig := hYs
    iXYs := i
    iXYs_isom := hi
    iYXm := i'
    iYXm_isom := hi'
    YsLow := fun t j _ => Y t j
    YsLow_zero := fun _ _ => rfl
    Xs_rec := fun j _ => (hrec _ rfl).1 j
    Ys_rec := fun j _ => (hrec _ rfl).2 j
    conjAF := fun _ F => F
    conjAF_add := fun _ _ _ => rfl
    conjAF_smul := fun _ _ _ => rfl
    conjAF_conjAF := fun _ _ => rfl
    conjAF_cusp := by intros; trivial
    Pos := fun _ _ _ => Unit
    FJd := fun _ _ _ => PUnit
    Bper := fun _ _ _ _ _ _ _ => 0
    Bper_right := fun _ _ _ _ _ _ => ⟨by intros; simp, by intros; simp⟩
    Bper_add_left := by intros; simp
    Bper_smul_left := by intros; simp
    Bper_odd := by intros; rfl
    Btop := fun _ _ _ _ _ => 0
    Btop_right := fun _ _ _ _ => ⟨by intros; simp, by intros; simp⟩
    Btop_add_left := by intros; simp
    Btop_smul_left := by intros; simp
    pos1 := fun _ => ()
    posSym := fun _ => ()
    colAF := fun _ _ _ => 0
    rowAF := fun _ _ => 0
    PhiY := fun _ _ => 0
    PhiYup := fun _ _ => 0
    mY := fun _ _ => 1
    mY_pos := fun _ _ => one_pos
    adelicDataRowMeasureScale_trivialTuple := fun _ => rfl
    mY_zero := fun _ => rfl }⟩

end GlobalTheory

end
