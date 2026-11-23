import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylCharacterRegularity.AlgInfCharIff

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh Topology

namespace UpperTheory.V.WeylC

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

omit [NumberField E] in
theorem extGL_one (f : GL (Fin a) (Cinf E) → ℂ) : extGL f (oneL E a) = f 1 := extGL_val f 1

theorem IsReg.diff {ι κ : Type} {M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ} (h : IsReg M) (i : ι) (j : κ) :
    HasFDerivAt (extGL fun y => M y i j) (fderiv ℝ (extGL fun y => M y i j) (oneL E a)) (oneL E a) :=
  (differentiableAt_extGL (h i j) (x := oneL E a) isUnit_one).hasFDerivAt

omit [NumberField E] in
theorem isReg_conj {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ] {M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ} (h : IsReg M)
    (B : Matrix ι' ι ℂ) (A : Matrix κ κ' ℂ) : IsReg fun y => B * M y * A := fun i j => by
  have e : (fun y => (B * M y * A) i j) = ∑ l, ∑ k, (B i k * A l j) • fun y => M y k l := by
    funext y
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  exact Subalgebra.sum_mem _ fun l _ => Subalgebra.sum_mem _ fun k _ => Subalgebra.smul_mem _ (h k l) _

theorem dOf_conj {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ] {M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ} (h : IsReg M)
    (B : Matrix ι' ι ℂ) (A : Matrix κ κ' ℂ) (X : Lie E a) : dOf (fun y => B * M y * A) X = B * dOf M X * A := by
  ext i j
  have h1 := HasFDerivAt.fun_sum (u := Finset.univ) fun l _ =>
    (HasFDerivAt.fun_sum (u := Finset.univ) fun k _ => (h.diff k l).const_mul (B i k)).mul_const (A l j)
  have h2 := h1.congr_of_eventuallyEq (extGL_eventuallyEq (f := fun y => (B * M y * A) i j)
    (fun y => by simp only [extGL_val, Matrix.mul_apply]) (x := oneL E a) isUnit_one)
  rw [dOf, Matrix.of_apply, h2.fderiv]
  simp [Matrix.mul_apply, dOf, mul_comm]

theorem eOf_conj {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ] {M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ} (h : IsReg M)
    (B : Matrix ι' ι ℂ) (A : Matrix κ κ' ℂ) (τ : E →+* ℂ) (i j : Fin a) :
    eOf (fun y => B * M y * A) τ i j = B * eOf M τ i j * A := by
  simp only [eOf, dOf_conj h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

variable {T κ : Type} [Fintype T] [DecidableEq T] [Fintype κ] [DecidableEq κ]

omit [NumberField E] in
theorem isReg_piK {M : T → GL (Fin a) (Cinf E) → Matrix κ κ ℂ} (h : ∀ t, IsReg (M t)) :
    IsReg fun y => piK fun t => M t y := fun f g => by
  have e : (fun y => piK (fun t => M t y) f g) = ∏ t, fun y => M t y (f t) (g t) := by
    funext y; simp [piK_apply]
  rw [e]
  exact Subalgebra.prod_mem _ fun t _ => h t _ _

theorem dOf_piK {M : T → GL (Fin a) (Cinf E) → Matrix κ κ ℂ} (h : ∀ t, IsReg (M t)) (h1 : ∀ t, M t 1 = 1) (X : Lie E a) :
    dOf (fun y => piK fun t => M t y) X = ∑ t, intersection_update_fsHerm_neg_one t (dOf (M t) X) := by
  ext f g
  have h2 := HasFDerivAt.finset_prod (u := Finset.univ) fun t _ => (h t).diff (f t) (g t)
  have h3 := h2.congr_of_eventuallyEq (extGL_eventuallyEq (f := fun y => piK (fun t => M t y) f g)
    (fun y => by simp only [extGL_val, piK_apply]) (x := oneL E a) isUnit_one)
  rw [dOf, Matrix.of_apply, h3.fderiv]
  simp [Matrix.sum_apply, position_apply, dOf, extGL_one, h1, mul_comm]

theorem eOf_piK {M : T → GL (Fin a) (Cinf E) → Matrix κ κ ℂ} (h : ∀ t, IsReg (M t)) (h1 : ∀ t, M t 1 = 1)
    (τ : E →+* ℂ) (i j : Fin a) : eOf (fun y => piK fun t => M t y) τ i j = ∑ t, intersection_update_fsHerm_neg_one t (eOf (M t) τ i j) := by
  simp only [eOf, dOf_piK h h1, map_smul, map_sub, Finset.smul_sum, ← Finset.sum_sub_distrib]

open Classical in

theorem coord_hol [IsTotallyComplex E] (τ τ' : E →+* ℂ) :
    (1 / 2 : ℂ) * (coord τ' (atEmb τ 1) - Complex.I * coord τ' (atEmb τ Complex.I)) = if τ' = τ then 1 else 0 := by
  split_ifs with h
  · subst h
    rw [coord_atEmb, coord_atEmb, Complex.I_mul_I]; norm_num
  · by_cases hw : InfinitePlace.mk τ' = InfinitePlace.mk τ
    · obtain rfl : ComplexEmbedding.conjugate τ' = τ := (InfinitePlace.mk_eq_iff.1 hw).resolve_left h
      simp [atEmb_conj, coord_atEmb]
    · have h0 : ∀ z, coord τ' (atEmb τ z) = 0 := fun z => by
        have := congrArg (coord τ') (atEmb_mul_of_ne hw 1 z)
        rwa [map_mul, coord_atEmb, one_mul, map_zero] at this
      simp [h0]

end UpperTheory.V.WeylC
