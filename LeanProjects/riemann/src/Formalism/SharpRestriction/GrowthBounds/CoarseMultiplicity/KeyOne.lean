import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestRawTail1Of

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

theorem liftSubst_one_X {p f : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p f) O] (w : O) (r : ℕ)
    {ι : Type} {k : ℕ} (LL : LiftLetters ι) (v : ι × Fin k) :
    liftSubst p f O w r LL (1 : Matrix (Fin k) (Fin k) (WF p f)) (X v) =
      C (algebraMap O (KK O) (dW O w LL r v.1 v.2)) * X v := by
  unfold liftSubst
  rw [MvPolynomial.aeval_X, sigMat_one, inv_one]
  by_cases hv : LL.vec v.1 <;> simp [hv, Matrix.one_apply, dW] <;> split_ifs <;> simp_all

theorem liftSubst_one_hh {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (x : X.TT × Bool) (b : Fin (X.m + 1)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
        (MvPolynomial.X (x, b)) =
      (if (x.2 = true ∧ 1 ≤ (b : ℕ)) ∨ (x.2 = false ∧ (b : ℕ) < 1) then
        C (algebraMap O (KK O) w) * MvPolynomial.X (x, b) else MvPolynomial.X (x, b)) := by
  rw [liftSubst_one_X]
  have hd : dW O w (hhLetters X.TT) 1 x b =
      if (x.2 = true ∧ 1 ≤ (b : ℕ)) ∨ (x.2 = false ∧ (b : ℕ) < 1) then w else 1 := rfl
  rw [hd]
  split_ifs <;> simp

private theorem liftSubst_X_true_zero_eq_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, true), (0 : Fin (X.m + 1)))) = MvPolynomial.X ((y, true), 0) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_true_succ_eq_C_mul_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, true), c.succ)) =
        C (algebraMap O (KK O) w) * MvPolynomial.X ((y, true), c.succ) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_false_zero_eq_C_mul_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, false), (0 : Fin (X.m + 1)))) =
        C (algebraMap O (KK O) w) * MvPolynomial.X ((y, false), 0) := by
  rw [liftSubst_one_hh]
  simp

private theorem liftSubst_X_false_succ_eq_X {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [Algebra (WF X.p X.n') O] (w : O) (y : X.TT) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) (1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
      (MvPolynomial.X ((y, false), c.succ)) = MvPolynomial.X ((y, false), c.succ) := by
  rw [liftSubst_one_hh]
  simp

theorem key3One_S {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (kSkey O X j i) =
      w • (MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), 0) +
        w ^ (X.p ^ (segDists X.TT j).get i - 1) • (∑ c : Fin X.m,
          MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) *
            MvPolynomial.X ((topOdd X j i, false), c.succ) : RHH O X) : RHH O X) := by
  have hq1 : 1 ≤ X.p ^ (segDists X.TT j).get i := Nat.one_le_pow _ _ (Fact.out : X.p.Prime).pos
  unfold kSkey
  rw [map_sum, Fin.sum_univ_succ]
  simp only [map_mul, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X, liftSubst_X_false_zero_eq_C_mul_X, liftSubst_X_false_succ_eq_X]
  rw [Algebra.smul_def, Algebra.smul_def, MvPolynomial.algebraMap_apply,
    MvPolynomial.algebraMap_apply, map_pow, map_pow]
  obtain ⟨q', hq'⟩ : ∃ q', X.p ^ (segDists X.TT j).get i = q' + 1 :=
    ⟨_, (Nat.sub_add_cancel hq1).symm⟩
  rw [hq', Nat.add_sub_cancel]
  have hsum : ∑ c : Fin X.m, (C (algebraMap O (KK O) w) * MvPolynomial.X ((topStart X j, true), c.succ)) ^
      (q' + 1) * MvPolynomial.X ((topOdd X j i, false), c.succ) =
      C (algebraMap O (KK O) w) ^ (q' + 1) * ∑ c : Fin X.m,
        MvPolynomial.X ((topStart X j, true), c.succ) ^ (q' + 1) * MvPolynomial.X ((topOdd X j i, false), c.succ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsum]
  ring

theorem key_lift_identity_lower {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (kWkey O X j i c.succ) =
      w • (MvPolynomial.X ((topOdd X j i, true), c.succ) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
        w ^ (X.p ^ (segDists X.TT j).get i - 1) •
          (MvPolynomial.X ((topOdd X j i, true), 0) *
            MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) : RHH O X) : RHH O X) := by
  have hq1 : 1 ≤ X.p ^ (segDists X.TT j).get i := Nat.one_le_pow _ _ (Fact.out : X.p.Prime).pos
  unfold kWkey
  simp only [map_sub, map_mul, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X]
  rw [Algebra.smul_def, Algebra.smul_def, MvPolynomial.algebraMap_apply,
    MvPolynomial.algebraMap_apply, map_pow, map_pow]
  obtain ⟨q', hq'⟩ : ∃ q', X.p ^ (segDists X.TT j).get i = q' + 1 :=
    ⟨_, (Nat.sub_add_cancel hq1).symm⟩
  rw [hq', Nat.add_sub_cancel]
  ring

theorem loc4One {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
    (c : Fin X.m) :
    liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (locC O X c.succ) =
      ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1) -
        w ^ (∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1)) •
          (∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ segG X.TT j - 1) : RHH O X) := by
  unfold locC
  simp only [map_sub, map_prod, map_pow, liftSubst_X_true_zero_eq_X, liftSubst_X_true_succ_eq_C_mul_X]
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, map_pow, map_pow,
    ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun j _ => mul_pow _ _ _

def CoarseMultiplicityOrderBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X →
    ∀ (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)),
      ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
        InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kSkey O X j i) 1 ∧
        ∀ c : Fin X.m, InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (kWkey O X j i c.succ) 1

def LocalOrderBound : Prop :=
  ∀ (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O), S.SqP → D1num X → 2 ≤ numSeg X.TT →
    ∀ (j0 : Fin (numSeg X.TT)) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')), IsGLW g →
      ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1 →
      InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (locR O X j0) 1

theorem third_key_of_order (h : CoarseMultiplicityOrderBound) : CoarseMultiplicityBoundAtIdentity := by
  intro X _ O _ _ _ _ S hSq hD j i
  exact ⟨fun g hg => h X O S hSq hD j i g hg, key3One_S S.w j i, fun c => key_lift_identity_lower S.w j i c⟩

theorem local_fourth_of_order (h : LocalOrderBound) : LocalBoundAtIdentity := by
  intro X _ O _ _ _ _ S hSq hD hn
  exact ⟨fun j0 g hg hr => h X O S hSq hD hn j0 g hg hr, fun c => loc4One S.w c⟩

end Formalism.MainNotions.ColumnSystems.Pf
