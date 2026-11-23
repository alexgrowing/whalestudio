import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MultidegAdd
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PsiRes0Ne

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

abbrev VarH (X : Loc) := (X.TT × Bool) × Fin (X.m + 1)

def wN (X : Loc) : VarH X → ℕ := fun v =>
  if (v.1.2 = true ∧ 1 ≤ v.2.val) ∨ (v.1.2 = false ∧ v.2.val < 1) then 1 else 0

def dX {X : Loc} (x l : X.TT × Bool) : ℕ := if x = l then 1 else 0

def wL (X : Loc) (l : X.TT × Bool) : VarH X → ℕ := fun v => dX v.1 l

section Grad

variable {X : Loc}

theorem wN_pos {v : VarH X} (h : (v.1.2 = true ∧ 1 ≤ v.2.val) ∨ (v.1.2 = false ∧ v.2.val < 1)) : wN X v = 1 := if_pos h

theorem wN_neg {v : VarH X} (h : ¬ ((v.1.2 = true ∧ 1 ≤ v.2.val) ∨ (v.1.2 = false ∧ v.2.val < 1))) : wN X v = 0 := if_neg h

theorem ndM_eq (m : MonH X) : ndM X m = Finsupp.weight (wN X) m := by
  classical
  unfold ndM degUS
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : (v.1.2 = true ∧ 1 ≤ v.2.val) ∨ (v.1.2 = false ∧ v.2.val < 1)
  · have h' : ((hhLetters X.TT).vec v.1 = true ∧ 1 ≤ v.2.val) ∨ ((hhLetters X.TT).vec v.1 = false ∧ v.2.val < 1) := h
    rw [if_pos h', wN_pos h, smul_eq_mul, mul_one]
  · have h' : ¬ (((hhLetters X.TT).vec v.1 = true ∧ 1 ≤ v.2.val) ∨ ((hhLetters X.TT).vec v.1 = false ∧ v.2.val < 1)) := h
    rw [if_neg h', wN_neg h, smul_eq_mul, mul_zero]

theorem multideg_eq (m : MonH X) (l : X.TT × Bool) : multideg m l = Finsupp.weight (wL X l) m := by
  classical
  unfold multideg
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_prod_type,
    Finset.sum_eq_single l]
  · simp [wL, dX]
  · intro b _ hb
    simp [wL, dX, hb]
  · intro h; exact absurd (Finset.mem_univ l) h

variable {K : Type} [CommRing K]

theorem mem_Pol_iff {d : X.TT × Bool → ℕ} {P : MvPolynomial (VarH X) K} :
    P ∈ Pol K (ι := X.TT × Bool) (X.m + 1) d ↔ ∀ l, IsWeightedHomogeneous (wL X l) P (d l) := by
  unfold Pol
  rw [MvPolynomial.mem_restrictSupport_iff]
  constructor
  · intro h l m hm
    rw [← multideg_eq]
    exact h (Finset.mem_coe.2 (MvPolynomial.mem_support_iff.2 hm)) l
  · intro h m hm l
    rw [multideg_eq]
    exact h l (MvPolynomial.mem_support_iff.1 (Finset.mem_coe.1 hm))

theorem ndHom_iff {o : ℕ} {P : MvPolynomial (VarH X) K} :
    (∀ m ∈ P.support, ndM X m = o) ↔ IsWeightedHomogeneous (wN X) P o := by
  constructor
  · intro h m hm
    rw [← ndM_eq]
    exact h m (MvPolynomial.mem_support_iff.2 hm)
  · intro h m hm
    rw [ndM_eq]
    exact h (MvPolynomial.mem_support_iff.1 hm)

end Grad

section Int

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}

theorem X_int (v : σ) : (MvPolynomial.X v : MvPolynomial σ (KK O)) ∈ intSub O σ := X_mem_goodSub v rfl

end Int

section Lift

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O]

theorem identity_lift_X (w : O) (v : VarH X) :
    lift1 X O w (MvPolynomial.X v) = (w ^ wN X v) • (MvPolynomial.X v : RHH O X) := by
  obtain ⟨x, b⟩ := v
  show liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (MvPolynomial.X (x, b)) = _
  rw [liftSubst_one_hh]
  by_cases h : (x.2 = true ∧ 1 ≤ (b : ℕ)) ∨ (x.2 = false ∧ (b : ℕ) < 1)
  · rw [if_pos h, C_mul_eq_smul, wN_pos (v := (x, b)) h, pow_one]
  · rw [if_neg h, wN_neg (v := (x, b)) h, pow_zero, one_smul]

theorem identity_lift_monomial (w : O) (M : MonH X) :
    lift1 X O w (monomial M 1) = (w ^ ndM X M) • (monomial M 1 : RHH O X) := by
  classical
  induction M using Finsupp.induction_linear with
  | zero =>
    have : ndM X (0 : MonH X) = 0 := degUS_zero _ _
    rw [this]
    simp
  | add f g hf hg =>
    have e : (monomial (f + g) 1 : RHH O X) = monomial f 1 * monomial g 1 := by
      rw [monomial_mul, one_mul]
    rw [e, map_mul, hf, hg, ndM_add, pow_add, smul_mul_smul_comm]
  | single a b =>
    have e : (monomial (Finsupp.single a b) 1 : RHH O X) = MvPolynomial.X a ^ b := (X_pow_eq_monomial).symm
    have hn : ndM X (Finsupp.single a b) = b * wN X a := by
      rw [ndM_eq, Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]
      simp
    rw [e, map_pow, identity_lift_X, smul_pow, hn, ← pow_mul, mul_comm]

theorem identity_lift_eq_sum (w : O) (P : RHH O X) :
    lift1 X O w P = ∑ m ∈ P.support, monomial m (algebraMap O (KK O) (w ^ ndM X m) * P.coeff m) := by
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff P]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : (monomial m (P.coeff m) : RHH O X) = C (P.coeff m) * monomial m 1 := by
    rw [C_mul_monomial, mul_one]
  rw [e, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, identity_lift_monomial, ← C_mul_eq_smul, C_mul_monomial,
    C_mul_monomial, mul_one, mul_comm]

theorem identity_lift_weighted_homog (w : O) {wt : VarH X → ℕ} {n : ℕ} {P : RHH O X} (h : IsWeightedHomogeneous wt P n) :
    IsWeightedHomogeneous wt (lift1 X O w P) n := by
  rw [identity_lift_eq_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  exact isWeightedHomogeneous_monomial wt m _ (h (MvPolynomial.mem_support_iff.1 hm))

theorem identity_lift_mem_Pol (w : O) {d : X.TT × Bool → ℕ} {P : RHH O X}
    (h : P ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) d) :
    lift1 X O w P ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) d :=
  mem_Pol_iff.2 fun l => identity_lift_weighted_homog w (mem_Pol_iff.1 h l)

theorem identity_lift_normal_homog (w : O) {o : ℕ} {P : RHH O X} (h : IsWeightedHomogeneous (wN X) P o) :
    lift1 X O w P = (w ^ o) • P := by
  rw [identity_lift_eq_sum]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff P]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [ndM_eq, h (MvPolynomial.mem_support_iff.1 hm), ← C_mul_eq_smul, C_mul_monomial]

end Lift

section FacCalc

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

theorem inWjRg_zero_of_inA (w : O) {f : RHH O X} (hf : InA f)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) :
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g f 0 := by
  intro m
  obtain ⟨a, ha⟩ := lift_substitution_coeff_divisible X.p X.n' O w (hhLetters X.TT) 1 g hg f hf m
  exact ⟨w ^ degUS (hhLetters X.TT) 1 m * a, by rw [ha, pow_zero, one_mul]⟩

theorem IsFac.one (w : O) : IsFac (X := X) w (1 : RHH O X) 0 1 where
  inA := (inA_iff_wj w).2 (inWj_one w)
  ord := fun g _ => by
    unfold InWjRg
    rw [map_one]
    exact inWj_one w
  sym := by
    rw [map_one, pow_zero, one_smul, sub_self]
    exact (wjSub w _).zero_mem
  sgInt := (inA_iff_wj w).2 (inWj_one w)

theorem IsFac.pow {w : O} {f sg : RHH O X} {o : ℕ} (h : IsFac w f o sg) (u : ℕ) : IsFac w (f ^ u) (u * o) (sg ^ u) := by
  induction u with
  | zero => simpa using IsFac.one (X := X) w
  | succ u ih =>
    have := ih.mul h
    rw [pow_succ, pow_succ]
    have e : u * o + o = (u + 1) * o := by ring
    rwa [e] at this

theorem IsFac.congr_sg {w : O} {f sg sg' : RHH O X} {o : ℕ} (h : IsFac w f o sg) (h' : InWj w (sg - sg') 1)
    (hi : InA sg') : IsFac w f o sg' where
  inA := h.inA
  ord := h.ord
  sym := by
    have e : liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f - (w ^ o) • sg' =
        (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f - (w ^ o) • sg) + (w ^ o) • (sg - sg') := by
      rw [smul_sub]; abel
    rw [e]
    have := wj_smul_pow h' o
    rw [add_comm 1 o] at this
    exact (wjSub w (o + 1)).add_mem h.sym this
  sgInt := hi

theorem IsFac.of_exact {w : O} {f sg r : RHH O X} {o e : ℕ} (hA : InA f)
    (hord : ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
      InWjRg X.p X.n' O w 1 (hhLetters X.TT) g f o)
    (he : 1 ≤ e) (hs : InA sg) (hr : InA r)
    (hl : liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f = (w ^ o) • (sg + (w ^ e) • r)) : IsFac w f o sg where
  inA := hA
  ord := hord
  sym := by
    rw [hl, smul_add, add_sub_cancel_left, smul_smul, ← pow_add]
    have := wj_smul_pow ((inA_iff_wj w).1 hr) (o + e)
    rw [zero_add] at this
    exact wj_mono (by omega) this
  sgInt := hs

end FacCalc

structure SoftOK {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (w : O) (f : RHH O X) (od : ℕ) (sg : RHH O X) (dg : X.TT × Bool → ℕ) : Prop where
  fac : IsFac w f od sg
  sgHom : ∀ m ∈ sg.support, ndM X m = od
  liftPol : lift1 X O w f ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) dg
  sgPol : sg ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) dg

end Formalism.MainNotions.ColumnSystems.Pf
