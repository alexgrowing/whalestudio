import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestRoom
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymbolFormOfOrthogonality
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockMonomial
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFTrueDeg

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section TDs

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

theorem TD_wLetBL {Cde E : ℝ} (x : X.TT × Bool) (b : SegBlock (segS X.TT j) X.m)
    (hk : BLk C0 Cde CE1 CE2 X E j b) :
    TD C0 CE1 CE2 X j b (wLet X x) =
      (if segNext X.TT j = x.1.val then hhDegs X.TT X.aT X.bT x else 0) +
        ∑ i, (if segPos X.TT j i = x.1.val then hhDegs X.TT X.aT X.bT x else 0) := by
  have ho : b.oPlus ≤ segAPlus X.TT X.aT j := hk.2.2.2.1
  obtain ⟨t, bb⟩ := x
  have hterm : ∀ i : Fin (segS X.TT j),
      ((∑ c : Fin (X.m + 1), (b.rz i c * wLet X (t, bb) ((topOdd X j i, true), c) +
          b.ry i c * wLet X (t, bb) ((topOdd X j i, false), c))) +
     (X.seg C0 CE1 CE2 j).P X.p i *
      (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i) * wLet X (t, bb) ((topOdd X j i, true), 0) +
          b.sg i * wLet X (t, bb) ((topOdd X j i, false), 0) + b.w i * wLet X (t, bb) ((topOdd X j i, true), Fin.succ 0) +
          (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i) *
            wLet X (t, bb) ((topOdd X j i, false), Fin.succ 0)
       else
        (coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i) * wLet X (t, bb) ((topOdd X j i, true), 0) +
          b.o i * wLet X (t, bb) ((topOdd X j i, true), Fin.succ 0) +
          coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i *
            wLet X (t, bb) ((topOdd X j i, false), Fin.succ 0))) =
      (if segPos X.TT j i = t.val then hhDegs X.TT X.aT X.bT (t, bb) else 0) := by
    intro i
    have hodd := (pos_mem X.TT j i).2
    by_cases h : segPos X.TT j i = t.val
    · have ht : topOdd X j i = t := Subtype.ext h
      subst ht
      rw [if_pos h]
      cases bb
      · have w1 : ∀ c, wLet X (topOdd X j i, false) ((topOdd X j i, true), c) = 0 := fun c => if_neg (by simp)
        have w2 : ∀ c, wLet X (topOdd X j i, false) ((topOdd X j i, false), c) = 1 := fun c => if_pos rfl
        simp only [w1, w2, mul_zero, mul_one, zero_add, add_zero]
        have hd := hk.1.2.2 i
        have hPC : (X.seg C0 CE1 CE2 j).P X.p i * coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i =
            segATop X.TT X.aT j i - ∑ c, b.ry i c := Nat.mul_div_cancel' hd.2
        have hdeg : hhDegs X.TT X.aT X.bT (topOdd X j i, false) = segATop X.TT X.aT j i := by
          show hhDeg X.aT X.bT (segPos X.TT j i) false = X.aT (segPos X.TT j i)
          unfold hhDeg
          simp [hodd]
        have hin : (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
            b.sg i + (coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i - b.sg i)
            else coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i) =
            coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i := by
          split_ifs with hs
          · have := (hk.2.2.1 i hs).2.2.1
            omega
          · rfl
        rw [hin, hPC, hdeg]
        have := hd.1
        omega
      · have w1 : ∀ c, wLet X (topOdd X j i, true) ((topOdd X j i, true), c) = 1 := fun c => if_pos rfl
        have w2 : ∀ c, wLet X (topOdd X j i, true) ((topOdd X j i, false), c) = 0 := fun c => if_neg (by simp)
        simp only [w1, w2, mul_zero, mul_one, zero_add, add_zero]
        have hd := hk.1.2.1 i
        have hPA : (X.seg C0 CE1 CE2 j).P X.p i * coarseA X.p (X.seg C0 CE1 CE2 j) b i =
            (X.seg C0 CE1 CE2 j).bTop i - ∑ c, b.rz i c := Nat.mul_div_cancel' hd.2
        have hdeg : hhDegs X.TT X.aT X.bT (topOdd X j i, true) = (X.seg C0 CE1 CE2 j).bTop i := by
          show hhDeg X.aT X.bT (segPos X.TT j i) true = X.bT (segPos X.TT j i)
          unfold hhDeg
          simp [hodd]
        have hin : (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then
            coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.w i + b.w i
            else coarseA X.p (X.seg C0 CE1 CE2 j) b i - b.o i + b.o i) = coarseA X.p (X.seg C0 CE1 CE2 j) b i := by
          split_ifs with hs
          · have := (hk.2.2.1 i hs).2.1
            omega
          · have := (hk.2.1 i (not_lt.1 hs)).1
            omega
        rw [hin, hPA, hdeg]
        have := hd.1
        omega
    · have w0 : ∀ b' c, wLet X (t, bb) ((topOdd X j i, b'), c) = 0 := fun b' c =>
        if_neg (fun e => h (congrArg (fun z : X.TT × Bool => z.1.val) e))
      rw [if_neg h]
      simp only [w0, mul_zero, add_zero, Finset.sum_const_zero, ite_self]
  have hend : (segAPlus X.TT X.aT j - b.oPlus) * wLet X (t, bb) ((topEnd X j, true), 0) +
      b.oPlus * wLet X (t, bb) ((topEnd X j, true), Fin.succ 0) +
      (X.seg C0 CE1 CE2 j).bPlus * wLet X (t, bb) ((topEnd X j, false), Fin.succ 0) =
      (if segNext X.TT j = t.val then hhDegs X.TT X.aT X.bT (t, bb) else 0) := by
    have hev := (next_mem X.TT j).2
    by_cases h : segNext X.TT j = t.val
    · have ht : topEnd X j = t := Subtype.ext h
      subst ht
      rw [if_pos h]
      cases bb
      · have w1 : ∀ c, wLet X (topEnd X j, false) ((topEnd X j, true), c) = 0 := fun c => if_neg (by simp)
        have w2 : ∀ c, wLet X (topEnd X j, false) ((topEnd X j, false), c) = 1 := fun c => if_pos rfl
        simp only [w1, w2, mul_zero, mul_one, zero_add]
        show X.bT (segNext X.TT j) = hhDeg X.aT X.bT (segNext X.TT j) false
        unfold hhDeg
        simp [hev]
      · have w1 : ∀ c, wLet X (topEnd X j, true) ((topEnd X j, true), c) = 1 := fun c => if_pos rfl
        have w2 : ∀ c, wLet X (topEnd X j, true) ((topEnd X j, false), c) = 0 := fun c => if_neg (by simp)
        simp only [w1, w2, mul_zero, mul_one, add_zero]
        rw [Nat.sub_add_cancel ho]
        show X.aT (segNext X.TT j) = hhDeg X.aT X.bT (segNext X.TT j) true
        unfold hhDeg
        simp [hev]
    · have w0 : ∀ b' c, wLet X (t, bb) ((topEnd X j, b'), c) = 0 := fun b' c =>
        if_neg (fun e => h (congrArg (fun z : X.TT × Bool => z.1.val) e))
      rw [if_neg h]
      simp only [w0, mul_zero, add_zero]
  unfold TD
  rw [Finset.sum_congr rfl fun i _ => hterm i, add_assoc, add_assoc, ← add_assoc ((segAPlus X.TT X.aT j - b.oPlus) * _),
    hend, add_comm]

theorem TD_wN (b : SegBlock (segS X.TT j) X.m) :
    TD C0 CE1 CE2 X j b (wN X) = blockOrd X.p (X.seg C0 CE1 CE2 j) b := by
  unfold TD blockOrd oEff
  simp only [normal_weight_vector_zero_eq_zero, wN_vecS, normal_weight_covector_zero, wN_covS, mul_zero, mul_one, zero_add, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : ∑ c : Fin (X.m + 1), (b.rz i c * wN X ((topOdd X j i, true), c) + b.ry i c * wN X ((topOdd X j i, false), c)) =
      (∑ c : Fin (X.m + 1), if (c : ℕ) = 0 then 0 else b.rz i c) + b.ry i 0 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [normal_weight_vector_zero_eq_zero, wN_vecS, normal_weight_covector_zero, wN_covS, mul_zero, mul_one, zero_add, add_zero, Fin.val_zero, if_true,
      Fin.val_succ, Nat.succ_ne_zero, if_false]
    ring
  rw [h1]
  split_ifs <;> ring

end TDs

section Sym

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] {O : Type} [CommRing O] [IsDomain O]

def BalHom (O : Type) [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (X : Loc) (β : GlobalTheory X) (s : Syms O C0 CE1 CE2 X) : Prop :=
  ∀ j (ω' : BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t → ℕ) (ωL : Fin (2 * segS X.TT j + 1 + 1) → ℕ),
      Balanced X.m (X.seg C0 CE1 CE2 j) ω' ωL → IsWeightedHomogeneous ω' (s j)
        (OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (β j) ω' ωL)

theorem symPolBL (h2 : 2 ≤ numSeg X.TT) {E : ℝ} (β : GlobalTheory X) (hβ : ∀ j, BLk C0 Cde CE1 CE2 X E j (β j))
    (s : Syms O C0 CE1 CE2 X) (hs : BalHom O C0 CE1 CE2 X β s) :
    symFam (KK O) X.p C0 CE1 CE2 X β s ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT) := by
  classical
  unfold Pol
  rw [mem_restrictSupport_iff]
  intro μ hμ x
  have hwh : IsWeightedHomogeneous (wLet X x) (symFam (KK O) X.p C0 CE1 CE2 X β s)
      (∑ j, TD C0 CE1 CE2 X j (β j) (wLet X x)) :=
    IsWeightedHomogeneous.prod _ _ _ (fun j _ => ioBlock_wh' C0 CE1 CE2 X j O 0 (β j) (wLet X x) (fun _ _ _ => rfl)
      (fun _ => rfl) rfl (s j) (hs j))
  have h1 := hwh (mem_support_iff.1 (Finset.mem_coe.1 hμ))
  rw [weight_wLet] at h1
  rw [h1, Finset.sum_congr rfl fun j _ => TD_wLetBL C0 CE1 CE2 X j x (β j) (hβ j),
    ← natPartSum X.TT h2 (fun s => if s = x.1.val then hhDegs X.TT X.aT X.bT x else 0), Finset.sum_ite_eq',
    if_pos x.1.2]

theorem symNdBL (β : GlobalTheory X) (s : Syms O C0 CE1 CE2 X) (hs : BalHom O C0 CE1 CE2 X β s) :
    IsWeightedHomogeneous (wN X) (symFam (KK O) X.p C0 CE1 CE2 X β s) (ordFam C0 CE1 CE2 X β) := by
  have hwh : IsWeightedHomogeneous (wN X) (symFam (KK O) X.p C0 CE1 CE2 X β s)
      (∑ j, TD C0 CE1 CE2 X j (β j) (wN X)) :=
    IsWeightedHomogeneous.prod _ _ _ (fun j _ => ioBlock_wh' C0 CE1 CE2 X j O 0 (β j) (wN X)
      (fun x c c' => by
        rcases x with ⟨t, bb⟩
        cases bb
        · rw [wN_covS, wN_covS]
        · rw [wN_vecS, wN_vecS])
      (fun l => by rw [normal_weight_vector_zero_eq_zero, normal_weight_covector_zero, wN_vecS, wN_covS])
      (by rw [normal_weight_vector_zero_eq_zero, normal_weight_covector_zero, wN_vecS, wN_covS]) (s j) (hs j))
  have e : ∑ j, TD C0 CE1 CE2 X j (β j) (wN X) = ordFam C0 CE1 CE2 X β :=
    Finset.sum_congr rfl fun j _ => TD_wN C0 CE1 CE2 X j (β j)
  rwa [e] at hwh

theorem ioBlock_coeff (hp : 0 < X.p) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (u : MvPolynomial (BV C0 CE1 CE2 X j) (KK O)) (μ : BV C0 CE1 CE2 X j →₀ ℕ) :
    (ioBlock (KK O) X.p C0 CE1 CE2 X j b u).coeff (ioExp C0 CE1 CE2 X j b μ) = u.coeff μ := by
  classical
  induction u using MvPolynomial.induction_on' with
  | monomial ν c =>
    rw [ioBlock_monomial, coeff_monomial, coeff_monomial]
    by_cases h : ν = μ
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg fun e => h (ioExp_inj C0 CE1 CE2 X hp j b e)]
  | add p q hp' hq' => rw [ioBlock_add, coeff_add, coeff_add, hp', hq']

theorem ioBlock_ne_zero (hp : 0 < X.p) (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    {u : MvPolynomial (BV C0 CE1 CE2 X j) (KK O)} (hu : u ≠ 0) : ioBlock (KK O) X.p C0 CE1 CE2 X j b u ≠ 0 := by
  intro h
  apply hu
  ext μ
  rw [← ioBlock_coeff hp j b u μ, h, coeff_zero, coeff_zero]

theorem ioD_ne_zero (hp : 0 < X.p) {mu : ℝ} (β : GlobalTheory X) (j : Fin (numSeg X.TT))
    {u : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (BDk C0 CE1 CE2 mu X β j).T.t) (KK O)} (hu : u ≠ 0) :
    ioD O C0 CE1 CE2 mu X β j u ≠ 0 := by
  intro h
  refine ioBlock_ne_zero (C0 := C0) (CE1 := CE1) (CE2 := CE2) hp j (β j) (u := u) hu ?_
  show digitMon (KK O) C0 CE1 CE2 X j (β j) * sTopMon (KK O) X.p C0 CE1 CE2 X j (β j) * ioD O C0 CE1 CE2 mu X β j u = 0
  rw [h, mul_zero]

end Sym

end Formalism.MainNotions.ColumnSystems.Pf
