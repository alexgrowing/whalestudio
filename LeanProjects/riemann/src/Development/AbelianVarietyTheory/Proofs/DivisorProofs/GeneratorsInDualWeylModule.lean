import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare.LiftGen

open GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators

theorem telescope {n : ℕ} (f : Fin (n + 1) → ℤ) (t : Fin (n + 1)) :
    ∑ i : Fin n, (if t.val < i.val + 1 then f i.castSucc - f i.succ else 0) = f t - f (Fin.last n) := by
  induction n with
  | zero => simp [Fin.eq_zero t, Fin.last]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    induction t using Fin.lastCases with
    | last =>
      rw [Finset.sum_eq_zero, if_neg (by simp)]
      · simp
      · intro i _
        rw [if_neg]
        have := i.isLt
        simp only [Fin.val_last, Fin.val_castSucc]
        omega
    | cast t =>
      have h := ih (fun j => f j.castSucc) t
      have ht := t.isLt
      simp only [Fin.val_castSucc, Fin.succ_castSucc, Fin.val_last, Fin.succ_last] at h ⊢
      rw [h, if_pos (by omega)]
      simp

variable {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n}

theorem aNum_cast (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (i : Fin n) :
    (aNum lam sg i : ℤ) = sg.w i - lam.w i.succ :=
  Int.toNat_of_nonneg (sub_nonneg.2 (h i).1)

theorem bNum_cast (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (i : Fin n) :
    (bNum lam sg i : ℤ) = lam.w i.castSucc - sg.w i :=
  Int.toNat_of_nonneg (sub_nonneg.2 (h i).2)

theorem sum_ab (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (t : Fin n) :
    ((∑ i : Fin n, (aNum lam sg i * initW n (i.val + 1) t) + ∑ i : Fin n, (bNum lam sg i * initW n (i.val + 1) t) : ℕ) : ℤ)
      = lam.w t.castSucc - lam.w (Fin.last n) := by
  rw [← telescope lam.w t.castSucc, ← Finset.sum_add_distrib, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have ha := aNum_cast h i
  have hb := bNum_cast h i
  simp only [initW, Fin.val_castSucc]
  split_ifs
  · push_cast; linarith
  · simp

theorem sum_b_succ (b : Fin n → ℕ) (t : Fin n) :
    ∑ i : Fin n, b i * initW n (i.val + 1) t = ∑ i : Fin n, b i * initW n i.val t + b t := by
  have : b t = ∑ i : Fin n, if i = t then b i else 0 := by simp
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [initW, Fin.ext_iff]
  split_ifs <;> omega

theorem lamN_eq (t : Fin n) : lamN lam t = (lam.w t.castSucc - lam.w (Fin.last n)).toNat := by
  simp only [lamN, DomWeight.natW, DomWeight.detShift, Nat.succ_pos, dif_pos]
  rfl

theorem natW_eq (he : EqualLast lam sg) (t : Fin n) : sg.natW t = (sg.w t - lam.w (Fin.last n)).toNat := by
  have hn : 0 < n := t.pos
  simp only [DomWeight.natW, DomWeight.detShift, dif_pos hn]
  rw [he ⟨n - 1, by omega⟩ (by simp only; omega)]

theorem shape_lam (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) :
    (∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), initW n (i.val + 1)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), initW n (i.val + 1)) = lamN lam := by
  funext t
  have := sum_ab h t
  rw [lamN_eq, ← this, Int.toNat_natCast]
  simp [Finset.sum_apply]

theorem shape_sg (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (he : EqualLast lam sg) :
    (∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), initW n (i.val + 1)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), initW n i.val) = sg.natW := by
  funext t
  have h1 := sum_ab h t
  rw [sum_b_succ (bNum lam sg)] at h1
  have hb := bNum_cast h t
  rw [natW_eq he]
  simp only [Pi.add_apply, Finset.sum_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Pi.smul_apply]
  omega

theorem shape_b (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (he : EqualLast lam sg) :
    (∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), (0 : Fin n → ℕ)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), (Pi.single i 1 : Fin n → ℕ)) = fun s => lamN lam s - sg.natW s := by
  funext t
  have h1 := sum_ab h t
  rw [sum_b_succ (bNum lam sg)] at h1
  have hb := bNum_cast h t
  have h2 : ((∑ i : Fin n, ∑ _k : Fin (aNum lam sg i), (0 : Fin n → ℕ)) +
      (∑ i : Fin n, ∑ _k : Fin (bNum lam sg i), (Pi.single i 1 : Fin n → ℕ))) t = bNum lam sg t := by
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h2, natW_eq he, lamN_eq]
  omega

theorem prod_mem (K : Type) [Field K] {r n : ℕ} {ι : Type} (S : Finset ι) (w : ι → Fin n → ℕ)
    (g : ι → MvPolynomial (Fin r × Fin n) K) (hg : ∀ k, g k ∈ dualWeyl K r n (w k)) :
    ∏ k ∈ S, g k ∈ dualWeyl K r n (∑ k ∈ S, w k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (dualWeylMul K r n 0 0 0 0).2
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (dualWeylMul K r n _ _ _ _).1 (hg a) ih

theorem incl_initMinor (K : Type) [Field K] {s : ℕ} (I : Fin s → Fin (n + 1)) (hs : s ≤ n) (hs' : s ≤ n + 1) :
    incl K n (initMinor K I hs) = initMinor K I hs' := by
  unfold initMinor
  rw [algHom_det_of]
  simp only [incl, rename_X]
  rfl

theorem piGen_mem_and_lift (K : Type) [Field K] (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg) (he : EqualLast lam sg) (t : Gen lam sg) :
    piGen K lam sg t ∈ dualWeyl K n n sg.natW ∧
      ∃ G : BP K n, bmLift K n (lamN lam) (fun s => lamN lam s - sg.natW s) (piGen K lam sg t) G ∧
        phiGen K lam sg t = incl K n G := by
  refine ⟨?_, ?_⟩
  · rw [← shape_sg h he]
    exact (dualWeylMul K n n _ _ _ _).1
      (prod_mem K _ _ _ fun i => prod_mem K _ _ _ fun k => initMinor_mem _ _)
      (prod_mem K _ _ _ fun i => prod_mem K _ _ _ fun k => initMinor_mem _ _)
  · have h0 := bmG_prod (Finset.univ : Finset (Fin n)) _ _ _ _ fun i _ =>
      bmG_prod (Finset.univ : Finset (Fin (aNum lam sg i))) _ _ _ _ fun k _ =>
        bmLift_minor0 K n (t.1 i k) (Nat.succ_le_of_lt i.isLt)
    have h1 := bmG_prod (Finset.univ : Finset (Fin n)) _ _ _ _ fun i _ =>
      bmG_prod (Finset.univ : Finset (Fin (bNum lam sg i))) _ _ _ _ fun k _ =>
        bmLift_minor1 K n (t.2 i k) (Nat.succ_le_of_lt i.isLt)
    refine ⟨_, bmG_cast (bmLift_mul h0 h1) (shape_lam h) (shape_b h he) rfl rfl, ?_⟩
    unfold phiGen
    simp only [map_mul, map_prod]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
      exact (incl_initMinor K _ _ _).symm
    · refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
      rw [incl_initMinor K _ _ (Nat.succ_le_succ i.isLt.le)]
      refine congrArg (fun I => initMinor K I (Nat.succ_le_succ i.isLt.le)) ?_
      funext p
      induction p using Fin.lastCases with
      | last => simp
      | cast p => simp

end GlobalTheory.BrCompare.LiftGen
