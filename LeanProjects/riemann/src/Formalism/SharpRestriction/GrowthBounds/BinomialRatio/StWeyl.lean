import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountDefs
import Formalism.SharpRestriction.GrowthBounds.JointsLit

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem wdim_shift {r : ℕ} (lam : Fin r → ℤ) (c : ℤ) : wdim (fun i => lam i + c) = wdim lam := by
  unfold wdim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  split_ifs
  · congr 1
    push_cast
    ring
  · rfl

theorem wdim_nat {r : ℕ} (nu : Fin r → ℕ) :
    wdim (fun i => (nu i : ℤ)) = ∏ i : Fin r, ∏ j : Fin r,
      if i < j then ((nu i : ℚ) - (nu j : ℚ) + (j : ℚ) - (i : ℚ)) / ((j : ℚ) - (i : ℚ)) else 1 := by
  unfold wdim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Int.cast_natCast]

theorem antitone_of_interlace {r : ℕ} {lamN : Fin (r + 1) → ℕ} (hl : Antitone lamN) (nu : Fin r → ℕ)
    (h : ∀ i : Fin r, lamN i.succ ≤ nu i ∧ nu i ≤ lamN i.castSucc) : Antitone nu := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have h1 : i.succ ≤ j.castSucc := by
      rw [Fin.le_def]
      have : (i : ℕ) < (j : ℕ) := hlt
      simpa using this
    exact ((h j).2.trans (hl h1)).trans (h i).1

theorem numBranch_of {D : Formalism.BasicNotions.D7} (h2 : adm2 D) (h3 : adm3 D) : NumBranchAt := by
  intro r mu hmu
  classical
  set c : ℤ := mu (Fin.last r) with hc
  let lamN : Fin (r + 1) → ℕ := fun i => (mu i - c).toNat
  have hge : ∀ i, c ≤ mu i := fun i => hmu (Fin.le_last i)
  have hcast : ∀ i, (lamN i : ℤ) = mu i - c := fun i => Int.toNat_of_nonneg (by linarith [hge i])
  have hanti : Antitone lamN := by
    intro i j hij
    have h1 := hmu hij
    have : (lamN j : ℤ) ≤ (lamN i : ℤ) := by rw [hcast, hcast]; linarith
    exact_mod_cast this
  have e1 : wdim mu = (Module.finrank ℚ (Formalism.GradedWeylDivisibility.dualWeyl ℚ (r + 1) (r + 1) lamN) : ℚ) := by
    have hmu' : mu = fun i => (lamN i : ℤ) + c := funext fun i => by rw [hcast]; ring
    calc wdim mu = wdim (fun i => (lamN i : ℤ) + c) := congrArg wdim hmu'
      _ = wdim (fun i => (lamN i : ℤ)) := wdim_shift _ c
      _ = _ := by rw [wdim_nat, h3 ℚ (r + 1) lamN hanti]
  rw [e1, h2 ℚ r lamN hanti]
  push_cast
  set F := (Fintype.piFinset (fun _ : Fin r => Finset.range (lamN 0 + 1))).filter
    (fun nu => ∀ i : Fin r, lamN i.succ ≤ nu i ∧ nu i ≤ lamN i.castSucc) with hF
  have hinj : Set.InjOn (fun (nu : Fin r → ℕ) (i : Fin r) => (nu i : ℤ) + c) F := by
    intro a _ b _ hab
    funext i
    have := congrFun hab i
    simp only at this
    omega
  rw [finsum_eq_sum_of_support_subset (s := F.image (fun (nu : Fin r → ℕ) (i : Fin r) => (nu i : ℤ) + c))]
  · rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [hF, Finset.mem_filter] at hnu
    have hnu2 := hnu.2
    have hA : Antitone nu := antitone_of_interlace hanti nu hnu2
    rw [if_pos, wdim_shift, wdim_nat, h3 ℚ r nu hA]
    intro i
    show mu i.succ ≤ (nu i : ℤ) + c ∧ (nu i : ℤ) + c ≤ mu i.castSucc
    have h1 := hnu2 i
    have a1 := hcast i.succ
    have a2 := hcast i.castSucc
    constructor <;> omega
  · intro lam hlam
    rw [Function.mem_support] at hlam
    have hcond : ∀ i : Fin r, mu i.succ ≤ lam i ∧ lam i ≤ mu i.castSucc := by
      by_contra hn
      exact hlam (if_neg hn)
    rw [Finset.coe_image]
    refine ⟨fun i => (lam i - c).toNat, ?_, ?_⟩
    · rw [Finset.mem_coe, hF, Finset.mem_filter, Fintype.mem_piFinset]
      have hl : ∀ i, ((lam i - c).toNat : ℤ) = lam i - c := fun i =>
        Int.toNat_of_nonneg (by linarith [hge i.succ, (hcond i).1])
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rw [Finset.mem_range]
        show (lam i - c).toNat < lamN 0 + 1
        have a0 := hcast 0
        have h0 : mu i.castSucc ≤ mu 0 := hmu (Fin.zero_le _)
        have := hl i
        have := (hcond i).2
        omega
      · show lamN i.succ ≤ (lam i - c).toNat ∧ (lam i - c).toNat ≤ lamN i.castSucc
        have a1 := hcast i.succ
        have a2 := hcast i.castSucc
        have b1 := hl i
        have b2 := hcond i
        constructor <;> omega
    · funext i
      have : ((lam i - c).toNat : ℤ) = lam i - c :=
        Int.toNat_of_nonneg (by linarith [hge i.succ, (hcond i).1])
      simp only [this]
      ring

theorem stWeylAt (D : Formalism.BasicNotions.D7) : StWeylAt := by
  intro n N LL B P
  have h := Formalism.MainNotions.G.Joints.Lit.weyl_dimension_formula_index_sets D n N P.mu (P.dom (Fin.last N))
  rw [h]
  rfl

end Formalism.MainNotions.ColumnSystems.Pf
