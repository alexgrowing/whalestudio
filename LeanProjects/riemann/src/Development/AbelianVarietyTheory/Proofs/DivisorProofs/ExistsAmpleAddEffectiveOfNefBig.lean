import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasNonzeroSecPowOfAmpleSubAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivOfGlobalSectionPowNumEquivMultiple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectivePointFlagHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfIsNef
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.KodairaNefBig

theorem isAffine_of_dim_zero {X : Scheme.{0}} [IsIntegral X] (h : topologicalKrullDim X = 0) :
    IsAffine X := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hmem, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have hU' : U = ⊤ := eq_top_iff.2 fun x _ => by
    rw [GlobalTheory.FlagQ.eq_genericPoint_of_krullDim_zero h x]; exact hmem
  subst hU'
  haveI : IsAffine (⊤ : X.Opens) := hU
  exact IsAffine.of_isIso X.topIso.inv

theorem prod_le {d : ℕ} (q : ℤ) (hq : 1 ≤ q) (n : Fin (d + 1) → Fin 2 → ℤ)
    (h0 : ∀ j, 0 ≤ n 0 j ∧ n 0 j ≤ 2) (hs : ∀ (i : Fin d) j, 0 ≤ n i.succ j ∧ n i.succ j ≤ q)
    (a : Fin (d + 1) → Fin 2) : ∏ i, n i (a i) ≤ 2 * q ^ d := by
  rw [Fin.prod_univ_succ]
  have hp : ∏ i : Fin d, n i.succ (a i.succ) ≤ ∏ _i : Fin d, q :=
    Finset.prod_le_prod (fun i _ => (hs i _).1) fun i _ => (hs i _).2
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hp
  exact mul_le_mul (h0 _).2 hp (Finset.prod_nonneg fun i _ => (hs i _).1) (by norm_num)

end GlobalTheory.KodairaNefBig

open GlobalTheory.KodairaNefBig in

theorem GlobalTheory.exists_ample_add_eff_of_isNef_isBig : GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N : LB X) (hN : N.IsLB), IsNef ℂ N → IsBig ℂ N → ∃ (a : ℕ) (A : LB X) (hA : A.IsLB) (E₀ : CartierDiv X), 0 < a ∧ IsAmpleLB A ∧ E₀.Eff ∧ a • cls N hN = cls A hA + cls (toLB E₀) (isLB_toLB E₀) := by
  intro hNN X _ _ p hp N hN hnef hbig
  letI := algebraΓOfHom p
  have hp' : IsProjOver (strHom ℂ X) := by rwa [strHom_eq (f := p) fun _ => rfl]
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨D, hD, -⟩ := hbig.growth
  cases D with
  | zero =>
    have := isAffine_of_dim_zero (X := X) (by simpa using hD)
    refine ⟨1, N, hN, 0, one_pos, isAmpleLB_of_isAffine hN, CartierDiv.eff_zero, ?_⟩
    rw [one_smul, ← toPic_apply, map_zero, add_zero]
  | succ d =>
    have := isNoetherian_of_isProjOver hp
    have hV := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom ℂ X) (GlobalTheory.structureModule X)
      hp' (d := d + 1) (by rw [QCoh.suppDim_structureModule]; exact hD.le)
    let P : Fin 2 → LB X := ![N, A]
    have hPn : ∀ j, IsNef ℂ (P j) := fun j => by
      fin_cases j
      exacts [hnef, hA.isNef]
    have hP : ∀ j, (P j).IsLB := fun j => (hPn j).isLB
    have hI : ∀ a : Fin (d + 1) → Fin 2, 0 ≤ interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) :=
      fun a => hNN.1.interNum_nonneg hp' hD fun i => hPn (a i)
    set S : ℤ := ∑ a : Fin (d + 1) → Fin 2, interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) with hSdef
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun a _ => hI a
    have hT : 0 < topSelfIntersection ℂ N (d + 1) := (hNN.2.2.isBig_iff hp' hD hnef).1 hbig
    set q : ℕ := 2 * (d + 1) * S.toNat + 1 with hqdef
    have hqS : (q : ℤ) = 2 * (d + 1) * S + 1 := by
      rw [hqdef]; push_cast [Int.toNat_of_nonneg hS0]; ring
    have hq1 : (1 : ℤ) ≤ q := by rw [hqS]; nlinarith
    let L : LB X := tens A (lbPow N q)
    have hL : IsAmpleLB L := IsAmpleLB.tens_of_isNef hNN ℂ X p hp A _ hA (hnef.pow hA q)
    let B : LB X := lbPow A 2
    have hB : IsAmpleLB B := (isAmpleLB_pow_iff hA.isLB (by norm_num)).2 hA
    let M : LB X := tens (lbPow N q) (dual A)
    have hM : M.IsLB := isLB_tens (isLB_lbPow hN q) (isLB_dual hA.isLB)
    have hclsL : cls L hL.isLB = (q : ℤ) • cls N hN + cls A hA.isLB := by
      rw [cls_tens hA.isLB (isLB_lbPow hN q), cls_lbPow hN, natCast_zsmul, add_comm]
    have hclsB : cls B hB.isLB = (2 : ℤ) • cls A hA.isLB := by
      rw [cls_lbPow hA.isLB]; norm_cast
    have hclsM : cls M hM = (q : ℤ) • cls N hN - cls A hA.isLB := by
      rw [cls_tens (isLB_lbPow hN q) (isLB_dual hA.isLB), cls_lbPow hN, cls_dual hA.isLB,
        natCast_zsmul, sub_eq_add_neg]
    have e : cls L hL.isLB = cls M hM + cls B hB.isLB := by
      rw [hclsL, hclsM, hclsB]; abel

    have e₁ := hV.interNum_of_cls_eq_sum hP (Q := fun _ => L) (fun _ => hL.isLB)
      (fun _ => ![(q : ℤ), 1]) (fun _ => by
        rw [Fin.sum_univ_two, hclsL]
        simp [P])
    have hlow : (q : ℤ) ^ (d + 1) * topSelfIntersection ℂ N (d + 1) ≤ topSelfIntersection ℂ L (d + 1) := by
      rw [topSelf_def ℂ L, e₁]
      have hnn : ∀ a : Fin (d + 1) → Fin 2,
          0 ≤ (∏ i, (![(q : ℤ), 1] : Fin 2 → ℤ) (a i)) * interNum ℂ (GlobalTheory.structureModule X) (P ∘ a) :=
        fun a => mul_nonneg (Finset.prod_nonneg fun i _ => by
          rcases Fin.exists_fin_two.1 ⟨a i, rfl⟩ with h | h <;> rw [h] <;> simp <;> omega) (hI a)
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun a _ => hnn a)
        (Finset.mem_univ (fun _ => (0 : Fin 2))))
      simp only [Matrix.cons_val_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rfl

    let n : Fin (d + 1) → Fin 2 → ℤ := Fin.cons ![0, 2] (fun _ => ![(q : ℤ), 1])
    have e₂ := hV.interNum_of_cls_eq_sum hP (Q := Fin.cons B (fun _ : Fin d => L))
      (Fin.cases hB.isLB fun _ => hL.isLB) n (fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [Fin.sum_univ_two]
          simp only [Fin.cons_zero, n]
          rw [hclsB]
          simp [P]
        · rw [Fin.sum_univ_two]
          simp only [Fin.cons_succ, n]
          rw [hclsL]
          simp [P])
    have hup : interNum ℂ (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X)
        ≤ 2 * (q : ℤ) ^ d * S := by
      rw [e₂, hSdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right ?_ (hI a)
      refine prod_le (q : ℤ) hq1 n (fun j => ?_) (fun i j => ?_) a
      · rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h <;> simp [n]
      · rcases Fin.exists_fin_two.1 ⟨j, rfl⟩ with h | h <;> subst h <;> simp [n] <;> omega
    have hineq : ((d : ℤ) + 1) * interNum ℂ (GlobalTheory.structureModule X)
        (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection ℂ L (d + 1) := by
      have hqd : (0 : ℤ) < (q : ℤ) ^ d := pow_pos (by omega) d
      have hd1 : (0 : ℤ) ≤ (d : ℤ) + 1 := by positivity
      calc ((d : ℤ) + 1) * interNum ℂ (GlobalTheory.structureModule X)
            (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X)
          ≤ ((d : ℤ) + 1) * (2 * (q : ℤ) ^ d * S) := mul_le_mul_of_nonneg_left hup hd1
        _ = (q : ℤ) ^ d * (2 * (d + 1) * S) := by ring
        _ < (q : ℤ) ^ d * q := mul_lt_mul_of_pos_left (by rw [hqS]; omega) hqd
        _ = (q : ℤ) ^ (d + 1) * 1 := by ring
        _ ≤ (q : ℤ) ^ (d + 1) * topSelfIntersection ℂ N (d + 1) :=
          mul_le_mul_of_nonneg_left (by omega) (by positivity)
        _ ≤ topSelfIntersection ℂ L (d + 1) := hlow
    obtain ⟨r, hr, hs⟩ := exists_hasNonzeroSec_pow_of_ample_sub_ample ℂ X hp' d hD.le L B M hL hB hM
      e hineq
    obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
    refine ⟨q * r, lbPow A r, isLB_lbPow hA.isLB r, divOfSec (isLB_lbPow hM r) s hs,
      Nat.mul_pos (Nat.succ_pos _) hr, (isAmpleLB_pow_iff hA.isLB hr).2 hA,
      eff_divOfSec_of_sec _ s hs, ?_⟩
    rw [← toPic_apply, (presents_divOfRatSec _ (isRatSec_ratOfSec s hs)).toPic_eq,
      cls_lbPow hA.isLB, cls_lbPow hM, hclsM]
    first
      | module
      | (simp only [← natCast_zsmul, smul_sub, smul_smul, Nat.cast_mul]; rw [mul_comm (r : ℤ)]; abel)
