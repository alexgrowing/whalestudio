import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.AmpleNefCombinationBound

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MorseNum

theorem morse_A_sq : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (A N L M : LB X) (hA : IsAmpleLB A) (hN : IsNef k N) (hL : IsAmpleLB L) (hM : M.IsLB), (∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons A P : Fin (d + 1) → LB X)) → 0 < topSelfIntersection k A (d + 1) → ∀ q b c : ℕ, 1 ≤ q → q ≤ b → b ≤ c * q → cls L hL.isLB = q • cls N hN.isLB + b • cls A hA.isLB → cls M hM = cls N hN.isLB + c • cls A hA.isLB → 2 * ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons A (fun _ : Fin d => M) : Fin (d + 1) → LB X) < q → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons (lbPow A 2) (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) := by
  intro k _ _ X _ hproj d hd A N L M hA hN hL hM hnef htop q b c hq1 hqb hbc hLcls hMcls hlt
  have hD : DiffVanish (d + 1 + 1) (chiPic k (GlobalTheory.structureModule X)) := by
    refine diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom (k := k) (X := X)) _ hproj ?_
    rw [suppDim_structureModule]
    exact hd
  set F := GlobalTheory.structureModule X with hF
  let Lv : Fin 2 → LB X := ![A, N]
  have hLv : ∀ j, (Lv j).IsLB := by
    intro j; fin_cases j
    · exact hA.isLB
    · exact hN.isLB
  have hLvnef : ∀ j, IsNef k (Lv j) := by
    intro j; fin_cases j
    · exact hA.isNef
    · exact hN
  let nL : Fin (d + 1) → Fin 2 → ℤ := Fin.cons ![1, 0] (fun _ => ![(b : ℤ), (q : ℤ)])
  let nM : Fin (d + 1) → Fin 2 → ℤ := Fin.cons ![1, 0] (fun _ => ![(c : ℤ), 1])
  have hQL : ∀ i, ((Fin.cons A (fun _ : Fin d => L) : Fin (d + 1) → LB X) i).IsLB := by
    intro i; refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hA.isLB
    · simpa using hL.isLB
  have hQM : ∀ i, ((Fin.cons A (fun _ : Fin d => M) : Fin (d + 1) → LB X) i).IsLB := by
    intro i; refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hA.isLB
    · simpa using hM
  have eL := DiffVanish.interNum_of_cls_eq_sum hD hLv hQL nL (by
    intro i; refine Fin.cases ?_ (fun i => ?_) i
    · simp [nL, Lv, Fin.sum_univ_two]
    · simp only [nL, Lv, Fin.sum_univ_two, Fin.cons_succ, Fin.cons_zero]
      simp [hLcls, natCast_zsmul, add_comm])
  have eM := DiffVanish.interNum_of_cls_eq_sum hD hLv hQM nM (by
    intro i; refine Fin.cases ?_ (fun i => ?_) i
    · simp [nM, Lv, Fin.sum_univ_two]
    · simp only [nM, Lv, Fin.sum_univ_two, Fin.cons_succ, Fin.cons_zero]
      simp [hMcls, natCast_zsmul, add_comm])
  have hbq : (b : ℤ) ≤ (q : ℤ) * c := by
    have : b ≤ q * c := by rw [mul_comm]; exact hbc
    exact_mod_cast this
  have hent0 : ∀ j : Fin 2, 0 ≤ (![(b : ℤ), (q : ℤ)] : Fin 2 → ℤ) j := by
    intro j; fin_cases j <;> simp
  have hent1 : ∀ j : Fin 2, (![(b : ℤ), (q : ℤ)] : Fin 2 → ℤ) j ≤ (q : ℤ) * (![(c : ℤ), 1] : Fin 2 → ℤ) j := by
    intro j; fin_cases j
    · simpa using hbq
    · simp
  have key : interNum k F (Fin.cons A (fun _ : Fin d => L) : Fin (d + 1) → LB X)
      ≤ (q : ℤ) ^ d * interNum k F (Fin.cons A (fun _ : Fin d => M) : Fin (d + 1) → LB X) := by
    rw [eL, eM, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _
    have h01 : a 0 = 0 ∨ a 0 = 1 := by
      generalize a 0 = j
      fin_cases j <;> simp
    rcases h01 with h0 | h0
    · have hJ : 0 ≤ interNum k F (Lv ∘ a) := by
        have hc : Lv ∘ a = Fin.cons A (fun i : Fin d => Lv (a i.succ)) := by
          funext i
          refine Fin.cases ?_ (fun i => ?_) i
          · simp [h0, Lv]
          · simp
        rw [hc]
        exact hnef _ (fun i => hLvnef _)
      have hc : (∏ i, nL i (a i)) ≤ (q : ℤ) ^ d * ∏ i, nM i (a i) := by
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
        simp only [nL, nM, Fin.cons_zero, Fin.cons_succ, h0]
        simp only [Matrix.cons_val_zero, one_mul]
        calc (∏ i : Fin d, (![(b : ℤ), (q : ℤ)] : Fin 2 → ℤ) (a i.succ))
            ≤ ∏ i : Fin d, ((q : ℤ) * (![(c : ℤ), 1] : Fin 2 → ℤ) (a i.succ)) :=
              Finset.prod_le_prod (fun i _ => hent0 _) (fun i _ => hent1 _)
          _ = (q : ℤ) ^ d * ∏ i : Fin d, (![(c : ℤ), 1] : Fin 2 → ℤ) (a i.succ) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc (∏ i, nL i (a i)) * interNum k F (Lv ∘ a)
          ≤ ((q : ℤ) ^ d * ∏ i, nM i (a i)) * interNum k F (Lv ∘ a) := mul_le_mul_of_nonneg_right hc hJ
        _ = _ := by ring
    · have hz1 : (∏ i, nL i (a i)) = 0 := by
        rw [Fin.prod_univ_succ]; simp [nL, h0]
      have hz2 : (∏ i, nM i (a i)) = 0 := by
        rw [Fin.prod_univ_succ]; simp [nM, h0]
      rw [hz1, hz2]; simp
  have h2 : interNum k F (Fin.cons (lbPow A 2) (fun _ : Fin d => L) : Fin (d + 1) → LB X)
      = 2 * interNum k F (Fin.cons A (fun _ : Fin d => L) : Fin (d + 1) → LB X) := by
    have hA2 : (lbPow A 2).IsLB := isLB_lbPow hA.isLB 2
    rw [DiffVanish.interNum_cons_of_cls_eq_add hD (le_refl _) (fun _ => hL.isLB) hA2 hA.isLB hA.isLB
      (by rw [cls_lbPow hA.isLB 2 hA2, two_nsmul])]
    ring
  have hq : (0 : ℤ) < (q : ℤ) ^ d := by
    have : (0 : ℤ) < q := by exact_mod_cast hq1
    positivity
  have hlow := NefLower.topSelf_lower k X hproj d hd A N L hA hN hL hnef q b hLcls
  have hqb' : (q : ℤ) ^ (d + 1) ≤ (b : ℤ) ^ (d + 1) :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hqb) _
  have htop1 : (1 : ℤ) ≤ topSelfIntersection k A (d + 1) := htop
  have s4 : (b : ℤ) ^ (d + 1) ≤ (b : ℤ) ^ (d + 1) * topSelfIntersection k A (d + 1) :=
    le_mul_of_one_le_right (by positivity) htop1
  have s1 : ((d : ℤ) + 1) * (2 * interNum k F (Fin.cons A (fun _ : Fin d => L) : Fin (d + 1) → LB X))
      ≤ (q : ℤ) ^ d * (2 * ((d : ℤ) + 1) * interNum k F (Fin.cons A (fun _ : Fin d => M) : Fin (d + 1) → LB X)) := by
    have := mul_le_mul_of_nonneg_left key (show (0 : ℤ) ≤ 2 * ((d : ℤ) + 1) by positivity)
    calc _ = 2 * ((d : ℤ) + 1) * interNum k F (Fin.cons A (fun _ : Fin d => L) : Fin (d + 1) → LB X) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have s2 := mul_lt_mul_of_pos_left hlt hq
  have s3 : (q : ℤ) ^ d * q = (q : ℤ) ^ (d + 1) := by ring
  rw [h2]
  linarith

end GlobalTheory.MorseNum
