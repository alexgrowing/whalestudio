import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.TopParam

def Dset (R : Ranks) (h : HCParam R) : Finset ℚ :=
  (Finset.univ.image h.v ∪ Finset.univ.image (fun j => -h.b j)) ∪
    Finset.univ.biUnion (fun j => TPar.block (-h.e j) R.t)

theorem sgHC_sub_mem (R : Ranks) (h : HCParam R) (i : ℕ) (hi : i < R.N R.m - 1) :
    sgHC R h i - (R.m * (R.t + 1) / 2 : ℚ) ∈ Dset R h := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  unfold sgHC Dset
  simp only [add_sub_cancel_left]
  split_ifs with h1 h2 h3
  · simp
  · apply Finset.mem_union_left; apply Finset.mem_union_right; simp
  · apply Finset.mem_union_right
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, TPar.block, Finset.mem_image, Finset.mem_range]
    refine ⟨⟨_, h2⟩, (i - (R.k - 1)) % (R.t + 1) - 1, ?_, ?_⟩
    · have := Nat.mod_lt (i - (R.k-1)) (show 0 < R.t + 1 by omega); omega
    · have : 1 ≤ (i - (R.k - 1)) % (R.t + 1) := Nat.pos_of_ne_zero h3
      push_cast [Nat.cast_sub this]; ring
  · exfalso; apply h2
    unfold Ranks.N at hi
    rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
    generalize R.m * (R.t + 1) = P at hi
    omega

theorem card_Dset_le (R : Ranks) (h : HCParam R) : (Dset R h).card ≤ R.N R.m - 1 := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  unfold Dset
  calc _ ≤ (Finset.univ.image h.v ∪ Finset.univ.image (fun j => -h.b j)).card
          + (Finset.univ.biUnion (fun j => TPar.block (-h.e j) R.t)).card := Finset.card_union_le _ _
    _ ≤ ((R.k - 1) + R.m) + R.m * R.t := by
        gcongr
        · refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
          · exact Finset.card_image_le.trans (by simp)
          · exact Finset.card_image_le.trans (by simp)
        · refine (Finset.card_biUnion_le_card_mul _ _ R.t ?_).trans (by simp)
          intro j _
          exact Finset.card_image_le.trans (by simp)
    _ = R.N R.m - 1 := by
        unfold Ranks.N
        have : R.m * (R.t + 1) = R.m + R.m * R.t := by ring
        rw [this]; omega

end GlobalTheory.Core.Rk.TopParam

namespace GlobalTheory.Core.Rk.TopParam

theorem neg_lam_rev_eq : ∀ (D : D7) (u : D.what₂.Word) (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)), (∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i) → ∀ τ (i : Fin D.sp.X'.rank), -M.lam τ (Fin.rev i) = (((sgT u τ).w (Fin.cast (rankP D) i) : ℤ) : ℝ) + ((rhoVec D.sp.X'.rank i : ℚ) : ℝ) := by
  intro D u M hsg τ i
  obtain ⟨hanti, q, hq, hS⟩ := M.enum τ
  have hdiv : ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℚ) = (D.R.m : ℚ) * (D.R.t + 1) / 2 := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rw [Nat.cast_div (by rw [ha]; exact Dvd.intro (a * (D.R.t + 1)) (by ring)) (by norm_num)]
    push_cast; ring
  have hn : ((D.sp.X'.rank : ℕ) : ℚ) = ((D.R.N D.R.m - 1 : ℕ) : ℚ) := by rw [rankP D]
  let F : Fin D.sp.X'.rank → ℚ := fun i =>
    sgHC D.R (D.hcW u τ) (Fin.cast (rankP D) i) - (D.R.m * (D.R.t + 1) / 2 : ℚ)
  let G : Fin D.sp.X'.rank → ℚ := fun i => -q (Fin.rev i)
  have hRHS : ∀ i : Fin D.sp.X'.rank,
      (((sgT u τ).w (Fin.cast (rankP D) i) : ℤ) : ℚ) + rhoVec D.sp.X'.rank i = F i := by
    intro i
    have h1 := hsg (Fin.cast (rankP D) i) τ
    simp only [sgT, shW, F]
    rw [Int.cast_sub, h1, Int.cast_natCast, hdiv]
    simp only [rhoVec, Fin.coe_cast]
    rw [hn]; ring
  have hFa : StrictAnti F := by
    intro i j hij
    rw [← hRHS i, ← hRHS j]
    have h1 : (sgT u τ).w (Fin.cast (rankP D) j) ≤ (sgT u τ).w (Fin.cast (rankP D) i) :=
      (sgT u τ).anti (by rw [Fin.le_iff_val_le_val]; simp only [Fin.coe_cast]; exact hij.le)
    have h2 : rhoVec D.sp.X'.rank j < rhoVec D.sp.X'.rank i := by
      simp only [rhoVec]; have : (i : ℚ) < j := by exact_mod_cast hij
      linarith
    have h1' : ((sgT u τ).w (Fin.cast (rankP D) j) : ℚ) ≤ (sgT u τ).w (Fin.cast (rankP D) i) := by exact_mod_cast h1
    linarith
  have hGa : StrictAnti G := by
    intro i j hij
    have h1 := hanti (Fin.rev_lt_rev.mpr hij)
    rw [hq, hq] at h1
    have h1' : q (Fin.rev i) < q (Fin.rev j) := by exact_mod_cast h1
    simp only [G]; linarith
  have hFm : ∀ x, F x ∈ Dset D.R (D.hcW u τ) := by
    intro x
    have := sgHC_sub_mem D.R (D.hcW u τ) (Fin.cast (rankP D) x) (Fin.cast (rankP D) x).isLt
    simpa [F] using this
  have hGm : ∀ x, G x ∈ Dset D.R (D.hcW u τ) := by
    intro x
    have hmem : (q (Fin.rev x), M.ε τ (Fin.rev x)) ∈ parB (Ptw D) D.R.m τ := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hodd : ¬ Odd D.R.m := Nat.not_odd_iff_even.mpr D.R.m_even
    simp only [parB, dualPar, TPar.Dpar, Finset.mem_image, hodd, if_false, add_zero] at hmem
    obtain ⟨⟨y1, y2⟩, ⟨⟨z1, z2⟩, hz, hzy⟩, hy⟩ := hmem
    simp only [Prod.mk.injEq] at hzy hy
    obtain ⟨rfl, rfl⟩ := hzy
    have hGx : G x = z1 := by simp only [G]; rw [← hy.1]; ring
    rw [hGx]
    simp only [Dset, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter, Prod.mk.injEq, D.hcW_v, D.hcW_b, D.hcW_e] at hz ⊢
    rcases hz with (⟨a, ha, -⟩ | ⟨a, ha, -⟩) | ⟨a, -, w, hw, hwz, -⟩
    · exact Or.inl (Or.inl ⟨a, ha⟩)
    · exact Or.inl (Or.inr ⟨a, ha⟩)
    · exact Or.inr ⟨a, hwz ▸ hw⟩
  have hcard : (Dset D.R (D.hcW u τ)).card = D.sp.X'.rank := by
    apply le_antisymm
    · rw [rankP D]; exact card_Dset_le _ _
    · have hsub : Finset.univ.image F ⊆ Dset D.R (D.hcW u τ) := by
        intro y hy; obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy; exact hFm x
      have := Finset.card_le_card hsub
      rwa [Finset.card_image_of_injective _ hFa.injective, Finset.card_univ, Fintype.card_fin] at this
  have hFG : F ∘ Fin.rev = G ∘ Fin.rev := by
    have e1 := Finset.orderEmbOfFin_unique hcard (f := F ∘ Fin.rev) (fun x => hFm _)
      (fun a b hab => hFa (Fin.rev_lt_rev.mpr hab))
    have e2 := Finset.orderEmbOfFin_unique hcard (f := G ∘ Fin.rev) (fun x => hGm _)
      (fun a b hab => hGa (Fin.rev_lt_rev.mpr hab))
    exact e1.trans e2.symm
  have hi := congrFun hFG (Fin.rev i)
  simp only [Function.comp, Fin.rev_rev, G] at hi
  rw [hq]
  have key := congrArg (fun x : ℚ => (x : ℝ)) ((hRHS i).trans hi)
  push_cast at key
  rw [key]

end GlobalTheory.Core.Rk.TopParam
