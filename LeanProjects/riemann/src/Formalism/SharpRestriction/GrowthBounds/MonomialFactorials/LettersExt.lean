import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BoxOfFibres

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Letters

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem letters_ext {N : ℕ} (L L' : Formalism.GM.M.Letters N) (h1 : L.vec = L'.vec) (h2 : L.deg = L'.deg) : L = L' := by
  cases L; cases L'; simp_all

theorem uTop_inj : Function.Injective (uTop (X.S C0 CE1 CE2)) := by
  intro i j h
  have h' := congrArg Fin.val h
  simp only [uTop] at h'
  exact Fin.ext (by omega)

abbrev lLL (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) : Formalism.GM.M.Letters (2 * X.s + 1) :=
  (gB C0 CE1 CE2 X aTop 0 b).lettersAt x.1 x.2

abbrev gT (b : SegBlock X.s X.r) : Formalism.GM.M.TieData := (gB C0 CE1 CE2 X (fun _ => 0) 0 b).T

theorem deg_eta (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) (i : Fin (X.S C0 CE1 CE2).t)
    (q : Fin (2 * X.s + 1)) (hq : (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1) :
    (lLL C0 CE1 CE2 X aTop b x).deg q = coarseC X.p (X.S C0 CE1 CE2) aTop b (uTop (X.S C0 CE1 CE2) i) - x.1 i := by
  have hi := i.2
  simp only [SegData.t] at hi
  simp only [lLL, Formalism.GM.M.BlockData.lettersAt, gB, gmB, gmL, gmT, blockData, BlockData.withMargin, blockBase, segChain, segTies]
  have h1 : (q : ℕ) ≠ 2 * X.s := by omega
  have hodd : ¬ (q : ℕ) % 2 = 0 := by omega
  have htop : topOf q h1 = uTop (X.S C0 CE1 CE2) i := Fin.ext (by simp only [topOf, uTop]; omega)
  have hnl : ¬ ((uTop (X.S C0 CE1 CE2) i : ℕ) < (X.S C0 CE1 CE2).sigma) := by simp only [uTop]; omega
  have hu : ¬ q = ⟨2 * X.s, by omega⟩ := by
    intro h
    exact h1 (by rw [h])
  rw [dif_neg h1, if_neg hodd, htop, if_neg hnl]
  simp only [hu, if_false, Nat.sub_zero]
  congr 1
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro j _ hj
    have hj' : (j : ℕ) ≠ (i : ℕ) := fun h => hj (Fin.ext h)
    apply if_neg
    show ¬ ((q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (j : ℕ)) ∨ (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (j : ℕ)) + 1)
    omega
  · intro h
    exact absurd (Finset.mem_univ i) h
  · exact if_pos (Or.inr (show (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1 from hq))

theorem deg_other (aTop aTop' : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X)
    (hag : ∀ l : Fin X.s, (l : ℕ) < (X.S C0 CE1 CE2).sigma → aTop l = aTop' l)
    (q : Fin (2 * X.s + 1)) (hq : ¬ ∃ i : Fin (X.S C0 CE1 CE2).t, 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1 = (q : ℕ)) :
    (lLL C0 CE1 CE2 X aTop b x).deg q = (lLL C0 CE1 CE2 X aTop' b x).deg q := by
  have hLL : (gB C0 CE1 CE2 X aTop 0 b).LL.deg q = (gB C0 CE1 CE2 X aTop' 0 b).LL.deg q := by
    simp only [gB, gmB, gmL, blockData, BlockData.withMargin, blockBase, segChain]
    by_cases h : (q : ℕ) = 2 * X.s
    · rw [dif_pos h, dif_pos h]
    · rw [dif_neg h, dif_neg h]
      have hv : ((topOf q h : Fin X.s) : ℕ) = (q : ℕ) / 2 := rfl
      have hlt : (q : ℕ) / 2 < X.s := by
        have := (topOf q h).2
        omega
      split_ifs with h2 h3 h3
      · rfl
      · rfl
      · simp only [coarseC]
        rw [hag _ h3]
      · exfalso
        apply hq
        refine ⟨⟨(q : ℕ) / 2 - (X.S C0 CE1 CE2).sigma, ?_⟩, ?_⟩
        · simp only [SegData.t]
          omega
        · simp only
          omega
  simp only [lLL, Formalism.GM.M.BlockData.lettersAt]
  rw [hLL]
  rfl

theorem lLL_ovr (a : Fin X.s → ℕ) (n : Fin (X.S C0 CE1 CE2).t → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    lLL C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) b x =
      (lLL C0 CE1 CE2 X a b x).setTies (gT C0 CE1 CE2 X b)
        (fun i : Fin (X.S C0 CE1 CE2).t =>
          (n i - ∑ c, b.ry (uTop (X.S C0 CE1 CE2) i) c) / (X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) - x.1 i) := by
  apply letters_ext
  · rfl
  · funext q
    simp only [Formalism.GM.M.Letters.setTies]
    split_ifs with h
    · have hc := Classical.choose_spec h
      have hp : (gT C0 CE1 CE2 X b).pos (Classical.choose h) = 2 * ((X.S C0 CE1 CE2).sigma + ((Classical.choose h : Fin (X.S C0 CE1 CE2).t) : ℕ)) := rfl
      have hjq : (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + ((Classical.choose h : Fin (X.S C0 CE1 CE2).t) : ℕ)) + 1 := by
        omega
      rw [deg_eta C0 CE1 CE2 X _ b x _ q hjq]
      have he : ∃ i, uTop (X.S C0 CE1 CE2) i = uTop (X.S C0 CE1 CE2) (Classical.choose h) := ⟨_, rfl⟩
      have hov : ovr (uTop (X.S C0 CE1 CE2)) a n (uTop (X.S C0 CE1 CE2) (Classical.choose h)) = n (Classical.choose h) := by
        simp only [ovr, dif_pos he]
        rw [uTop_inj C0 CE1 CE2 X (Classical.choose_spec he)]
      simp only [coarseC, hov]
      rfl
    · rw [deg_other C0 CE1 CE2 X _ a b x ?_ q ?_]
      · intro l hl
        have hne : ¬ ∃ i, uTop (X.S C0 CE1 CE2) i = l := by
          rintro ⟨i, rfl⟩
          simp only [uTop] at hl
          omega
        simp only [ovr, dif_neg hne]
      · rintro ⟨i, hi⟩
        exact h ⟨i, hi⟩

end Letters

end Formalism.MainNotions.G.SymmetricFormBlocks

end
