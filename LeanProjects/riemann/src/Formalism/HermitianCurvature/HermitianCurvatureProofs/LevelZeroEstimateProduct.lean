import Formalism.HermitianCurvature.StatementC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JointInstanceTheoremA

namespace Formalism.FourierDecayAlt.P

open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C

open scoped ComplexOrder

noncomputable section

open Classical

namespace Cx1

theorem psd_pullback {α β : Type} (Y : Finset α) (φ : α → β) (k : β → β → ℂ) (Z : Finset β)
    (hZ : ∀ x ∈ Y, φ x ∈ Z) (h : TB.PSDOn Z k) : TB.PSDOn Y (fun x y => k (φ x) (φ y)) := by
  simp only [TB.PSDOn] at h ⊢
  exact h.submatrix (fun x : Y => (⟨φ x, hZ x x.2⟩ : Z))

theorem psd_zero {α : Type} (Y : Finset α) : TB.PSDOn Y (fun _ _ => (0 : ℂ)) := by
  simp only [TB.PSDOn]
  exact Matrix.PosSemidef.zero

end Cx1

theorem gram_positive_semidefinite : C.GramPSDOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hP _ Kr hK0 Th e ε hε i w Y
  show TB.PSDOn Y (S.gram ε i w.1)
  have prodPSD : ∀ (s : Finset (Fin S.f)) (k : Fin S.f → TB.Pt E → TB.Pt E → ℂ),
      (∀ v, TB.PSDOn Y (k v)) → TB.PSDOn Y (fun p q => ∏ v ∈ s, k v p q) := by
    intro s k hk
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, TB.PSDOn]
      let A : Matrix Unit Y ℂ := Matrix.of fun _ _ => 1
      have h2 := Matrix.posSemidef_conjTranspose_mul_self A
      convert h2 using 1
      ext x y
      simp [A, Matrix.mul_apply]
    | @insert a s ha ih =>
      simp only [TB.PSDOn] at ih ⊢
      have h1 : (Matrix.of fun x y : Y => ∏ v ∈ insert a s, k v x y) =
          (Matrix.of fun x y : Y => k a x y).hadamard (Matrix.of fun x y : Y => ∏ v ∈ s, k v x y) := by
        ext x y
        simp [Finset.prod_insert ha, Matrix.hadamard]
      rw [h1]
      exact (hk a).hadamard ih
  by_cases hi : i ≤ S.G.r + 1
  · have hg : S.gram ε i w.1 =
        fun p q => ∏ v, S.gramLoc v ε i (w.1 v) (loc (S.σ v) p) (loc (S.σ v) q) := by
      funext p q
      simp [Formalism.FourierDecayAlt.C.HidaSetting.gram, hi]
    rw [hg]
    exact prodPSD Finset.univ _ fun v =>
      Cx1.psd_pullback Y (loc (S.σ v)) _ _ (fun x hx => Finset.mem_image_of_mem _ hx)
        (hP v ε hε i hi w _)
  · have hg : S.gram ε i w.1 = fun _ _ => 0 := by
      funext p q
      simp [Formalism.FourierDecayAlt.C.HidaSetting.gram, hi]
    rw [hg]
    exact Cx1.psd_zero Y

theorem words_pos_of_parts : C.WordsPosOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG Kr hK0 Th e w
  show 0 < Word.size S.P w.1
  unfold Word.size
  apply Finset.prod_pos
  intro v _
  apply List.prod_pos
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  apply abs_pos.mpr
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
  have hadm := w.2.1.1 v j hj
  by_cases hb : ((w.1 v)[j]'hj).1 = true
  · rw [if_pos hb] at hadm
    have hy : (∃ a, ((w.1 v)[j]'hj).2 ∈ S.grid v a) ∨ ((w.1 v)[j]'hj).2 ∈ S.grid1 v := by
      rcases Finset.mem_union.mp hadm with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    exact ((hG v).2.2.2.2.2 _ hy).2.2.1
  · rw [if_neg hb] at hadm
    have hy : (∃ a, ((w.1 v)[j]'hj).2 - 1 ∈ S.grid v a) ∨ ((w.1 v)[j]'hj).2 - 1 ∈ S.grid1 v := by
      rcases Finset.mem_union.mp hadm with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    have := ((hG v).2.2.2.2.2 _ hy).2.2.2
    rwa [sub_add_cancel] at this

theorem wave_estimate_of_integral : C.EstWaveOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG hI hP Kr hK0 Th e ε hε i hi1 hi2 w hw hcnt
  obtain ⟨θ, hθ, hb⟩ := hP ε hε i hi1 hi2 w hw hcnt
  exact ⟨θ, hθ, fun Y hY κ hκ => ⟨(hI ε hε i hi1 hi2 w Y hY κ hκ).2,
    fun l hl hl0 => ⟨S.bigPlaces i l, hb Y hY κ hκ l hl hl0⟩⟩⟩

theorem lift_estimate_of_base : C.EstLiftOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S h Kr hK0 Th e
  exact h

theorem block_estimate_of_base : C.EstBlockOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S C₄ h Kr hK0 Th e
  exact h

theorem level_zero_estimate_product : C.EstEOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S jv hG hE Kr hK0 Th e w _
  have hgram : ∀ ε, (S.mkData Kr hK0 Th e).gram ε 0 w [] [] = ∏ v, (S.pd v).RR ε 0 (w.1 v) [] [] := by
    intro ε
    show S.gram ε 0 w.1 [] [] = _
    simp [HidaSetting.gram, HidaSetting.gramLoc, loc, nLoc, nAux]
  have hsize : (S.mkData Kr hK0 Th e).wt w = ∏ v, S.sizeAt v (w.1 v) := rfl
  have hpos : 0 < ∏ v, S.sizeAt v (w.1 v) := by
    rw [← hsize]
    exact words_pos_of_parts E Wp Wq S hG Kr hK0 Th e w
  have hlim : Tendsto (fun ε => ∏ v, (S.pd v).RR ε 0 (w.1 v) [] []) (𝓝[>] 0)
      (𝓝 (∏ v, ((S.sizeAt v (w.1 v) * jv v : ℝ) : ℂ))) :=
    tendsto_finsetProd _ (fun v _ => hE w v)
  have hre := ((Complex.continuous_re.tendsto _).comp hlim).div_const (∏ v, S.sizeAt v (w.1 v))
  have key : (∏ v, ((S.sizeAt v (w.1 v) * jv v : ℝ) : ℂ)).re /
      (∏ v, S.sizeAt v (w.1 v)) = ∏ v, jv v := by
    rw [← Complex.ofReal_prod, Complex.ofReal_re, Finset.prod_mul_distrib,
      mul_div_cancel_left₀ _ hpos.ne']
  rw [key] at hre
  simp_rw [hgram, hsize]
  exact hre

theorem cutoff_of_parts : C.CutoffOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S H _ _ Vt hPG Kr hK0 Th e Y hY
  filter_upwards [hPG Y hY] with ε hε p hp q hq _
  exact hε p hp q hq

end

end Formalism.FourierDecayAlt.P
