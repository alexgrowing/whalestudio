import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZCombExpand
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open GroundTheory.Heights₂.Heights.Inter (famExt famExt_apply famExt_basis famExt_symm)

noncomputable section

set_option linter.unusedSectionVars false

namespace ZCombExpand

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem famExt_symm_of (e : Fin 2 → HermLine ι) (he : ∀ i, IsSmoothHerm (e i))
    (hJ : ∀ (L : Fin n → HermLine ι) (σ : Equiv.Perm (Fin n)), (∀ j, IsSmoothHerm (L j)) →
      J P n (L ∘ σ) = J P n L) :
    IsSymmForm (famExt J P n e) := by
  intro σ v
  rw [famExt_apply, famExt_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin 2))) _ _ fun s => ?_
  have h1 : e ∘ (Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) = (e ∘ s) ∘ σ.symm := rfl
  have h2 : ∏ j, v j ((Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) j) = ∏ j, (v ∘ σ) j (s j) := by
    refine (Equiv.prod_comp σ fun j => v j (s (σ.symm j))).symm.trans ?_
    simp
  rw [h1, h2, hJ (e ∘ s) σ.symm fun j => he _]

theorem famExt_expand (e : Fin 2 → HermLine ι) (hs : IsSymmForm (famExt J P n e)) (q p : ℝ) :
    famExt J P n e (fun _ => ![q, p]) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * q ^ (n - i) * p ^ i *
        J P n (fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1) := by
  classical
  have hw : (fun _ : Fin n => (![q, p] : Fin 2 → ℝ)) =
      fun _ => p • (Pi.single 1 1 : Fin 2 → ℝ) + q • (Pi.single 0 1 : Fin 2 → ℝ) := by
    funext j i
    fin_cases i <;> simp
  rw [hw, symm_expand _ hs, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [show n + 1 - 1 - i = n - i by omega]
  have hmix : (mix (n - i) (Pi.single 0 1) (p • Pi.single 1 1) : Fin n → Fin 2 → ℝ) =
      (Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) < n - i).piecewise
        (fun j => p • (mix (n - i) (Pi.single 0 1) (Pi.single 1 1) : Fin n → Fin 2 → ℝ) j)
        (mix (n - i) (Pi.single 0 1) (Pi.single 1 1)) := by
    funext j
    by_cases h : (j : ℕ) < n - i
    · rw [Finset.piecewise_eq_of_notMem _ _ _ (by simp; omega)]
      simp [mix, h]
    · rw [Finset.piecewise_eq_of_mem _ _ _ (by simp; omega)]
      simp [mix, h]
  have hcard : (Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) < n - i).card = i := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
      Fintype.card_fin, Fin.card_filter_val_lt]
    omega
  have hbasis : (mix (n - i) (Pi.single 0 1) (Pi.single 1 1) : Fin n → Fin 2 → ℝ) =
      fun j => Pi.single ((fun j : Fin n => if (j : ℕ) < n - i then (0 : Fin 2) else 1) j) 1 := by
    funext j
    simp only [mix]
    split_ifs <;> rfl
  have hlist : (e ∘ fun j : Fin n => if (j : ℕ) < n - i then (0 : Fin 2) else 1) =
      fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1 := by
    funext j
    simp only [Function.comp]
    split_ifs <;> rfl
  rw [hmix, MultilinearMap.map_piecewise_smul, Finset.prod_const, hcard, hbasis, famExt_basis, hlist,
    smul_eq_mul, Nat.choose_symm hin]
  ring

end ZCombExpand

theorem ZCombExpand.proof : ZCombExpand.Statement := by
  intro K _ ι _ I hI P d M H q p hP hM hH
  set e : Fin 2 → HermLine ι := ![M, H] with he_def
  have he : ∀ i, IsSmoothHerm (e i) := by
    intro i
    fin_cases i
    · exact hM
    · exact hH
  set Z := HermLine.zcomb M H (q : ℤ) (p : ℤ) with hZ_def
  have hZ : IsSmoothHerm Z := ZCombLimit.isSmoothHerm_zcomb_int hM hH _ _
  refine ⟨?_, ?_⟩
  · have hposition : ∀ (L : Fin d → HermLine ι) (a : Fin d), (∀ j, IsSmoothHerm (L j)) →
        I P d (Function.update L a Z) =
          (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 0 * I P d (Function.update L a (e 0)) +
            (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 1 * I P d (Function.update L a (e 1)) := by
      intro L a hL
      cases d with
      | zero => exact a.elim0
      | succ m =>
        have h := ZCombLimit.fam_update_zcomb_int hI hP L hL a hM hH (q : ℤ) (p : ℤ)
        simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := I) (P := P) IsSmoothHerm e Z ![(q : ℝ), (p : ℝ)] he hZ
      hposition Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    rw [key, ZCombExpand.famExt_expand e (famExt_symm hI hP e he)]
    rfl
  · intro hd
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    let J : Ideal (MRing ι) → (m : ℕ) → (Fin m → HermLine ι) → ℝ :=
      fun P' m L => I P' (m + 1) (Fin.cons (α := fun _ => HermLine ι) M L)
    have hcons : ∀ L : Fin n → HermLine ι, (∀ j, IsSmoothHerm (L j)) →
        ∀ j, IsSmoothHerm (Fin.cons (α := fun _ => HermLine ι) M L j) := by
      intro L hL j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hM
      · simpa using hL j
    have hsymm : ∀ (L : Fin n → HermLine ι) (σ : Equiv.Perm (Fin n)), (∀ j, IsSmoothHerm (L j)) →
        J P n (L ∘ σ) = J P n L := by
      intro L σ hL
      have hc : (Fin.cons (α := fun _ => HermLine ι) M (L ∘ σ) : Fin (n + 1) → HermLine ι) =
          (Fin.cons (α := fun _ => HermLine ι) M L) ∘ (Equiv.Perm.decomposeFin.symm (0, σ)) := by
        funext j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp [Equiv.Perm.decomposeFin_symm_apply_zero]
        · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
      show I P (n + 1) _ = I P (n + 1) _
      rw [hc, hI.1 P (n + 1) _ _ hP (hcons L hL)]
    have hposition : ∀ (L : Fin n → HermLine ι) (a : Fin n), (∀ j, IsSmoothHerm (L j)) →
        J P n (Function.update L a Z) =
          (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 0 * J P n (Function.update L a (e 0)) +
            (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 1 * J P n (Function.update L a (e 1)) := by
      intro L a hL
      show I P (n + 1) _ = _ * I P (n + 1) _ + _ * I P (n + 1) _
      rw [Fin.cons_update, Fin.cons_update, Fin.cons_update]
      have h := ZCombLimit.fam_update_zcomb_int hI hP _ (hcons L hL) a.succ hM hH (q : ℤ) (p : ℤ)
      simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := J) (P := P) IsSmoothHerm e Z ![(q : ℝ), (p : ℝ)] he hZ
      hposition Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    have hl : (fun j : Fin (n + 1) => if (j : ℕ) = 0 then M else Z) =
        Fin.cons (α := fun _ => HermLine ι) M (fun _ : Fin n => Z) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp
    rw [hl, show I P (n + 1) (Fin.cons (α := fun _ => HermLine ι) M (fun _ : Fin n => Z)) =
      J P n (fun _ => Z) from rfl, key,
      ZCombExpand.famExt_expand e (ZCombExpand.famExt_symm_of e he hsymm), Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hl2 : (Fin.cons (α := fun _ => HermLine ι) M
        (fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1) : Fin (n + 1) → HermLine ι) =
        fun j : Fin (n + 1) => if (j : ℕ) < n + 1 - i then M else H := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero]
        exact (if_pos (show ((0 : Fin (n + 1)) : ℕ) < n + 1 - i by simp; omega)).symm
      · simp only [Fin.cons_succ, Fin.val_succ]
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd (by omega) h2
        · exact absurd (by omega) h1
        · rfl
    show _ * I P (n + 1) _ = _
    rw [hl2]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
