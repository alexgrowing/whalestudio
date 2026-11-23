import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.ChamberInd

variable {m : ℕ}

def nrm (χ : Fin m → ℂˣ) : Fin m → ℝ := fun i => ‖(χ i : ℂ)‖

def wt (a : Fin m → ℝ) : ℝ := ∑ i : Fin m, ((m : ℝ) - (i.val : ℝ)) * Real.log (a i)

theorem nrm_pos (χ : Fin m → ℂˣ) (i : Fin m) : 0 < nrm χ i := by
  exact norm_pos_iff.mpr (Units.ne_zero _)

theorem wt_swap_gt (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) (i j : Fin m) (hij : i.val + 1 = j.val)
    (hlt : a i < a j) : wt a < wt (a ∘ Equiv.swap i j) := by
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have hsub : wt (a ∘ Equiv.swap i j) - wt a =
      ((m : ℝ) - (i.val : ℝ)) * (Real.log (a j) - Real.log (a i)) +
        ((m : ℝ) - (j.val : ℝ)) * (Real.log (a i) - Real.log (a j)) := by
    unfold wt
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_add i j hne (fun k hk => by
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hk.1 hk.2, sub_self])]
    simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
  have hj : (j.val : ℝ) = (i.val : ℝ) + 1 := by
    rw [← hij]
    push_cast
    ring
  have hlog : Real.log (a i) < Real.log (a j) := Real.log_lt_log (ha i) hlt
  have hd : wt (a ∘ Equiv.swap i j) - wt a = Real.log (a j) - Real.log (a i) := by
    rw [hsub, hj]
    ring
  linarith

theorem wt_update_gt (χ : Fin m → ℂˣ) (j : Fin m) (hj : j.val + 1 = m) (hlt : ‖(χ j : ℂ)‖ < 1) :
    wt (nrm χ) < wt (nrm (Function.update χ j (χ j)⁻¹)) := by
  have hpos : 0 < ‖(χ j : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have hn : nrm (Function.update χ j (χ j)⁻¹) = Function.update (nrm χ) j (‖(χ j : ℂ)‖⁻¹) := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp [nrm]
    · simp [nrm, Function.update_of_ne hk]
  rw [hn]
  have hdiff : wt (Function.update (nrm χ) j ‖(χ j : ℂ)‖⁻¹) - wt (nrm χ) =
      ((m : ℝ) - (j.val : ℝ)) * (Real.log ‖(χ j : ℂ)‖⁻¹ - Real.log (nrm χ j)) := by
    unfold wt
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_single j (fun k hk => by
      simp only [Function.update_of_ne hk, sub_self])]
    simp only [Function.update_self]
    ring
  have hm : (m : ℝ) - (j.val : ℝ) = 1 := by
    have hj' : (j.val : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hj
    linarith
  have hlog : Real.log ‖(χ j : ℂ)‖ < 0 := Real.log_neg hpos hlt
  have e : nrm χ j = ‖(χ j : ℂ)‖ := rfl
  rw [Real.log_inv, hm, e] at hdiff
  linarith

theorem weylConj_swap {α χ : Fin m → ℂˣ} (h : GlobalTheory.LGrp.WeylConjU α χ) (i j : Fin m) :
    GlobalTheory.LGrp.WeylConjU α (χ ∘ Equiv.swap i j) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨(Equiv.swap i j).trans w, fun k => hw _⟩

theorem weylConj_update {α χ : Fin m → ℂˣ} (h : GlobalTheory.LGrp.WeylConjU α χ) (j : Fin m) :
    GlobalTheory.LGrp.WeylConjU α (Function.update χ j (χ j)⁻¹) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, fun k => ?_⟩
  by_cases hk : k = j
  · subst hk
    rw [Function.update_self]
    rcases hw k with h | h
    · right
      rw [h]
    · left
      rw [h, inv_inv]
  · rw [Function.update_of_ne hk]
    exact hw k

theorem finite_nrm (α : Fin m → ℂˣ) (T : Set (Fin m → ℂˣ)) (hT : ∀ β ∈ T, GlobalTheory.LGrp.WeylConjU α β) :
    (nrm '' T).Finite := by
  classical
  let S : Set ℝ := (Set.range fun k => ‖(α k : ℂ)‖) ∪ Set.range fun k => ‖(((α k)⁻¹ : ℂˣ) : ℂ)‖
  have hS : S.Finite := (Set.finite_range _).union (Set.finite_range _)
  refine (Set.Finite.pi (t := fun _ : Fin m => S) (fun _ => hS)).subset ?_
  rintro _ ⟨β, hβ, rfl⟩
  rw [Set.mem_univ_pi]
  intro i
  obtain ⟨w, hw⟩ := hT β hβ
  rcases hw i with h | h
  · exact Or.inl ⟨w i, by simp only [nrm, h]⟩
  · exact Or.inr ⟨w i, by simp only [nrm, h]⟩

theorem exists_chamber (P : (Fin m → ℂˣ) → Prop)
    (hs : ∀ (χ : Fin m → ℂˣ) (i j : Fin m), i.val + 1 = j.val → ‖(χ i : ℂ)‖ < ‖(χ j : ℂ)‖ → P χ →
      P (χ ∘ Equiv.swap i j))
    (hv : ∀ (χ : Fin m → ℂˣ) (j : Fin m), j.val + 1 = m → ‖(χ j : ℂ)‖ < 1 → P χ →
      P (Function.update χ j (χ j)⁻¹))
    (α χ : Fin m → ℂˣ) (hα : GlobalTheory.LGrp.WeylConjU α χ) (hχ : P χ) :
    ∃ β : Fin m → ℂˣ, GlobalTheory.LGrp.WeylConjU α β ∧ (∀ i j : Fin m, i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖) ∧
      (∀ i, 1 ≤ ‖(β i : ℂ)‖) ∧ P β := by
  classical
  obtain ⟨T, hTdef⟩ : ∃ T : Set (Fin m → ℂˣ), T = {β | GlobalTheory.LGrp.WeylConjU α β ∧ P β} := ⟨_, rfl⟩
  have hfin : (nrm '' T).Finite := finite_nrm α T (fun β hβ => by rw [hTdef] at hβ; exact hβ.1)
  have hne : (nrm '' T).Nonempty := ⟨nrm χ, χ, by rw [hTdef]; exact ⟨hα, hχ⟩, rfl⟩
  obtain ⟨_, ⟨β, hβT, rfl⟩, hmax⟩ := Set.exists_max_image (nrm '' T) wt hfin hne
  rw [hTdef] at hβT
  obtain ⟨hβα, hβP⟩ := hβT
  have hmax' : ∀ γ : Fin m → ℂˣ, GlobalTheory.LGrp.WeylConjU α γ → P γ → wt (nrm γ) ≤ wt (nrm β) :=
    fun γ h1 h2 => hmax _ ⟨γ, by rw [hTdef]; exact ⟨h1, h2⟩, rfl⟩
  have hadj : ∀ i j : Fin m, i.val + 1 = j.val → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖ := by
    intro i j hij
    by_contra hcon
    rw [not_le] at hcon
    have h1 := hmax' _ (weylConj_swap hβα i j) (hs β i j hij hcon hβP)
    have h2 := wt_swap_gt (nrm β) (nrm_pos β) i j hij hcon
    exact absurd h1 (not_le.mpr h2)
  have key : ∀ d : ℕ, ∀ i j : Fin m, j.val = i.val + d → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖ := by
    intro d
    induction d with
    | zero =>
      intro i j h
      rw [show j = i from Fin.ext (by omega)]
    | succ d ih =>
      intro i j h
      have hk : i.val + d < m := by
        have := j.isLt
        omega
      exact le_trans (hadj ⟨i.val + d, hk⟩ j (by show i.val + d + 1 = j.val; omega))
        (ih i ⟨i.val + d, hk⟩ rfl)
  have hmono : ∀ i j : Fin m, i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖ := by
    intro i j hij
    have h' : i.val ≤ j.val := hij
    exact key (j.val - i.val) i j (by omega)
  have hone : ∀ i, 1 ≤ ‖(β i : ℂ)‖ := by
    intro i
    have hi := i.isLt
    have hlast : (⟨m - 1, by omega⟩ : Fin m).val + 1 = m := by
      show m - 1 + 1 = m
      omega
    have hl : 1 ≤ ‖(β ⟨m - 1, by omega⟩ : ℂ)‖ := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 := hmax' _ (weylConj_update hβα _) (hv β _ hlast hcon hβP)
      have h2 := wt_update_gt β _ hlast hcon
      exact absurd h1 (not_le.mpr h2)
    exact le_trans hl (hmono i _ (by show i.val ≤ m - 1; omega))
  exact ⟨β, hβα, hmono, hone, hβP⟩

theorem chamberU : PositivityTheory.SphericalProduct.ChamberU := by
  unfold ChamberU
  intro hsw hinv
  unfold SwapStepU at hsw
  unfold InvStepU at hinv
  intro L _ _ _ ϖ σ q n hU V _ _ ρ hadm hirr hsph α χ hα f hf hfeq
  obtain ⟨β, h1, h2, h3, hP⟩ := exists_chamber (m := n / 2)
    (fun χ => ∃ f : V →ₗ[ℂ] ↥(GlobalTheory.LFun.psSpaceU σ q χ), Function.Injective f ∧
      ∀ (g : ↥(Formalism.UG.GU σ n)) (v : V), f (ρ g v) = (GlobalTheory.LFun.psFunU σ q χ g) (f v))
    (fun χ i j hij hlt hP => by
      obtain ⟨f, hf, hfeq⟩ := hP
      exact hsw L ϖ σ q n hU V ρ hadm hirr hsph χ i j hij
        (by rw [norm_div, div_lt_one (norm_pos_iff.mpr (Units.ne_zero _))]; exact hlt) f hf hfeq)
    (fun χ j hj hlt hP => by
      obtain ⟨f, hf, hfeq⟩ := hP
      exact hinv L ϖ σ q n hU V ρ hadm hirr hsph χ j hj hlt f hf hfeq)
    α χ hα ⟨f, hf, hfeq⟩
  exact ⟨β, h1, h2, h3, hP⟩

end GlobalTheory.CompanionTheory.ChamberInd

end
