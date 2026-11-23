import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

theorem locDens_expand_ofFun : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → ∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, locDens A (fun i => P i + LocPot.ofFun (f i)) j y = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y := by
  intro e X _ A U P f Θ hU hPot hΘ hf j y hy
  classical
  unfold ReciprocityTheory.AnForm.M.IsPotential at hPot hΘ
  have smooth_at : ∀ (g : X → ℝ) (W : Set X), IsOpen W → A.SmoothOn W g →
      y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W →
      ContDiffAt ℝ 2 (fun y' => g ((A.chart j).symm y')) y := by
    intro g W hW hg hyW
    have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
      (A.chart j).isOpen_inter_preimage_symm hW
    have h1 := (hg j).contDiffAt (hopen.mem_nhds hyW)
    exact h1.of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) | decide | simp)
  have hsP : ∀ k, ContDiffAt ℝ 2
      (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := fun k =>
    smooth_at ((P k).φ ((A.chart j).symm y)) ((P k).U ((A.chart j).symm y)) ((P k).isOpen_U _)
      ((hPot k).1 _) ⟨hy.1, (P k).mem_U _⟩
  have hsf : ∀ k, ContDiffAt ℝ 2 (fun y' => f k ((A.chart j).symm y')) y := fun k =>
    smooth_at (f k) U hU (hf k) hy
  have hsΘ : ContDiffAt ℝ 2 (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y :=
    smooth_at (Θ.φ ((A.chart j).symm y)) (Θ.U ((A.chart j).symm y)) (Θ.isOpen_U _)
      (hΘ.1 _) ⟨hy.1, Θ.mem_U _⟩
  have hessAdd : ∀ φ ψ : (Fin e → ℂ) → ℝ, ContDiffAt ℝ 2 φ y → ContDiffAt ℝ 2 ψ y →
      hessC (fun w => φ w + ψ w) y = hessC φ y + hessC ψ y := by
    intro φ ψ hφ hψ
    have hev : ∀ χ : (Fin e → ℂ) → ℝ, ContDiffAt ℝ 2 χ y → ∀ᶠ w in 𝓝 y, DifferentiableAt ℝ χ w := by
      intro χ hχ
      obtain ⟨f', u, hu, -, hder⟩ :=
        contDiffAt_one_iff.1 (hχ.of_le (by first | norm_num | exact one_le_two))
      exact Filter.mem_of_superset hu fun w hw => (hder w hw).differentiableAt
    have hd2 : ∀ χ : (Fin e → ℂ) → ℝ, ContDiffAt ℝ 2 χ y → DifferentiableAt ℝ (fderiv ℝ χ) y := by
      intro χ hχ
      exact (hχ.fderiv_right (m := 1) (by first | norm_num | exact le_of_eq one_add_one_eq_two)).differentiableAt one_ne_zero
    have hfd : fderiv ℝ (fun w => φ w + ψ w) =ᶠ[𝓝 y] fun w => fderiv ℝ φ w + fderiv ℝ ψ w := by
      filter_upwards [hev φ hφ, hev ψ hψ] with w h1 h2
      exact fderiv_add h1 h2
    have h2 : fderiv ℝ (fderiv ℝ (fun w => φ w + ψ w)) y =
        fderiv ℝ (fderiv ℝ φ) y + fderiv ℝ (fderiv ℝ ψ) y := by
      rw [hfd.fderiv_eq]
      exact fderiv_add (hd2 φ hφ) (hd2 ψ hψ)
    ext a b
    simp only [ReciprocityTheory.AnForm.hessC, h2, Matrix.add_apply, ContinuousLinearMap.add_apply,
      Complex.ofReal_add, Complex.ofReal_sub]
    ring
  have hL : ∀ k, hessC (fun y' => (P k + LocPot.ofFun (f k)).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y +
        hessC (fun y' => f k ((A.chart j).symm y')) y := fun k =>
    hessAdd (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y'))
      (fun y' => f k ((A.chart j).symm y')) (hsP k) (hsf k)
  have hR : ∀ (T : Finset (Fin e)) (k : Fin e),
      hessC (fun y' => ((if k ∈ T then P k else LocPot.ofFun 0) + LocPot.ofFun (if k ∈ T then f k else 0) + Θ).φ
        ((A.chart j).symm y) ((A.chart j).symm y')) y =
        if k ∈ T then hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y +
            hessC (fun y' => f k ((A.chart j).symm y')) y +
            hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y
        else hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    intro T k
    by_cases hk : k ∈ T
    · simp only [hk, ↓reduceIte]
      rw [← hL k]
      exact hessAdd (fun y' => (P k + LocPot.ofFun (f k)).φ ((A.chart j).symm y) ((A.chart j).symm y'))
        (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) ((hsP k).add (hsf k)) hsΘ
    · simp only [hk, ↓reduceIte]
      congr 1
      funext y'
      show (0 : X → ℝ) ((A.chart j).symm y') + (0 : X → ℝ) ((A.chart j).symm y') +
          Θ.φ ((A.chart j).symm y) ((A.chart j).symm y') = Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')
      simp
  have hPE : ∀ x z : Fin e → ℂ, ∑ T : Finset (Fin e), (-1 : ℂ) ^ (e - T.card) *
      ∏ k, (if k ∈ T then x k + z k else z k) = ∏ k, x k := by
    intro x z
    have hadd := Finset.prod_add (fun k => x k + z k) (fun k => -z k) (Finset.univ : Finset (Fin e))
    simp only [add_neg_cancel_right, Finset.powerset_univ] at hadd
    rw [hadd]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_neg, Finset.card_univ_diff, Fintype.card_fin]
    rw [show (∏ k, if k ∈ T then x k + z k else z k) = ∏ k, T.piecewise (fun k => x k + z k) z k from rfl,
      Finset.prod_piecewise, Finset.univ_inter]
    ring
  have hK : ∀ c : Fin e → Fin e, ∑ S : Finset (Fin e), (-1 : ℂ) ^ (e - S.card) *
      (if ∀ i, c i ∈ S then (1 : ℂ) else 0) = if Function.Surjective c then 1 else 0 := by
    intro c
    have hterm : ∀ S : Finset (Fin e), (if ∀ i, c i ∈ S then (1 : ℂ) else 0) =
        ∏ k, (if k ∈ S then (if k ∈ Set.range c then (1 : ℂ) else 0) + (if k ∈ Set.range c then 0 else 1)
          else (if k ∈ Set.range c then 0 else 1)) := by
      intro S
      by_cases h : ∀ i, c i ∈ S
      · rw [if_pos h]
        symm
        refine Finset.prod_eq_one fun k _ => ?_
        by_cases hkS : k ∈ S
        · rw [if_pos hkS]
          split_ifs <;> simp
        · have hkr : k ∉ Set.range c := by
            rintro ⟨i, rfl⟩
            exact hkS (h i)
          rw [if_neg hkS, if_neg hkr]
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        rw [if_neg (fun h' => hi (h' i))]
        symm
        refine Finset.prod_eq_zero (Finset.mem_univ (c i)) ?_
        rw [if_neg hi, if_pos (Set.mem_range_self i)]
    simp only [hterm]
    rw [hPE, Finset.prod_boole]
    by_cases hs : Function.Surjective c
    · rw [if_pos hs, if_pos (show ∀ i ∈ Finset.univ, i ∈ Set.range c from fun k _ => hs k)]
    · rw [if_neg hs, if_neg (show ¬ ∀ i ∈ Finset.univ, i ∈ Set.range c from fun h => hs fun k => h k (Finset.mem_univ k))]
  have hE : ∀ B : Fin e → Matrix (Fin e) (Fin e) ℂ,
      ∑ S : Finset (Fin e), (-1 : ℂ) ^ (e - S.card) * (∑ k ∈ S, B k).det =
        ∑ σ : Equiv.Perm (Fin e), ∑ c : Fin e → Fin e,
          (if Function.Surjective c then (1 : ℂ) else 0) *
            (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, B (c i) (σ i) i) := by
    intro B
    have h1 : ∀ S : Finset (Fin e), (∑ k ∈ S, B k).det = ∑ σ : Equiv.Perm (Fin e), ∑ c : Fin e → Fin e,
        (if ∀ i, c i ∈ S then (1 : ℂ) else 0) * (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, B (c i) (σ i) i) := by
      intro S
      rw [Matrix.det_apply']
      refine Finset.sum_congr rfl fun σ _ => ?_
      have hs : ∀ i, (∑ k ∈ S, B k) (σ i) i = ∑ k, if k ∈ S then B k (σ i) i else 0 := by
        intro i
        rw [Matrix.sum_apply, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
      simp only [hs]
      rw [Fintype.prod_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases h : ∀ i, c i ∈ S
      · rw [if_pos h, one_mul, Finset.prod_congr rfl fun i _ => if_pos (h i)]
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        rw [if_neg (fun h' => hi (h' i)), zero_mul, Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi),
          mul_zero]
    simp only [h1, Finset.mul_sum]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin e))))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin e))))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hK c, Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  have hT : ∀ (B : Fin e → Matrix (Fin e) (Fin e) ℂ) (C : Matrix (Fin e) (Fin e) ℂ)
      (σ : Equiv.Perm (Fin e)) (c : Fin e → Fin e), Function.Surjective c →
      ∑ T : Finset (Fin e), (-1 : ℂ) ^ (e - T.card) * ∏ i, (if c i ∈ T then B (c i) + C else C) (σ i) i =
        ∏ i, B (c i) (σ i) i := by
    intro B C σ c hc
    obtain ⟨E, rfl⟩ : ∃ E : Fin e ≃ Fin e, ⇑E = c :=
      ⟨Equiv.ofBijective c ⟨Finite.injective_iff_surjective.2 hc, hc⟩, rfl⟩
    have hre : ∀ T : Finset (Fin e), ∏ i, (if E i ∈ T then B (E i) + C else C) (σ i) i =
        ∏ k, (if k ∈ T then B k (σ (E.symm k)) (E.symm k) + C (σ (E.symm k)) (E.symm k)
          else C (σ (E.symm k)) (E.symm k)) := by
      intro T
      refine Fintype.prod_equiv E _ _ fun i => ?_
      simp only [Equiv.symm_apply_apply]
      split_ifs <;> rfl
    simp only [hre]
    rw [hPE]
    exact (Fintype.prod_equiv E _ _ fun i => by simp only [Equiv.symm_apply_apply]).symm
  have hKey : ∀ (B : Fin e → Matrix (Fin e) (Fin e) ℂ) (C : Matrix (Fin e) (Fin e) ℂ),
      mdisc B = ∑ T : Finset (Fin e), (-1 : ℂ) ^ (e - T.card) *
        mdisc (fun k => if k ∈ T then B k + C else C) := by
    intro B C
    unfold ReciprocityTheory.AnForm.mdisc
    simp only [hE]
    have hterm : ∀ (σ : Equiv.Perm (Fin e)) (c : Fin e → Fin e),
        (if Function.Surjective c then (1 : ℂ) else 0) * (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, B (c i) (σ i) i) =
          ∑ T : Finset (Fin e), (-1 : ℂ) ^ (e - T.card) * ((if Function.Surjective c then (1 : ℂ) else 0) *
            (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, (if c i ∈ T then B (c i) + C else C) (σ i) i)) := by
      intro σ c
      by_cases hc : Function.Surjective c
      · rw [if_pos hc, ← hT B C σ c hc, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        ring
      · simp only [if_neg hc, zero_mul, mul_zero, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun c _ => hterm σ c]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin e))))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Finset (Fin e))))]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun T _ => ?_
    ring
  unfold ReciprocityTheory.AnForm.M.locDens ReciprocityTheory.AnForm.maDens
  simp only [hL, hR]
  rw [hKey (fun k => hessC (fun y' => (P k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y +
      hessC (fun y' => f k ((A.chart j).symm y')) y)
    (hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y)]
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [show ((-1 : ℂ) ^ (e - T.card)) = (((-1 : ℝ) ^ (e - T.card) : ℝ) : ℂ) by norm_num,
    Complex.re_ofReal_mul]
  ring

end

end GlobalTheory.CompanionTheory.Ar.Giv
