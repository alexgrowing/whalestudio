import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetAllComponents

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

namespace GlobalTheory.NetMax

open GlobalTheory.NetMulti

theorem exists_net_all_components_max : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) [Fintype Comp] [Nonempty Comp] (Xx : Comp → DataX E r) (la : ∀ k, Wt (Xx k).Ψ r) (M w L : ℝ), 1 ≤ r → 1 ≤ L → 1 ≤ M → 0 < w → (∀ k, (∑ τ, (Xx k).spread (la k) τ) ≤ w) → (∀ k, ∀ v ∈ (Xx k).L', herm (Xx k).Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ (Xx k).Γ, (Xx k).χ (la k) γ = 1 ∧ ∀ τ : (Xx k).Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = (Xx k).flowMat v τ ((M : ℂ) * τ.1 b)) → Real.log (fdeg E) ≤ 2 * L → Real.log r ≤ L → Real.log M ≤ 30 * L → Real.log w ≤ 3 * L → Real.log (dE E) ≤ 4 * fdeg E * L → (∀ k, Real.log (1 + ∑ τ, ∑ i, |(la k τ i : ℝ)|) ≤ 3 * L ∧ Real.log (Xx k).NA ≤ 30 * fdeg E * L ∧ Real.log (Xx k).NC ≤ 30 * fdeg E * L ∧ Real.log (Xx k).g ≤ 30 * fdeg E * L) → Real.log (Fintype.card Comp) ≤ 41 * (fdeg E * r * L) ^ 2 → ∃ NN : Finset (FPt (fun k => (Xx k).toData)), NN.Nonempty ∧ (∀ P ∈ holSub (fun k => (Xx k).toData) la, ∃ p ∈ NN, supN (fun k => (Xx k).toData) la P ≤ 4 * ((fun k => (Xx k).toData) p.1).pnorm (la p.1) (P p.1) p.2) ∧ Real.log (16 * NN.card) ≤ 1041 * (fdeg E * r * L) ^ 3 := by
  classical
  intro E _ _ _ r Comp _ _ Xx la M w L hr hL hM hw hsp hT hfL hrL hML hwL hdL hk hC

  have hf1 : (1 : ℝ) ≤ fdeg E := by
    have h2 := GlobalTheory.BoundedBasis.finrank_eq_two_mul_fdeg (E := E)
    have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
    have : 1 ≤ fdeg E := by omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hA : 1 ≤ (fdeg E : ℝ) * r * L :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf1 hr1) hL

  have hnet : ∀ k, ∃ N : Finset (Frame (Xx k).Ψ r), N.Nonempty ∧ (∀ y ∈ N, y ∈ (Xx k).dom) ∧
      (∀ Q ∈ (Xx k).SS (la k), ∀ x ∈ (Xx k).dom, ∃ y ∈ N,
        (Xx k).pnorm (la k) Q x ≤ 4 * (Xx k).pnorm (la k) Q y) ∧
      Real.log (16 * N.card) ≤ 1000 * ((fdeg E : ℝ) * r * L) ^ 3 := by
    intro k
    have hex := GlobalTheory.exists_finite_net (Xx k) (la k) M w (by linarith) (hsp k) hw (hT k)
    dsimp only at hex
    obtain ⟨N, hne, hdom, hmax, -, hsz⟩ := hex
    refine ⟨N, hne, hdom, hmax, ?_⟩
    obtain ⟨hs, hNA, hNC, hg⟩ := hk k
    have hk0 : Real.log (Xx k).k0 ≤ 4 * L := by
      have h1 : Real.log (Xx k).k0 ≤ Real.log 2 := Real.log_le_log (Xx k).minWeight_pos (Xx k).k0_le
      have h2 := Real.log_two_lt_d9
      norm_num at h2
      linarith
    have hcub := GlobalTheory.NetSize.net_size_cubic (fdeg E) r L M w (Xx k).k0 (dE E)
      (∑ τ, ∑ i, |(la k τ i : ℝ)|) (Xx k).NA (Xx k).NC (Xx k).g hf1 hr1 hL hM hw (Xx k).minWeight_pos
      (GlobalTheory.NetMulti.one_le_absDisc E) (by positivity) (by exact_mod_cast (Xx k).NA_pos)
      (by exact_mod_cast (Xx k).NC_pos) (by exact_mod_cast (Xx k).g_pos) hfL hrL hML hwL hk0 hdL
      hs hNA hNC hg
    have hcard : (0 : ℝ) < N.card := by exact_mod_cast Finset.card_pos.2 hne
    rw [Real.log_mul (by norm_num) hcard.ne']
    linarith
  choose N hNne hNdom hNmax hNsz using hnet

  let NN : Finset (FPt (fun k => (Xx k).toData)) :=
    Finset.univ.sigma fun k => (N k).subtype fun y => y ∈ ((Xx k).dom : Set (Frame (Xx k).Ψ r))
  have hmemNN : ∀ k y (hy : y ∈ (Xx k).dom), y ∈ N k →
      (⟨k, ⟨y, hy⟩⟩ : FPt (fun k => (Xx k).toData)) ∈ NN := by
    intro k y hy hyN
    simp only [NN, Finset.mem_sigma, Finset.mem_univ, Finset.mem_subtype, true_and]
    exact hyN
  have hNNne : NN.Nonempty := by
    obtain ⟨k⟩ := (inferInstance : Nonempty Comp)
    obtain ⟨y, hy⟩ := hNne k
    exact ⟨_, hmemNN k y (hNdom k y hy) hy⟩
  refine ⟨NN, hNNne, ?_, ?_⟩
  ·
    intro P hP
    obtain ⟨p, hpNN, hpmax⟩ := NN.exists_max_image
      (fun q => ((Xx q.1).toData).pnorm (la q.1) (P q.1) q.2) hNNne
    refine ⟨p, hpNN, ?_⟩
    have hSS := GlobalTheory.NetMulti.component_mem_SS (fun k => (Xx k).toData) la hP
    have hp0 : 0 ≤ ((Xx p.1).toData).pnorm (la p.1) (P p.1) p.2 := by
      unfold Data.pnorm
      exact mul_nonneg (norm_nonneg _) (Formalism.L2.PjFree.pnorm_fac_nonneg _ _ _)
    unfold supN
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    unfold supE
    refine iSup_le fun q => ?_
    obtain ⟨k, x, hx⟩ := q
    obtain ⟨y, hy, hxy⟩ := hNmax k (P k) (hSS k) x hx
    have hle := hpmax _ (hmemNN k y (hNdom k y hy) hy)
    apply ENNReal.ofReal_le_ofReal
    simp only at hle hxy ⊢
    linarith
  ·
    have h2 : ∀ k, 16 * ((N k).card : ℝ) ≤ Real.exp (1000 * ((fdeg E : ℝ) * r * L) ^ 3) := by
      intro k
      have hc : (0 : ℝ) < (N k).card := by exact_mod_cast Finset.card_pos.2 (hNne k)
      exact (Real.log_le_iff_le_exp (by positivity)).1 (hNsz k)
    have h1 : (NN.card : ℝ) ≤ ∑ k : Comp, ((N k).card : ℝ) := by
      have : NN.card ≤ ∑ k : Comp, (N k).card := by
        simp only [NN, Finset.card_sigma]
        exact Finset.sum_le_sum fun k _ =>
          (Finset.card_subtype _ _).trans_le (Finset.card_filter_le _ _)
      exact_mod_cast this
    have hcardle : 16 * (NN.card : ℝ) ≤
        Fintype.card Comp * Real.exp (1000 * ((fdeg E : ℝ) * r * L) ^ 3) := by
      calc 16 * (NN.card : ℝ) ≤ 16 * ∑ k : Comp, ((N k).card : ℝ) := by linarith
        _ = ∑ k : Comp, 16 * ((N k).card : ℝ) := by rw [Finset.mul_sum]
        _ ≤ ∑ _k : Comp, Real.exp (1000 * ((fdeg E : ℝ) * r * L) ^ 3) :=
          Finset.sum_le_sum fun k _ => h2 k
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hNNpos : 0 < 16 * (NN.card : ℝ) := by
      have : (0 : ℝ) < NN.card := by exact_mod_cast Finset.card_pos.2 hNNne
      positivity
    have hCpos : (0 : ℝ) < Fintype.card Comp := by exact_mod_cast Fintype.card_pos
    set A := (fdeg E : ℝ) * r * L with hAdef
    have hA23 : A ^ 2 ≤ A ^ 3 := by nlinarith [sq_nonneg A, mul_nonneg (sq_nonneg A) (sub_nonneg.2 hA)]
    calc Real.log (16 * NN.card) ≤ Real.log (Fintype.card Comp * Real.exp (1000 * A ^ 3)) :=
          Real.log_le_log hNNpos hcardle
      _ = Real.log (Fintype.card Comp) + 1000 * A ^ 3 := by
          rw [Real.log_mul hCpos.ne' (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ 1041 * A ^ 3 := by linarith

end GlobalTheory.NetMax
