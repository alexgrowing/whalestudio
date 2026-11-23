import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ReadLimit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PInfConv

noncomputable section

open Polynomial Finset Filter Topology
open scoped Classical
open PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.CG.InfiniteConvergence

namespace PositivityTheory.Rg.BcB.F.Rd.B

theorem gelfVal_cont (n l : ℕ) : Continuous fun χ : Fin n → ℂ => GlobalTheory.Dec.gelfVal χ l := by
  unfold GlobalTheory.Dec.gelfVal
  have hA : Continuous fun χ : Fin n → ℂ => Formalism.REAL.Amat (fun c => χ c + ((n : ℂ) - 1) / 2) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Formalism.REAL.Amat, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply a).add continuous_const
    · exact continuous_const
    · exact continuous_const
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => (hA.pow l).matrix_elem a b

theorem coef_conv (m : ℕ) (x : ℕ → Fin (m + 1) → ℂ) (t : ℕ → ℂ)
    (ht : ∀ l, Tendsto (fun k => GlobalTheory.Dec.gelfVal (x k) l) atTop (𝓝 (t l))) :
    ∀ i, ∃ c, Tendsto (fun k => (cq m (x k)).coeff i) atTop (𝓝 c) := by
  have hind : ∀ j i, m + 1 - j ≤ i → ∃ c, Tendsto (fun k => (cq m (x k)).coeff i) atTop (𝓝 c) := by
    intro j
    induction j with
    | zero =>
      intro i hi
      rcases eq_or_lt_of_le (show m + 1 ≤ i by omega) with h | h
      · subst h
        have e : ∀ χ, (cq m χ).coeff (m + 1) = 1 := fun χ => by
          have := (cq_monic m χ).coeff_natDegree
          rwa [cq_natDegree] at this
        simp only [e]
        exact ⟨1, tendsto_const_nhds⟩
      · have e : ∀ χ, (cq m χ).coeff i = 0 := fun χ =>
          coeff_eq_zero_of_natDegree_lt (by rw [cq_natDegree]; exact h)
        simp only [e]
        exact ⟨0, tendsto_const_nhds⟩
    | succ j ih =>
      intro i hi
      by_cases hij : m + 1 - j ≤ i
      · exact ih i hij
      · have hr : i ≤ m := by omega
        have hij' : i + j = m := by omega
        have hne : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
        have hform : ∀ χ : Fin (m + 1) → ℂ, (cq m χ).coeff i =
            (defect (GlobalTheory.Dec.gelfVal χ) m (m + 1) (Hi i (m + 1) (cq m χ))).coeff (i + (m + 1)) / ((j : ℂ) + 1) := by
          intro χ
          have hk := key m χ i hr
          have hc : (i : ℂ) = (m : ℂ) - j := by rw [← hij']; push_cast; ring
          rw [eq_div_iff hne]
          linear_combination (-1 : ℂ) * hk + (cq m χ).coeff i * hc
        let c : ℕ → ℂ := fun l => if h : ∃ c, Tendsto (fun k => (cq m (x k)).coeff l) atTop (𝓝 c) then h.choose else 0
        have hc : ∀ l ∈ Ioc i (m + 1), Tendsto (fun k => (cq m (x k)).coeff l) atTop (𝓝 (c l)) := fun l hl => by
          have h := ih l (by simp only [mem_Ioc] at hl; omega)
          simp only [c, dif_pos h]
          exact h.choose_spec
        let Q₀ : ℂ[X] := ∑ l ∈ Ioc i (m + 1), Polynomial.C (c l) * X ^ l
        have h1 : CoefTo (fun k => Hi i (m + 1) (cq m (x k))) Q₀ := by
          simp only [Hi, Q₀]
          exact CoefTo.sum _ fun l hl => CoefTo.mul (CoefTo.C (hc l hl)) (CoefTo.const _)
        have hQc : Q₀.comp (X + 1) = ∑ l ∈ Ioc i (m + 1), Polynomial.C (c l) * (X + 1) ^ l := by
          simp only [Q₀]
          rw [← coe_compRingHom_apply, map_sum]
          simp only [coe_compRingHom_apply, mul_comp, C_comp, X_pow_comp]
        have h2 : CoefTo (fun k => (Hi i (m + 1) (cq m (x k))).comp (X + 1)) (Q₀.comp (X + 1)) := by
          simp only [Hi_comp, hQc]
          exact CoefTo.sum _ fun l hl => CoefTo.mul (CoefTo.C (hc l hl)) (CoefTo.const _)
        have h3 := CoefTo.defect (t := fun k => GlobalTheory.Dec.gelfVal (x k)) ht m (m + 1) h1 h2 (i + (m + 1))
        exact ⟨_, (h3.div_const ((j : ℂ) + 1)).congr fun k => (hform (x k)).symm⟩
  exact fun i => hind (m + 1) i (by omega)

theorem infLim : InfLim := by
  intro n x t ht
  rcases n with _ | m
  · have h0 : ∀ (χ : Fin 0 → ℂ) (l : ℕ), GlobalTheory.Dec.gelfVal χ l = 0 := fun χ l => by simp [GlobalTheory.Dec.gelfVal]
    refine ⟨Fin.elim0, fun l => ?_⟩
    have h := ht l
    simp only [h0] at h
    rw [h0]
    exact tendsto_nhds_unique tendsto_const_nhds h
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, ∀ i, Tendsto (fun k => (cq m (x k)).coeff i) atTop (𝓝 (c i)) := by
    choose c hc using coef_conv m x t ht
    exact ⟨c, hc⟩
  have hbd : ∀ i, ∃ B, ∀ k, ‖(cq m (x k)).coeff i‖ ≤ B := fun i => by
    obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ (hc i)).exists_norm_le
    exact ⟨B, fun k => hB _ ⟨k, rfl⟩⟩
  choose Cb hCb using hbd
  set B := max 1 (∑ i ∈ range (m + 1), Cb i) + ‖(m : ℂ) / 2‖ with hBdef
  have hB0 : 0 ≤ B := by
    have := le_max_left (1 : ℝ) (∑ i ∈ range (m + 1), Cb i)
    have := norm_nonneg ((m : ℂ) / 2)
    linarith
  have hxb : ∀ k s, ‖x k s‖ ≤ B := by
    intro k s
    have h1 := norm_root_le _ (cq_monic m (x k)) _ (cq_eval m (x k) s)
    rw [cq_natDegree] at h1
    have h2 : ∑ i ∈ range (m + 1), ‖(cq m (x k)).coeff i‖ ≤ ∑ i ∈ range (m + 1), Cb i :=
      sum_le_sum fun i _ => hCb i k
    have h3 : ‖x k s‖ ≤ ‖(m : ℂ) / 2‖ + ‖(m : ℂ) / 2 - x k s‖ := by
      have := norm_sub_le ((m : ℂ) / 2) ((m : ℂ) / 2 - x k s)
      rwa [sub_sub_cancel] at this
    have h4 := max_le_max (le_refl (1 : ℝ)) h2
    linarith
  have hmem : ∀ k, x k ∈ Metric.closedBall (0 : Fin (m + 1) → ℂ) B := fun k =>
    mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg hB0).2 fun s => hxb _ s)
  obtain ⟨z, -, ψ, hψm, hψ⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hmem
  refine ⟨z, fun l => ?_⟩
  have h1 : Tendsto (fun k => GlobalTheory.Dec.gelfVal (x (ψ k)) l) atTop (𝓝 (GlobalTheory.Dec.gelfVal z l)) :=
    ((gelfVal_cont (m + 1) l).tendsto z).comp hψ
  have h2 : Tendsto (fun k => GlobalTheory.Dec.gelfVal (x (ψ k)) l) atTop (𝓝 (t l)) :=
    (ht l).comp hψm.tendsto_atTop
  exact tendsto_nhds_unique h1 h2

end PositivityTheory.Rg.BcB.F.Rd.B

end
