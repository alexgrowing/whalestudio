import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSectionSmoothPolydiscStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

namespace GlobalTheory.PoincareLocal

open scoped Classical in

theorem sum_elim_eq_sum_branches {e m : ℕ} (σ : Fin m → Option (Fin e))
    (inj : ∀ i i' k, σ i = some k → σ i' = some k → i = i') (t : Fin e → ℝ) :
    (∑ i, Option.elim (σ i) 0 t) = ∑ k, if ∃ i, σ i = some k then t k else 0 := by
  have h1 : ∀ i, Option.elim (σ i) 0 t = ∑ k, if σ i = some k then t k else 0 := by
    intro i
    cases h : σ i with
    | none => simp
    | some k0 => simp [Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs with hk
  · obtain ⟨i0, hi0⟩ := hk
    rw [Finset.sum_eq_single i0]
    · simp [hi0]
    · intro b _ hb
      rw [if_neg]
      intro hbk
      exact hb (inj _ _ _ hbk hi0)
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    intro h
    exact hk ⟨i, h⟩

theorem rTot_comparable_tSum : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin m → Option (Fin e)),
    IsBoundary A L s D → IsAdaptedPolydisc A D ψ σ → ∃ C : ℝ, 0 < C ∧
      ∀ z ∈ Metric.ball (0 : Fin e → ℂ) (1 / 2), ψ.symm z ∉ ⋃ i, D i →
        C⁻¹ * tSum σ z ≤ rTot L s (ψ.symm z) ∧ rTot L s (ψ.symm z) ≤ C * tSum σ z := by
  intro e X _ A m L s D ψ σ hB hP
  have hfac := GlobalTheory.T.normal_section_smooth_polydisc A L s D ψ σ hB hP
  obtain ⟨_, _, hinj, hD⟩ := hP
  choose f hfs hfe using hfac
  have hK : IsCompact (Metric.closedBall (0 : Fin e → ℂ) (1 / 2)) := isCompact_closedBall _ _
  have hsub : Metric.closedBall (0 : Fin e → ℂ) (1 / 2) ⊆ Metric.ball 0 1 :=
    Metric.closedBall_subset_ball (by norm_num)
  have hbd : ∀ i, ∃ B, ∀ z ∈ Metric.closedBall (0 : Fin e → ℂ) (1 / 2), ‖f i z‖ ≤ B := fun i =>
    hK.exists_bound_of_continuousOn ((hfs i).continuousOn.mono hsub)
  choose B hBd using hbd
  set M := ∑ i, |B i| with hMdef
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpi := Real.pi_gt_three
  refine ⟨Real.exp 1 + M + 4 * Real.pi + 2, by linarith [Real.exp_pos 1, Real.pi_pos], ?_⟩
  intro z hz hnot
  have hzc : z ∈ Metric.closedBall (0 : Fin e → ℂ) (1 / 2) := Metric.ball_subset_closedBall hz
  have hz1 : z ∈ Metric.ball (0 : Fin e → ℂ) 1 := hsub hzc
  have hnD : ∀ i, ψ.symm z ∉ D i := fun i h => hnot (Set.mem_iUnion.2 ⟨i, h⟩)
  have hzk : ∀ i k, σ i = some k → z k ≠ 0 := fun i k h h0 => hnD i ((hD z hz1 i).2 ⟨k, h, h0⟩)
  have hne : ∀ i, normSec (L i) (s i) (ψ.symm z) ≠ 0 := by
    intro i h0
    have := hfe i z hz1
    rw [h0] at this
    cases h : σ i with
    | none =>
      simp [h] at this
      exact (Real.exp_pos _).ne' this.symm
    | some k =>
      have hk := hzk i k h
      simp [h, hk, Real.exp_ne_zero] at this
  have hlog : ∀ i, Real.log (normSec (L i) (s i) (ψ.symm z) ^ 2)
      = -(4 * Real.pi) * Option.elim (σ i) 0 (fun k => tOf (z k)) - f i z := by
    intro i
    rw [hfe i z hz1]
    cases h : σ i with
    | none => simp [Real.log_exp]
    | some k =>
      have hk := hzk i k h
      simp only [Option.elim]
      rw [Real.log_mul (pow_pos (norm_pos_iff.2 hk) 2).ne' (Real.exp_pos _).ne', Real.log_exp,
        Real.log_pow]
      unfold tOf
      push_cast
      field_simp
      ring
  have hr : rTot L s (ψ.symm z) = Real.exp 1
      + 4 * Real.pi * ∑ i, Option.elim (σ i) 0 (fun k => tOf (z k)) + ∑ i, f i z := by
    unfold rTot
    rw [← Finset.prod_pow, Real.log_prod (fun i _ => pow_ne_zero 2 (hne i))]
    simp only [hlog]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  have hts : tSum σ z = 1 + ∑ i, Option.elim (σ i) 0 (fun k => tOf (z k)) := by
    unfold tSum
    rw [sum_elim_eq_sum_branches σ hinj]
  have hT0 : 0 ≤ ∑ i, Option.elim (σ i) 0 (fun k => tOf (z k)) := by
    apply Finset.sum_nonneg
    intro i _
    cases σ i with
    | none => simp
    | some k =>
      simp only [Option.elim]
      unfold tOf
      apply div_nonneg _ (by positivity)
      rw [neg_nonneg]
      apply Real.log_nonpos (norm_nonneg _)
      rw [mem_ball_zero_iff] at hz1
      exact le_trans (norm_le_pi_norm z k) hz1.le
  have hF : |∑ i, f i z| ≤ M := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have := hBd i z hzc
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have hnn : ∀ i, 0 ≤ normSec (L i) (s i) (ψ.symm z) := fun i =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hge : Real.exp 1 ≤ rTot L s (ψ.symm z) := by
    unfold rTot
    have hp : 0 < ∏ i, normSec (L i) (s i) (ψ.symm z) :=
      Finset.prod_pos (fun i _ => lt_of_le_of_ne (hnn i) (hne i).symm)
    have hp1 : ∏ i, normSec (L i) (s i) (ψ.symm z) ≤ 1 :=
      Finset.prod_le_one (fun i _ => hnn i) (fun i _ => (hB i).2.2.2 _)
    have : Real.log ((∏ i, normSec (L i) (s i) (ψ.symm z)) ^ 2) ≤ 0 :=
      Real.log_nonpos (by positivity) (pow_le_one₀ hp.le hp1)
    linarith
  rw [hts]
  set T := ∑ i, Option.elim (σ i) 0 (fun k => tOf (z k))
  set R := rTot L s (ψ.symm z)
  set F := ∑ i, f i z
  have hF1 := (abs_le.1 hF).1
  have hF2 := (abs_le.1 hF).2
  constructor
  · rw [inv_mul_le_iff₀ (by linarith [Real.exp_pos 1, Real.pi_pos])]
    have h1 : T ≤ R + M := by nlinarith
    have h2 : M ≤ M * R := by nlinarith
    have h3 : 0 ≤ (Real.exp 1 + 4 * Real.pi) * R :=
      mul_nonneg (by positivity) (by linarith [Real.exp_pos 1])
    nlinarith
  · nlinarith [mul_nonneg hM hT0, mul_nonneg (Real.exp_pos 1).le hT0, mul_nonneg Real.pi_pos.le hT0]

end GlobalTheory.PoincareLocal
