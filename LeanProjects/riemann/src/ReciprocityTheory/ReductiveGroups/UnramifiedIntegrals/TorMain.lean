import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorTwo
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorLift
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorContr
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorClose

noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

variable {l : ℕ} [Fact l.Prime] {g2 g3 : ℂ_[l]}

theorem tor_nsmul_fix {A : Type*} [AddGroup A] (P : A) (N n : ℕ) (hNP : N • P = 0)
    (hn : n ≡ 1 [MOD N]) : n • P = P := by
  have h1 : n ≡ 1 [MOD addOrderOf P] := hn.of_dvd (addOrderOf_dvd_of_nsmul_eq_zero hNP)
  have h2 := nsmul_eq_nsmul_iff_modEq.mpr h1
  simpa using h2

theorem tor_norm_mult_lt (N : ℕ) (hN0 : 0 < N) : ‖((l ^ N.totient : ℕ) : ℂ_[l])‖ < 1 := by
  have hl : ‖(l : ℂ_[l])‖ < 1 := by
    rw [norm_l_Cl]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  rw [Nat.cast_pow, norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hl (Nat.totient_pos.mpr hN0).ne'

theorem tor_x_step (h : GoodPair l g2 g3) (P Q : (shortW g2 g3).toAffine.Point) (N : ℕ)
    (hN : ¬ l ∣ N) (hNP : N • P = 0) (h2 : P + P ≠ 0) (hD : InFormalGroupPoints (P - Q)) (n : ℕ)
    (hn : n ≡ 1 [MOD N]) : ‖px _ P - px _ (n • Q)‖ ≤ ‖uOf (n • (P - Q))‖ := by
  obtain ⟨hW, hΔ⟩ := good_model h
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact h2 (by simp)
  have hfix : n • P = P := tor_nsmul_fix P N n hNP hn
  have hsub : P - n • Q = n • (P - Q) := by
    rw [nsmul_sub, hfix]
  have hB : n • Q = P - n • (P - Q) := by
    rw [← hsub]; abel
  have hE : InFormalGroupPoints (n • (P - Q)) := (formalGroup_nsmul_estimate _ hW hΔ _ hD n).1
  by_cases h0 : n • (P - Q) = 0
  · have : n • Q = P := by rw [hB, h0, sub_zero]
    rw [this, sub_self, norm_zero]
    exact norm_nonneg _
  have hPE : ¬ InFormalGroupPoints P := torsion_not_mem_formalGroup h P N hN hNP hP0
  have hBE : ¬ InFormalGroupPoints (n • Q) := by
    rw [hB]; exact not_mem_formalGroup_sub h P _ hPE hE
  have h2E : ¬ InFormalGroupPoints (P + P) :=
    torsion_not_mem_formalGroup h (P + P) N hN (by rw [nsmul_add, hNP, add_zero]) h2
  have hS : P + n • Q = (P + P) - n • (P - Q) := by
    rw [hB]; abel
  have hSE : ¬ InFormalGroupPoints (P + n • Q) := by
    rw [hS]; exact not_mem_formalGroup_sub h _ _ h2E hE
  obtain ⟨_, _, hPy⟩ := integral_of_not_mem_formalGroup h P hPE
  obtain ⟨hB0, _, hBy⟩ := integral_of_not_mem_formalGroup h _ hBE
  obtain ⟨hS0, hSx, _⟩ := integral_of_not_mem_formalGroup h _ hSE
  have := norm_x_sub_le_of_formalGroup (shortW g2 g3) rfl rfl rfl hW P (n • Q) hP0 hB0 hPy hBy hS0 hSx
    (by rw [hsub]; exact h0) (by rw [hsub]; exact hE)
  rwa [hsub] at this

theorem tor_x_mem (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (N : ℕ) (hN0 : 0 < N)
    (hN : ¬ l ∣ N) (hNP : N • P = 0) (h2 : P + P ≠ 0) : px _ P ∈ MaximalUnramifiedExtension l := by
  obtain ⟨hW, hΔ⟩ := good_model h
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact h2 (by simp)
  have hPE : ¬ InFormalGroupPoints P := torsion_not_mem_formalGroup h P N hN hNP hP0
  obtain ⟨_, hPx, _⟩ := integral_of_not_mem_formalGroup h P hPE
  obtain ⟨Q, hQ, hD⟩ := tor_lift h P hP0 hPx (tor_y_unit h P N hN hNP h2)
  have hcop : Nat.Coprime l N := ((Fact.out : l.Prime).coprime_iff_not_dvd).mpr hN
  have hM : ∀ k : ℕ, (l ^ N.totient) ^ k ≡ 1 [MOD N] := fun k => by
    simpa using (Nat.ModEq.pow_totient hcop).pow k
  have ht := formalGroup_pow_tendsto_zero _ hW hΔ _ hD (l ^ N.totient) (tor_norm_mult_lt N hN0)
  have hlim : Filter.Tendsto (fun k : ℕ => px _ ((l ^ N.totient) ^ k • Q)) Filter.atTop
      (nhds (px _ P)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) ht
    rw [norm_sub_rev]
    exact tor_x_step h P Q N hN hNP h2 hD _ (hM k)
  have hcl : IsClosed ((MaximalUnramifiedExtension l : Subfield ℂ_[l]) : Set ℂ_[l]) :=
    Subfield.isClosed_topologicalClosure _
  refine hcl.mem_of_tendsto hlim (Filter.Eventually.of_forall fun k => ?_)
  exact (inSub_px _ _ _ (inSub_nsmul _ _ (good_coeff h) _ Q hQ)).1

theorem tor_kur (h : GoodPair l g2 g3) (P : (shortW g2 g3).toAffine.Point) (N : ℕ) (hN0 : 0 < N)
    (hN : ¬ l ∣ N) (hNP : N • P = 0) (hP0 : P ≠ 0) : px _ P ∈ MaximalUnramifiedExtension l ∧ py _ P ∈ MaximalUnramifiedExtension l := by
  by_cases h2 : P + P = 0
  · exact tor_two h P hP0 h2
  have hx := tor_x_mem h P N hN0 hN hNP h2
  have hy := tor_y_unit h P N hN hNP h2
  refine ⟨hx, ?_⟩
  have hl : l ≠ 2 := by have := h.five; omega
  have heq : (py _ P) ^ 2 = (px _ P) ^ 3 - g2 / 4 * px _ P - g3 / 4 := by
    match P, hP0 with
    | .zero, hP0 => exact absurd rfl hP0
    | .some x y hxy, _ =>
      have := (Affine.equation_iff _ _).mp hxy.1
      simp only [shortW, px, py] at this ⊢
      linear_combination this
  have h4 : (4 : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by exact_mod_cast natCast_mem (MaximalUnramifiedExtension l) 4
  refine sqrt_mem l hl _ _ ?_ hy heq
  exact sub_mem (sub_mem (pow_mem hx 3) (mul_mem (div_mem h.mem2 h4) hx)) (div_mem h.mem3 h4)

end ReciprocityTheory.ChartRestriction.L1
