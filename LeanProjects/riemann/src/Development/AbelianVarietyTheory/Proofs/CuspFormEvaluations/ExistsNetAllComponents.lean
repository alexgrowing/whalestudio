import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetOfThickPoints
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NetSizeCubic

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

namespace GlobalTheory.NetMulti

theorem component_mem_SS {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r) {P : FDSec X} (h : P ∈ holSub X la) :
    ∀ k, P k ∈ (X k).SS (la k) := by
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy =>
    exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.1 _ (hx k) _ (hy k)
  | smul a x _ hx => exact fun k => (siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0).1.2.2 a _ (hx k)

theorem one_le_absDisc (E : Type) [Field E] [NumberField E] [IsCMField E] : 1 ≤ dE E := by
  have h : (1 : ℤ) ≤ |discr E| := Int.one_le_abs (discr_ne_zero E)
  unfold dE
  exact_mod_cast h

theorem exists_net_all_components : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) [Fintype Comp] [Nonempty Comp] (Xx : Comp → DataX E r) (la : ∀ k, Wt (Xx k).Ψ r) (M w L : ℝ), 1 ≤ r → 1 ≤ L → 1 ≤ M → 0 < w → (∀ k, (∑ τ, (Xx k).spread (la k) τ) ≤ w) → (∀ k, ∀ v ∈ (Xx k).L', herm (Xx k).Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b → ∃ γ ∈ (Xx k).Γ, (Xx k).χ (la k) γ = 1 ∧ ∀ τ : (Xx k).Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = (Xx k).flowMat v τ ((M : ℂ) * τ.1 b)) → Real.log (fdeg E) ≤ 2 * L → Real.log r ≤ L → Real.log M ≤ 30 * L → Real.log w ≤ 3 * L → Real.log (dE E) ≤ 4 * fdeg E * L → (∀ k, Real.log (1 + ∑ τ, ∑ i, |(la k τ i : ℝ)|) ≤ 3 * L ∧ Real.log (Xx k).NA ≤ 30 * fdeg E * L ∧ Real.log (Xx k).NC ≤ 30 * fdeg E * L ∧ Real.log (Xx k).g ≤ 30 * fdeg E * L) → Real.log (Fintype.card Comp) ≤ 41 * (fdeg E * r * L) ^ 2 → ∃ NN : Finset (FPt (fun k => (Xx k).toData)), NN.Nonempty ∧ (∀ P ∈ holSub (fun k => (Xx k).toData) la, supN (fun k => (Xx k).toData) la P ≤ 4 * Real.sqrt NN.card * Real.sqrt ((NN.card : ℝ)⁻¹ * ∑ p ∈ NN, (((fun k => (Xx k).toData) p.1).pnorm (la p.1) (P p.1) p.2) ^ 2)) ∧ Real.log (16 * NN.card) ≤ 1041 * (fdeg E * r * L) ^ 3 := by
  intro E _ _ _ r Comp _ _ Xx la M w L hr hL hM hw hsp hT lf lr lM lw ld lk lC
  classical
  have hf : (1 : ℝ) ≤ fdeg E := one_le_field_half_degree
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hnet := fun k => GlobalTheory.exists_finite_net (Xx k) (la k) M w (by linarith) (hsp k) hw (hT k)
  choose N hN₁ hN₂ hN₃ _ hN₄ using hnet
  set Z : ℝ := fdeg E * r * L with hZ
  have hZ1 : 1 ≤ Z := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hr1) hL
  have hcard : ∀ k, 16 * ((N k).card : ℝ) ≤ Real.exp (1000 * Z ^ 3) := by
    intro k
    have hpos : (0 : ℝ) < (N k).card := by exact_mod_cast (hN₁ k).card_pos
    have hk0 : Real.log (Xx k).k0 ≤ 4 * L := by
      have := Real.log_le_sub_one_of_pos (Xx k).minWeight_pos
      linarith [(Xx k).k0_le]
    have h := GlobalTheory.NetSize.net_size_cubic (fdeg E) r L M w (Xx k).k0 (dE E)
      (∑ τ, ∑ i, |(la k τ i : ℝ)|) (Xx k).NA (Xx k).NC (Xx k).g hf hr1 hL hM hw (Xx k).minWeight_pos
      (one_le_absDisc E) (by positivity) (by exact_mod_cast (Xx k).NA_pos)
      (by exact_mod_cast (Xx k).NC_pos) (by exact_mod_cast (Xx k).g_pos) lf lr lM lw hk0 ld
      (lk k).1 (lk k).2.1 (lk k).2.2.1 (lk k).2.2.2
    rw [← Real.log_le_iff_le_exp (by positivity), Real.log_mul (by norm_num) hpos.ne']
    linarith [hN₄ k]
  let NN : Finset (FPt (fun k => (Xx k).toData)) :=
    Finset.univ.sigma fun k => (N k).subtype (· ∈ (Xx k).dom)
  have hmem : ∀ k, ∀ y (hy : y ∈ N k), (⟨k, ⟨y, hN₂ k y hy⟩⟩ : FPt (fun k => (Xx k).toData)) ∈ NN :=
    fun k y hy => Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_subtype.2 hy⟩
  have hne : NN.Nonempty := by
    obtain ⟨k⟩ := ‹Nonempty Comp›
    obtain ⟨y, hy⟩ := hN₁ k
    exact ⟨_, hmem k y hy⟩
  have hpos : (0 : ℝ) < NN.card := by exact_mod_cast hne.card_pos
  refine ⟨NN, hne, fun P hP => ?_, ?_⟩
  · set S : ℝ := ∑ p ∈ NN, (((fun k => (Xx k).toData) p.1).pnorm (la p.1) (P p.1) p.2) ^ 2 with hS
    have e : 4 * Real.sqrt NN.card * Real.sqrt ((NN.card : ℝ)⁻¹ * S) = 4 * Real.sqrt S := by
      rw [mul_assoc, ← Real.sqrt_mul hpos.le, mul_inv_cancel_left₀ hpos.ne']
    rw [e]
    unfold supN supE
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (iSup_le fun p => ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨y, hy, h⟩ := hN₃ p.1 (P p.1) (component_mem_SS _ la hP p.1) p.2 p.2.2
    refine h.trans (mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le ?_) (by norm_num))
    exact Finset.single_le_sum
      (f := fun p : FPt (fun k => (Xx k).toData) =>
        (((fun k => (Xx k).toData) p.1).pnorm (la p.1) (P p.1) p.2) ^ 2)
      (fun _ _ => sq_nonneg _) (hmem p.1 y hy)
  · have h1 : (NN.card : ℝ) ≤ ∑ k, ((N k).card : ℝ) := by
      rw [Finset.card_sigma]
      push_cast
      refine Finset.sum_le_sum fun k _ => ?_
      rw [Finset.card_subtype]
      exact_mod_cast Finset.card_filter_le _ _
    have hC : (0 : ℝ) < Fintype.card Comp := by exact_mod_cast Fintype.card_pos
    have h2 : 16 * (NN.card : ℝ) ≤ Fintype.card Comp * Real.exp (1000 * Z ^ 3) := by
      calc 16 * (NN.card : ℝ) ≤ ∑ k, 16 * ((N k).card : ℝ) := by
            rw [← Finset.mul_sum]; linarith
        _ ≤ ∑ _k : Comp, Real.exp (1000 * Z ^ 3) := Finset.sum_le_sum fun k _ => hcard k
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at h3
    have h4 : Z ^ 2 ≤ Z ^ 3 := pow_le_pow_right₀ hZ1 (by norm_num)
    linarith

end GlobalTheory.NetMulti
