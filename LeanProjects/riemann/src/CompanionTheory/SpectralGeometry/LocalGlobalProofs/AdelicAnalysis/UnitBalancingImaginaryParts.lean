import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.UnitBalance

open NumberField.Units NumberField.Units.dirichletUnitTheorem in

theorem exists_bound_log_centered (E : Type) [Field E] [NumberField E] :
    ∃ R : ℝ, ∀ t : InfinitePlace E → ℝ, ∃ (u : (𝓞 E)ˣ) (s : ℝ), ∀ w : InfinitePlace E,
      |t w + Real.log (w (u : E)) - s| ≤ R := by
  classical
  let B := (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E)
  obtain ⟨C, hC⟩ := (ZSpan.fundamentalDomain_isBounded B).exists_norm_le
  refine ⟨Fintype.card (InfinitePlace E) * |C|, fun t => ?_⟩
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  let s : ℝ := (∑ w : InfinitePlace E, (w.mult : ℝ) * t w) / Module.finrank ℚ E
  let l : logSpace E := fun w => (w.1.mult : ℝ) * (t w.1 - s)
  obtain ⟨⟨e, he⟩, h2, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B l
  rw [Module.Basis.ofZLatticeBasis_span ℝ (unitLattice E)] at he
  obtain ⟨u, -, rfl⟩ := he
  let a : InfinitePlace E → ℝ := fun w => (w.mult : ℝ) * (t w - s + Real.log (w (u.toMul : E)))
  have hsum : ∑ w, a w = 0 := by
    have h1 := sum_mult_mul_log (K := E) u.toMul
    have h3 : ∑ w : InfinitePlace E, (w.mult : ℝ) = Module.finrank ℚ E := by
      exact_mod_cast InfinitePlace.sum_mult_eq (K := E)
    simp only [a, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, h3, s]
    field_simp
    ring
  have ha : ∀ w, w ≠ w₀ → |a w| ≤ |C| := fun w hw => by
    have h4 := (norm_le_pi_norm _ (⟨w, hw⟩ : {w : InfinitePlace E // w ≠ w₀})).trans (hC _ h2)
    refine le_trans (le_of_eq ?_) (h4.trans (le_abs_self C))
    rw [Real.norm_eq_abs]
    congr 1
    change _ = (w.mult : ℝ) * Real.log (w (u.toMul : E)) + (w.mult : ℝ) * (t w - s)
    simp only [a]
    ring
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace E) := by exact_mod_cast Fintype.card_pos
  have ha' : ∀ w, |a w| ≤ Fintype.card (InfinitePlace E) * |C| := fun w => by
    by_cases hw : w = w₀
    · subst hw
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀), add_eq_zero_iff_eq_neg] at hsum
      rw [hsum, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ _ fun w hw => ha w (Finset.ne_of_mem_erase hw)).trans ?_
      rw [nsmul_eq_mul]
      gcongr
      exact Finset.card_le_univ _
    · exact (ha w hw).trans (le_mul_of_one_le_left (abs_nonneg C) hcard)
  refine ⟨u.toMul, s, fun w => ?_⟩
  have h5 : |t w - s + Real.log (w (u.toMul : E))| ≤ |a w| := by
    simp only [a]
    rw [abs_mul]
    refine le_mul_of_one_le_left (abs_nonneg _) ?_
    rw [Nat.abs_cast]
    exact_mod_cast w.mult_pos
  have h6 := h5.trans (ha' w)
  have h7 : t w + Real.log (w (u.toMul : E)) - s = t w - s + Real.log (w (u.toMul : E)) := by ring
  rw [h7]
  exact h6

theorem balance_by_units : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ ρ : InfinitePlace F → (F →+* ℝ), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) →
    ∃ κ : ℝ, 0 < κ ∧ ∀ y : InfinitePlace F → ℝ, (∀ w, 0 < y w) →
      ∃ u : (𝓞 F)ˣ, ∀ v w, κ * (ρ w ((u : 𝓞 F) : F) ^ 2 * y w) ≤ ρ v ((u : 𝓞 F) : F) ^ 2 * y v := by
  intro F _ _ _ ρ hρ
  obtain ⟨R, hR⟩ := exists_bound_log_centered F
  refine ⟨Real.exp (-(4 * R)), Real.exp_pos _, fun y hy => ?_⟩
  obtain ⟨u, s, hu⟩ := hR (fun w => Real.log (y w) / 2)
  refine ⟨u, fun v w => ?_⟩
  have hne : ((u : 𝓞 F) : F) ≠ 0 := NumberField.Units.coe_ne_zero u
  have hexp : ∀ w : InfinitePlace F, ρ w ((u : 𝓞 F) : F) ^ 2 * y w =
      Real.exp (2 * (Real.log (y w) / 2 + Real.log (w ((u : 𝓞 F) : F)))) := by
    intro w
    have habs : w ((u : 𝓞 F) : F) = |ρ w ((u : 𝓞 F) : F)| := by
      rw [← InfinitePlace.norm_embedding_eq, ← hρ, Complex.norm_real, Real.norm_eq_abs]
    have hpos : 0 < w ((u : 𝓞 F) : F) := w.pos_iff.2 hne
    have e1 : 2 * (Real.log (y w) / 2 + Real.log (w ((u : 𝓞 F) : F))) =
        Real.log (w ((u : 𝓞 F) : F)) + Real.log (w ((u : 𝓞 F) : F)) + Real.log (y w) := by ring
    rw [e1, Real.exp_add, Real.exp_add, Real.exp_log hpos, Real.exp_log (hy w), habs, ← sq, sq_abs]
  rw [hexp v, hexp w, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := abs_le.1 (hu v)
  have h2 := abs_le.1 (hu w)
  linarith [h1.1, h1.2, h2.1, h2.2]

end GlobalTheory.CompanionTheory.SW.UnitBalance
