import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ExponentShiftEqLevelExponent

noncomputable section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem aStep_fin (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hT : TLeft) (hF : FormulaF) (hCH : CH) (k r' : ℕ) (hk : 1 ≤ k)
    (hA' : AAt k r') : AAt k (1 + r') := by
  intro s hs μG hμG A hA
  obtain ⟨hOSI, -, hHCL, hHI, -, -, hHGE, hHA, hGNL, hHC, hHCLM⟩ := heisenbergFacts_of_inductiveInput hB2
  obtain ⟨μ₁, hμ₁⟩ := hHGE k r'
  have : IsFiniteMeasureOnCompacts μ₁ := ⟨fun K hK => hμ₁.finite_compact K hK⟩
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : (0 : ℝ) ≤ r' := Nat.cast_nonneg r'
  have hs1 : SAdm k r' (fun l => s (sc r' l)) := fun l => by
    have h := hs (sc r' l)
    have e : s0 k (1 + r') (sc r' l) = s0 k r' l := by
      unfold s0 sc; split_ifs <;> first | rfl | (exfalso; simp_all; omega)
    rw [e] at h; exact h
  have hAB : AB k r' ≤ A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ) := by
    unfold AB at hA ⊢; push_cast at hA ⊢; nlinarith
  have hdA : ((4 * r' + 2 * k + 3 : ℕ) : ℝ) < A := by
    unfold AB at hA; push_cast at hA ⊢; nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hr0]
  have hJ1 := hA' _ hs1 μ₁ hμ₁ _ hAB
  obtain ⟨J1, hJ1d⟩ : ∃ J1, J1 = JInt μ₁ (A - ((4 * r' + 2 * k + 3 : ℕ) : ℝ)) (fun l => s (sc r' l)) := ⟨_, rfl⟩
  rw [← hJ1d] at hJ1
  obtain ⟨C0, hC0⟩ := eInt_bound hGNL hHA hHC hHCL hHCLM k r' hk A hdA
  obtain ⟨C, -, hOS⟩ := hOSI k r' μG μ₁ hμG hμ₁
  have hfm : Measurable (fun g : Mt k (1 + r') =>
      ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k (1 + r') s (Matrix.of g)) :=
    ((by unfold gN; fun_prop : Continuous fun g : Mt k (1 + r') => gN (Matrix.of g)).measurable.pow_const
      _).ennreal_ofReal.mul (FsE_meas k (1 + r') s)
  unfold JInt
  rw [hOS _ hfm]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  obtain ⟨aw, haw⟩ : ∃ aw : ℝ, aw = 2 * ((2 * r' + k + 1 : ℕ) : ℝ) - ∑ l, s l := ⟨_, rfl⟩
  have hc0 : ∀ᵐ c : ℂ, c ≠ 0 := by
    rw [ae_iff]; simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]; exact measure_singleton 0
  have hYc : Continuous fun x : HPar k r' => Yx k r' x := by
    have e : (fun x : HPar k r' => Yx k r' x) = fun x a => heis0 k r' (-x.1, -x.2) *ᵥ phi2 k r' a := by
      funext x a; unfold Yx; rw [hHI]
    rw [e]; have := heisenberg_map_continuous k r'; fun_prop
  have hGac : ∀ l, Continuous fun x : HPar k r' => Ga k (1 + r') l (Yx k r' x) := by
    intro l; unfold Ga; fun_prop
  have hDm : Measurable fun x => Dx k r' x := by unfold Dx; exact (hGac 0).sqrt.measurable
  have hPm : Measurable fun x => Psi k r' s x := by
    unfold Psi
    exact Finset.measurable_prod _ fun l _ => ((hGac _).measurable.div (hGac 0).measurable).pow_const _
  have hFm : Measurable (Function.uncurry fun (c : ℂ) (x : HPar k r') => ENNReal.ofReal (‖c‖ ^ aw) *
      (ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (mw k r' (c * (Dx k r' x : ℂ))))) :=
    ((measurable_norm.comp measurable_fst).pow_const _).ennreal_ofReal.mul
      ((hPm.comp measurable_snd).ennreal_ofReal.mul ((mw_meas k r').comp
        (measurable_fst.mul (Complex.measurable_ofReal.comp (hDm.comp measurable_snd)))).ennreal_ofReal)
  have hS0 : ∑ l, s0 k (1 + r') l = 2 * (1 + (r' : ℝ)) + k := by
    rw [sum_sc, levelExponent_first_eq_two, sum_levelExponents_shifted]; ring
  have hlt : ∑ l, s l < ∑ l, s0 k (1 + r') l :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun l _ => by linarith [(hs l).1]
  have hge : ∑ l, (s0 k (1 + r') l - 1 / 10) ≤ ∑ l, s l := Finset.sum_le_sum fun l _ => by linarith [(hs l).2]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hge
  push_cast at hge
  have hK1 : ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c) < ⊤ := by
    have h := cInt_fin (2 * r' + k + 1) (∑ l, s l) (by linarith) (by push_cast; linarith)
    have e : (4 * r' + 2 * k + 3 : ℕ) = 2 * (2 * r' + k + 1) + 1 := by ring
    unfold mw; rw [e, haw]; exact h
  have hCHc : CHCond (1 + r') fun l =>
      (if l = 0 then aw + 2 - ∑ l' : Fin (r' + 1), s (sc r' l') else s l) - s0N (1 + r') (k - 1) l := by
    refine chcond_of _ (fun l => s0 k (1 + r') l - s l) (fun l => by linarith [(hs l).1]) ?_ ?_
    · simp only [if_pos rfl]
      rw [sum_erase0, exponentShift_eq_levelExponent k r' hk, levelExponent_first_eq_two, Finset.sum_sub_distrib, sum_levelExponents_shifted, haw, sum_sc r' s]
      push_cast; ring
    · intro l hl0
      simp only [if_neg hl0]
      rw [exponentShift_eq_levelExponent k r' hk]; ring
  have hTh : ∫⁻ x, ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) (th_fin hB2 hF hCH k r' hk _ hCHc)
    have hg := yx_ga hB2 hIW k r' hk x
    exact th_ident k r' s aw x hg.1 hg.2
  calc ∫⁻ c, ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))) *
        ∫⁻ p : (HPar k r' × HPar k r') × Mt k r',
          ENNReal.ofReal (gN (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)) ^ (-A)) *
            FsE k (1 + r') s (Matrix.of (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2))
          ∂((volume : Measure (HPar k r' × HPar k r')).prod μ₁)
      ≤ ∫⁻ c, ENNReal.ofReal (‖c‖ ^ aw) * ∫⁻ x, ENNReal.ofReal (Psi k r' s x) *
          (ENNReal.ofReal (|C0| * mw k r' (c * (Dx k r' x : ℂ))) * J1) := by
        refine lintegral_mono_ae (hc0.mono fun c hc => ?_)
        have h := inner_c_le k r' hB2 hIW hT hk A C0 hC0 s μ₁ hμ₁ c hc
        rw [← hJ1d, ← haw] at h; exact h
    _ = ENNReal.ofReal |C0| * J1 * ∫⁻ x, ∫⁻ c, ENNReal.ofReal (‖c‖ ^ aw) *
          (ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (mw k r' (c * (Dx k r' x : ℂ)))) := by
        rw [← lintegral_lintegral_swap hFm.aemeasurable,
          ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ1.ne)]
        refine lintegral_congr fun c => ?_
        rw [← lintegral_const_mul' (ENNReal.ofReal (‖c‖ ^ aw)) _ ENNReal.ofReal_ne_top,
          ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ1.ne)]
        refine lintegral_congr fun x => ?_
        rw [ENNReal.ofReal_mul (abs_nonneg _)]; ring
    _ = ENNReal.ofReal |C0| * J1 * ∫⁻ x, ENNReal.ofReal (Psi k r' s x) *
          (ENNReal.ofReal (Dx k r' x ^ (-(aw + 2))) *
            ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c)) := by
        congr 1
        refine lintegral_congr fun x => ?_
        have hD : 0 < Dx k r' x := Real.sqrt_pos.mpr (yx_ga hB2 hIW k r' hk x).1
        rw [← scale_c k r' aw _ hD, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun c => ?_; ring
    _ = ENNReal.ofReal |C0| * J1 * ((∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ aw) * ENNReal.ofReal (mw k r' c)) *
          ∫⁻ x, ENNReal.ofReal (Psi k r' s x) * ENNReal.ofReal (Dx k r' x ^ (-(aw + 2)))) := by
        congr 1
        rw [← lintegral_const_mul' _ _ hK1.ne]
        refine lintegral_congr fun x => ?_; ring
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ1) (ENNReal.mul_lt_top hK1 hTh)

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
