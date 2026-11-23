import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.InnerBound

noncomputable section
open Matrix MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 BL

theorem bStepBase_of (hB2 : InductiveHeisenbergInputs) : BStepBase := by
  obtain ⟨-, -, -, -, hNB, -⟩ := hB2
  intro k _ δ _
  refine ⟨1, one_pos, fun s _ z _ _ μN hμ => ?_⟩
  set o : Mt k 0 := ((1 : Mat k 0) : Mt k 0) with ho
  have hc : μN ({o}ᶜ : Set (Mt k 0)) = 0 := by
    have h := hμ.conc; rw [hNB k] at h; exact h
  have hr : μN.restrict {o} = μN :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (by simpa [Set.compl_def] using hc))
  unfold IInt
  rw [← hr, lintegral_singleton]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    (hμ.finite_compact _ isCompact_singleton)

theorem bStepSucc_of (hB2 : InductiveHeisenbergInputs) (hIW : IW) (hF : FormulaF) (hOS : OS) : BStepSucc := by
  obtain ⟨-, -, -, hNR, -, hHC, -, -, -, -, -, hHH, -, -, -, -, hHU, -, -, -, hCN, -, -, -, hHN, -, hHA⟩ := hB2
  intro k r r' hr hk δ hδ hδ2 hB'
  subst hr
  obtain ⟨e', he', hB'⟩ := hB'
  obtain ⟨γ, hγd⟩ : ∃ γ : ℝ, γ = min (δ / 8) (e' / 2) := ⟨_, rfl⟩
  have hγ : 0 < γ := by rw [hγd]; exact lt_min (by positivity) (by positivity)
  have hγ8 : γ ≤ δ / 8 := by rw [hγd]; exact min_le_left _ _
  have hγe : γ ≤ e' / 2 := by rw [hγd]; exact min_le_right _ _
  have hD : (0 : ℝ) < 4 * (1 + r') + 4 := by positivity
  refine ⟨min (e' / 2) (γ / (4 * (1 + r') + 4)), lt_min (by positivity) (div_pos hγ hD), ?_⟩
  intro s hs z hzW hzT μN hμN
  have he0 : ∀ l, 0 < s0 k (1 + r') l - s l := fun l => (hs l).1
  have heS : ∀ l, s0 k (1 + r') l - s l ≤ γ / (4 * (1 + r') + 4) := fun l => le_trans (hs l).2 (min_le_right _ _)
  have heS' : ∀ l, s0 k (1 + r') l - s l ≤ e' / 2 := fun l => le_trans (hs l).2 (min_le_left _ _)
  have hs0 : ∀ l, s0N (1 + r') (k - 1) l = s0 k (1 + r') l := by
    intro l; unfold s0N s0; split_ifs
    · rfl
    · push_cast [Nat.cast_sub hk]; ring
  have hsum : (s0 k (1 + r') 0 - s 0) + 2 * ∑ i : Fin (1 + r'), (s0 k (1 + r') i.succ - s i.succ) < γ / 2 := by
    have h1 : ∑ i : Fin (1 + r'), (s0 k (1 + r') i.succ - s i.succ) ≤ (1 + r') * (γ / (4 * (1 + r') + 4)) := by
      calc _ ≤ ∑ _i : Fin (1 + r'), γ / (4 * (1 + r') + 4) := Finset.sum_le_sum fun i _ => heS _
        _ = _ := by simp [Finset.sum_const, Finset.card_univ]
    have key : (3 + 2 * (r' : ℝ)) * (γ / (4 * (1 + r') + 4)) < γ / 2 := by
      rw [mul_div_assoc', div_lt_div_iff₀ hD (by norm_num)]; nlinarith
    linarith [heS 0]
  obtain ⟨C, hC⟩ := os_q hOS (1 + r') r' (k - 1) (by omega) δ γ (fun l => s0 k (1 + r') l - s l) hδ hδ2 hγ hγ8 he0 hsum
  have hC' : ∀ (η η' : Fin (1 + r') → ℂ) (ζ : Fin (k - 1) → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI s δ η η' ζ c₀ x ≤ ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)) := by
    intro η η' ζ c₀ h
    have hse : s = fun l => s0N (1 + r') (k - 1) l - (s0 k (1 + r') l - s l) := by funext l; rw [hs0]; ring
    rw [hse]; exact hC η η' ζ c₀ h
  obtain ⟨z1, hz1W, rfl⟩ : ∃ z1, inWb k r' z1 ∧ z = liftVec k 1 r' z1 := ⟨_, shifted_mem_weightSpace z hzW, z_lift z hzW⟩
  have hz1T : 0 < Tz k r' z1 := by rw [← tz_lift]; exact hzT
  have hcz := cz_ne hk z1 hz1T
  have hsP : ∀ a : Fin (r' + 1), 0 < s0 k r' a - (s (su a) - if a = 0 then γ else 0) ∧
      s0 k r' a - (s (su a) - if a = 0 then γ else 0) ≤ e' := by
    intro a
    have hs0a : s0 k r' a = s0 k (1 + r') (su a) := by
      unfold s0
      by_cases h : a.val < r'
      · rw [if_pos h, if_pos (show (su a).val < 1 + r' by rw [su_val]; omega)]
      · rw [if_neg h, if_neg (show ¬ (su a).val < 1 + r' by rw [su_val]; omega)]
    rw [hs0a]
    have h1 := he0 (su a); have h2 := heS' (su a)
    split_ifs <;> constructor <;> linarith
  obtain ⟨μ', hμ'⟩ := hHN k r'
  have hfin := hB' _ hsP z1 hz1W hz1T μ' hμ'
  obtain ⟨c, hc⟩ := hHU k (1 + r') (Nset k (1 + r')) _ μN (hCN k (1 + r')) (hNR k r' μ' hμ') hμN.conc hμN.left
    hμN.finite_compact
  rw [hc]; unfold IInt; rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  have : IsFiniteMeasureOnCompacts μ' := ⟨fun ⦃K⦄ hK => hμ'.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts (μHeis k r') := ⟨fun ⦃K⦄ hK => (hHH k r').finite_compact K hK⟩
  set F : Mt k (1 + r') → ℝ≥0∞ := fun n => ENNReal.ofReal (xiR k (1 + r') s (Matrix.of n)) *
    ENNReal.ofReal ((1 + |lam k (1 + r') (liftVec k 1 r' z1) (Matrix.of n)|) ^ (-δ)) with hFd
  have hsw : (μHeis k r').prod (μ'.map (levM k r')) = ((μ'.map (levM k r')).prod (μHeis k r')).map Prod.swap :=
    (Measure.prod_swap).symm
  have hae : ∀ᵐ m ∂μ', m ∈ Nset k r' := ae_iff.2 hμ'.conc
  have hpt : ∀ m ∈ Nset k r', ∫⁻ h, F (mulM (h, levM k r' m)) ∂(μHeis k r') ≤
      ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
        (ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) (Matrix.of m)) *
          ENNReal.ofReal ((1 + |lam k r' z1 (Matrix.of m)|) ^ (-(δ / 4)))) := by
    intro m hm
    calc _ ≤ ∫⁻ X, F (mulM (heis0 k r' X, levM k r' m)) ∂volume := by unfold μHeis; exact lintegral_map_le _ _
      _ ≤ _ := by rw [hFd]; exact inner_bound hIW hF hHC hHA hk s δ γ C z1 hC' hcz (Matrix.of m) hm.1
  calc ∫⁻ n, F n ∂(((μHeis k r').prod (μ'.map (levM k r'))).map mulM)
      ≤ ∫⁻ q, F (mulM q) ∂((μHeis k r').prod (μ'.map (levM k r'))) := lintegral_map_le _ _
    _ = ∫⁻ q, F (mulM q) ∂(((μ'.map (levM k r')).prod (μHeis k r')).map Prod.swap) := by rw [hsw]
    _ ≤ ∫⁻ q, F (mulM q.swap) ∂((μ'.map (levM k r')).prod (μHeis k r')) := lintegral_map_le _ _
    _ ≤ ∫⁻ n', ∫⁻ h, F (mulM (h, n')) ∂(μHeis k r') ∂(μ'.map (levM k r')) := lintegral_prod_le _
    _ ≤ ∫⁻ m, ∫⁻ h, F (mulM (h, levM k r' m)) ∂(μHeis k r') ∂μ' := lintegral_map_le _ _
    _ ≤ ∫⁻ m, ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
          (ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) (Matrix.of m)) *
            ENNReal.ofReal ((1 + |lam k r' z1 (Matrix.of m)|) ^ (-(δ / 4)))) ∂μ' := lintegral_mono_ae (hae.mono hpt)
    _ = ENNReal.ofReal (C * ‖herm (Hpk k r') (phiV k r' ⟨0, by omega⟩) (fvec k r' z1 ⟨0, by omega⟩)‖ ^ (-γ)) *
          ∫⁻ m, ENNReal.ofReal (xiR k r' (fun a => s (su a) - if a = 0 then γ else 0) (Matrix.of m)) *
            ENNReal.ofReal ((1 + |lam k r' z1 (Matrix.of m)|) ^ (-(δ / 4))) ∂μ' :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end ReciprocityTheory.ChartRestriction.DS.Xi
