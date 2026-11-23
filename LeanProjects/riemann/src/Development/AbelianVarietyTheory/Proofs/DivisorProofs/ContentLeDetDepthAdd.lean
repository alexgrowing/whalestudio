import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtBasisMapGood
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsExpEqOfSubstLg
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TypicalBasisCoordinates
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainLemmaMultivariatePowerSeriesCoordinateForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBasisChangeInvariaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthIntegralCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeFormalGroupDeterminantPowDepthOfRadiiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypicalCurveBasisAdaptedToSaturatedFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdGeExpOfLogSumTwoRadiiStatement

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth.InertBound

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem exists_chart_coords {d M : ℕ} (G : LogFGL v d) (Φ Ψ : Fin d → MvPowerSeries (Fin d) C)
    (hΦ0 : ∀ a, constantCoeff (Φ a) = 0) (hΨ0 : ∀ a, constantCoeff (Ψ a) = 0)
    (hΨΦ : ∀ a, subst Ψ (Φ a) = X a) (L : Fin d → MvPowerSeries (Fin M) C)
    (hL : ∀ k, constantCoeff (L k) = 0) :
    ∃ t : Fin d → MvPowerSeries (Fin M) C, (∀ a, constantCoeff (t a) = 0) ∧
      ∀ e, subst t (subst Φ (G.lg e)) = L e := by
  have hex := isExp_expOf G
  have hL' : HasSubst L := hasSubst_of_constantCoeff_zero hL
  have hexs : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero hex.1
  set E : Fin d → MvPowerSeries (Fin M) C := fun k => subst L (expOf G k) with hE
  have hE0 : ∀ k, constantCoeff (E k) = 0 := fun k =>
    constantCoeff_subst_eq_zero hL' hL (hex.1 k)
  have hEs : HasSubst E := hasSubst_of_constantCoeff_zero hE0
  refine ⟨fun a => subst E (Ψ a), fun a => constantCoeff_subst_eq_zero hEs hE0 (hΨ0 a), ?_⟩
  intro e
  have hΨs : HasSubst Ψ := hasSubst_of_constantCoeff_zero hΨ0
  have hΦs : HasSubst Φ := hasSubst_of_constantCoeff_zero hΦ0
  have h1 : ∀ k, subst (fun a => subst E (Ψ a)) (Φ k) = E k := by
    intro k
    rw [← subst_comp_subst_apply hΨs hEs, hΨΦ, subst_X hEs]
  rw [subst_comp_subst_apply hΦs (hasSubst_of_constantCoeff_zero
    (fun a => constantCoeff_subst_eq_zero hEs hE0 (hΨ0 a)))]
  simp only [h1]
  rw [hE, ← subst_comp_subst_apply hexs hL', hex.2 e, subst_X hL']

theorem lgSum_mulMatrix {d M : ℕ} (p : ℕ) (c : Fin d → ℕ → Fin d → C)
    (t : Fin d → MvPowerSeries (Fin M) C) (N : Matrix (Fin d) (Fin d) C) (b : Fin d) :
    lgSum p (fun a n b => ∑ e, c a n e * N e b) t b = ∑ e, N e b • lgSum p c t e := by
  ext α
  simp only [lgSum, map_sum, coeff_smul, smul_eq_mul]
  show (∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, (∑ e, c a n e * N e b) * coeff α (t a ^ p ^ n))
    = ∑ e, N e b * (∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n e * coeff α (t a ^ p ^ n))
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by ring

end

end GlobalTheory.FGDepth.InertBound

namespace GlobalTheory.FGDepth.InertBound

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem coeff_subst_typical {M p : ℕ} (hp : 2 ≤ p) (f : PowerSeries C)
    (hf : ∀ m, (∀ n, m ≠ p ^ n) → PowerSeries.coeff m f = 0)
    (s : MvPowerSeries (Fin M) C) (hs : constantCoeff s = 0) (α : Fin M →₀ ℕ) :
    coeff α (PowerSeries.subst s f) = ∑ n ∈ Finset.range (Finsupp.degree α + 1),
      PowerSeries.coeff (p ^ n) f * coeff α (s ^ (p ^ n)) := by
  classical
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs),
    finsum_eq_sum_of_support_subset
      (s := (Finset.range (Finsupp.degree α + 1)).image fun n => p ^ n),
    Finset.sum_image fun x _ y _ hxy => Nat.pow_right_injective hp hxy]
  · rfl
  · intro m hm
    rw [Function.mem_support, smul_eq_mul] at hm
    obtain ⟨n, rfl⟩ : ∃ n, m = p ^ n := by
      by_contra hne
      exact hm (by rw [hf m (fun n e => hne ⟨n, e⟩), zero_mul])
    have hle : p ^ n ≤ Finsupp.degree α := by
      by_contra hlt
      exact hm (by rw [GlobalTheory.ChainCoord.coeff_pow_eq_zero hs α (not_le.1 hlt), mul_zero])
    have hn : n < p ^ n := Nat.lt_pow_self hp
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩)

theorem subst_sum_lgCurve {d M : ℕ} (G : LogFGL v d) {p : ℕ} (hp : 2 ≤ p)
    (γ : Fin d → Fin d → PowerSeries C) (hγ : ∀ a, G.IsPTypical p (γ a))
    (t : Fin d → MvPowerSeries (Fin M) C) (ht : ∀ a, constantCoeff (t a) = 0) (b : Fin d) :
    subst t (∑ a, PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) b)) =
      lgSum p (fun a n e => G.lc p (γ a) n e) t b := by
  have hts : HasSubst t := hasSubst_of_constantCoeff_zero ht
  have h1 : ∀ a (f : PowerSeries C),
      subst t (PowerSeries.subst (X a : MvPowerSeries (Fin d) C) f) = PowerSeries.subst (t a) f := by
    intro a f
    rw [PowerSeries.subst_def, PowerSeries.subst_def, subst_comp_subst_apply (ptOn_hs a) hts]
    simp only [subst_X hts]
  rw [← coe_substAlgHom hts, map_sum]
  simp only [coe_substAlgHom, h1]
  ext α
  rw [map_sum]
  show _ = ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a,
    G.lc p (γ a) n b * coeff α (t a ^ (p ^ n))
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => coeff_subst_typical hp _ (hγ a b) (t a) (ht a) α

theorem sum_radii_le {i d j : ℕ} (p : ℕ) (hp : 2 ≤ p) (r : Fin i → Fin d) (good : Fin d → Prop)
    [DecidablePred good] (hgood : ∀ a : Fin i, j ≤ a.val → good (r a)) :
    (∑ a, (if good (r a) then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))) ≤
      i * (2 / ((p : ℝ) * (p - 1))) + j * (2 / ((p : ℝ) - 1)) := by
  have hp1 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hA : 0 ≤ 2 / ((p : ℝ) * (p - 1)) :=
    div_nonneg zero_le_two (mul_nonneg (by linarith) (by linarith))
  have hB : 0 ≤ 2 / ((p : ℝ) - 1) := div_nonneg zero_le_two (by linarith)
  generalize 2 / ((p : ℝ) * (p - 1)) = A at hA ⊢
  generalize 2 / ((p : ℝ) - 1) = B at hB ⊢
  have hcard : (Finset.univ.filter fun a : Fin i => a.val < j).card ≤ j := by
    calc _ = ((Finset.univ.filter fun a : Fin i => a.val < j).map Fin.valEmbedding).card :=
          (Finset.card_map _).symm
      _ ≤ (Finset.range j).card := Finset.card_le_card fun x hx => by
          obtain ⟨a, ha, rfl⟩ := Finset.mem_map.1 hx
          exact Finset.mem_range.2 (Finset.mem_filter.1 ha).2
      _ = j := Finset.card_range j
  calc _ ≤ ∑ a : Fin i, (A + if a.val < j then B else 0) := Finset.sum_le_sum fun a _ => by
        by_cases hj : a.val < j
        · rw [if_pos hj]
          split_ifs <;> linarith
        · rw [if_neg hj, if_pos (hgood a (not_lt.1 hj)), add_zero]
    _ = i * A + (Finset.univ.filter fun a : Fin i => a.val < j).card * B := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter]
        simp
    _ ≤ _ := by
        have : ((Finset.univ.filter fun a : Fin i => a.val < j).card : ℝ) ≤ j := by
          exact_mod_cast hcard
        nlinarith [mul_le_mul_of_nonneg_right this hB]

end

end GlobalTheory.FGDepth.InertBound

namespace GlobalTheory.FGDepth.InertBound

open GlobalTheory.ChainCoord in

theorem content_le_detDepth_add :
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
      p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h → ∀ (ty : Fin d → ZMod h) (G : LogFGL v d),
        MuAction G p h ty → ∀ (τ : ZMod h) (j i c : ℕ),
          (Finset.univ.filter fun a => ty a = τ + 1).card ≤ j →
          ∀ u : Fin i → Fin d → C, IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) →
            content v (detPow C i c) ≤ detDepth G u c +
              ((2 * i * c / ((p : ℝ) * (p - 1)) + 2 * j * c / ((p : ℝ) - 1) : ℝ) : EReal) := by
  intro C _ _ _ v p hp hv d h hh ty G μ τ j i c hcard u hu hsupp
  classical
  obtain ⟨γ, r, g, hB, -, hgdet, htan, hgood⟩ :=
    GlobalTheory.T.exists_typicalCurve_basis_adapted_to_saturated_frame C v p hp hv d h hh ty G μ τ j i hcard u hu hsupp
  obtain ⟨hγ, hγty, hdet⟩ := hB
  have e1 : detDepth G u c = detDepth G (fun a => tangent (γ (r a))) c := by
    rw [← GlobalTheory.T.formalGroupDeterminantPowDepth_basis_change_invariant C v i d c G u g hgdet]
    congr 1
    funext a
    exact (htan a).symm
  obtain ⟨Ψ, hΨi, hΨ0, hΨΦ, hΦΨ⟩ := ptBasisMap_inv G hγ hdet
  have hΦg := ptBasisMap_good G hγ
  set T : Matrix (Fin d) (Fin d) C := Matrix.of fun a b => tangent (γ a) b with hT
  obtain ⟨hTu, hTinv⟩ := pt_inv_int (M := T) (fun a b => (hγ a b).2 1) hdet
  set L : Fin d → MvPowerSeries (Fin i) C := fun e => ∑ a, tangent (γ (r a)) e • X a with hLdef
  have hL0 : ∀ e, constantCoeff (L e) = 0 := by intro e; simp [L]
  obtain ⟨t, ht0, htL⟩ :=
    exists_chart_coords G (ptBasisMap G γ) Ψ (fun a => (hΦg a).1) hΨ0 hΨΦ L hL0
  have hp2 : 2 ≤ p := hp.two_le
  have hlg : ∀ b, lgSum p (fun a n e => G.lc p (γ a) n e) t b = L b := by
    intro b
    rw [← htL b, ptBasisMap_lg G hγ b,
      subst_sum_lgCurve G hp2 γ (fun a => (hγty a).1) t ht0 b]
  set c' : Fin d → ℕ → Fin d → C := fun a n b => ∑ e, G.lc p (γ a) n e * T⁻¹ e b with hc'
  set z' : Fin d → MvPowerSeries (Fin i) C := fun b => ∑ e, T⁻¹ e b • L e with hz'
  have hlg' : ∀ b, lgSum p c' t b = z' b := by
    intro b
    rw [hc', lgSum_mulMatrix]
    simp only [hlg, hz']
  set good : Fin d → Prop := fun b => G.lc p (γ b) 1 = 0 with hgoodDef
  set rad : Fin d → ℝ := fun b => if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)
    with hrad
  set ρ : Fin i → ℝ := fun a => rad (r a) with hρ
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hrad0 : ∀ b, 0 ≤ rad b := by
    intro b
    simp only [hrad]
    split_ifs
    · exact div_nonneg zero_le_two (mul_nonneg (by linarith) (by linarith))
    · exact div_nonneg zero_le_two (by linarith)
  have hTT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hTu
  have hc0 : ∀ a, c' a 0 = Pi.single a 1 := by
    intro a
    funext b
    have hte : ∀ e, G.lc p (γ a) 0 e = T a e := fun e => by
      simp only [hT, Matrix.of_apply]
      exact (congrFun (ReciprocityTheory.ChartRestriction.G.Sh.PTb.tangent_eq_lc_zero G p (fun e => (hγ a e).1)) e).symm
    simp only [hc', hte]
    rw [← Matrix.mul_apply, hTT, Matrix.one_apply, Pi.single_apply]
    by_cases hab : b = a
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have hcn : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c' a n b) := by
    intro a n b
    refine v.map_le_sum fun e _ => ?_
    rw [v.map_mul]
    exact le_add_of_le_of_nonneg ((pt5v' C v p hp hv d h ty G γ ⟨hγ, hγty, hdet⟩ a).1 n e)
      (hTinv e b)
  have hcg : ∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n →
      ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c' a n b) := by
    intro a ha n b hn
    refine v.map_le_sum fun e _ => ?_
    rw [v.map_mul]
    exact le_add_of_le_of_nonneg
      ((pt5v' C v p hp hv d h ty G γ ⟨hγ, hγty, hdet⟩ a).2 ha n e hn) (hTinv e b)
  have hzeq : ∀ b, z' b = ∑ a, ((1 : Matrix (Fin d) (Fin d) C) (r a) b) • (X a : MvPowerSeries (Fin i) C) := by
    intro b
    rw [← hTT]
    simp only [hz', hLdef, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    simp only [hT, Matrix.of_apply]
    ring_nf
  have hz : ∀ b, OrdGe v ρ (z' b) (rad b) := by
    intro b
    rw [hzeq b]
    refine ord_sum _ fun a _ => ?_
    rw [Matrix.one_apply]
    split_ifs with hab
    · rw [one_smul]
      intro α
      rw [coeff_X]
      split_ifs with hα
      · subst hα
        have hs : ∑ m, ρ m * ((Finsupp.single a 1 : Fin i →₀ ℕ) m : ℝ) = ρ a := by
          simp [Finsupp.single_apply]
        rw [hs, v.map_one, ← hab]
        show ((rad (r a) - rad (r a) : ℝ) : WithTop ℝ) ≤ 0
        simp
      · simp
    · rw [zero_smul]
      exact ord_zero _
  have hD := GlobalTheory.T.ordGe_exp_of_logSum_two_radii C v p hp hv d i good c' hc0 hcn hcg ρ z' t hz ht0 hlg'
  have htord : ∀ b, OrdGe v ρ (t b) 0 := fun b => ord_mono (hD b) (hrad0 b)
  have e2 := GlobalTheory.T.differentialOperatorDepth_integral_coordinates C v i d c G (fun a => tangent (γ (r a))) (basisMap G γ) Ψ
    (fun a => by
      rw [basisMap_eq_ptBasisMap]
      exact ⟨(hΦg a).2, (hΦg a).1, hΨi a, hΨ0 a⟩)
    (fun a => by rw [basisMap_eq_ptBasisMap]; exact ⟨hΨΦ a, hΦΨ a⟩) t ht0
    (fun e => by rw [basisMap_eq_ptBasisMap]; exact htL e)
  rw [e1]
  have hS : (c : ℝ) * ∑ a, ρ a ≤ 2 * i * c / ((p : ℝ) * (p - 1)) + 2 * j * c / ((p : ℝ) - 1) := by
    have := sum_radii_le (d := d) p hp2 r good hgood
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    calc (c : ℝ) * ∑ a, ρ a ≤ c * (i * (2 / ((p : ℝ) * (p - 1))) + j * (2 / ((p : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  have hlowAll : ∀ B : ℝ, (∀ α ∈ (detPow C i c).support, ((B + (c : ℝ) * ∑ a, ρ a : ℝ) : WithTop ℝ) ≤
      v ((detPow C i c).coeff α * mfact α)) →
      (B : EReal) ≤ detDepth G (fun a => tangent (γ (r a))) c := by
    intro B hB
    rw [e2]
    refine le_iInf fun f => ?_
    have := GlobalTheory.T.le_formalGroupDeterminantPowDepth_of_radii C v i d c ρ t B ht0 htord hB f.1 f.2
    exact WithBot.coe_le_coe.2 this
  by_cases hfin : ∃ α ∈ (detPow C i c).support, v ((detPow C i c).coeff α * mfact α) ≠ ⊤
  · obtain ⟨α1, hα1, hne⟩ := hfin
    obtain ⟨α0, hα0, hmin⟩ := (detPow C i c).support.exists_min_image
      (fun α => v ((detPow C i c).coeff α * mfact α)) ⟨α1, hα1⟩
    have hne0 : v ((detPow C i c).coeff α0 * mfact α0) ≠ ⊤ := ne_top_of_le_ne_top hne (hmin α1 hα1)
    obtain ⟨κ, hκ⟩ := WithTop.ne_top_iff_exists.1 hne0
    have hlow := hlowAll (κ - (c : ℝ) * ∑ a, ρ a) (fun α hα => by
      rw [sub_add_cancel, hκ]; exact hmin α hα)
    have hcont : content v (detPow C i c) ≤ (κ : EReal) := by
      unfold content
      refine (iInf₂_le α0 hα0).trans (le_of_eq ?_)
      rw [← hκ]
      rfl
    refine hcont.trans ?_
    have e3 : (κ : EReal) = ((κ - (c : ℝ) * ∑ a, ρ a : ℝ) : EReal) + (((c : ℝ) * ∑ a, ρ a : ℝ) : EReal) := by
      rw [← EReal.coe_add]; congr 1; ring
    rw [e3]
    exact add_le_add hlow (EReal.coe_le_coe_iff.2 hS)
  · push_neg at hfin
    have htop : detDepth G (fun a => tangent (γ (r a))) c = ⊤ := by
      refine (EReal.eq_top_iff_forall_lt _).2 fun y => ?_
      refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one y)) (hlowAll (y + 1) fun α hα => ?_)
      rw [hfin α hα]
      exact le_top
    rw [htop, EReal.top_add_coe]
    exact le_top

end GlobalTheory.FGDepth.InertBound
