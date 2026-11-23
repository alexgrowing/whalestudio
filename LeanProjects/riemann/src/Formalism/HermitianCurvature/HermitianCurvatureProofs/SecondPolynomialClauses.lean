import Formalism.HermitianCurvature.LowerBlockNormalisedBoundFromComponents

open Finset
open scoped ComplexOrder

noncomputable section

namespace Formalism.FourierDecayAlt.P.SecondPolynomialClauses

open Formalism.FourierDecayAlt.PairingProductCorollary

theorem p3bOfA_ok : LeadingBlockBoundFromRecursion := by
  intro K t t' Ntt Nt Nt' S abelian₂ c ht ht' hne hle hNt hNt' hS hLam hc hG hA
  have ho0 : 0 < ‖1 / t - 1 / t'‖ := norm_pos_iff.mpr hne
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hto : ‖1 / t - 1 / t'‖ * ‖t‖ ≤ 2 := by
    have h1 : ‖1 / t - 1 / t'‖ ≤ ‖1 / t‖ + ‖1 / t'‖ := norm_sub_le _ _
    have h2 : ‖1 / t'‖ ≤ 1 / ‖t‖ := by
      rw [norm_div, norm_one]; exact one_div_le_one_div_of_le htpos hle
    have h3 : ‖1 / t‖ = 1 / ‖t‖ := by rw [norm_div, norm_one]
    have h4 : ‖1 / t - 1 / t'‖ ≤ 2 / ‖t‖ := by
      rw [h3] at h1; linarith [show 2 / ‖t‖ = 1 / ‖t‖ + 1 / ‖t‖ by ring]
    exact (le_div_iff₀ htpos).mp h4
  have hL : ‖t‖ * abelian₂ ≤ 2 * abelian₂ / ‖1 / t - 1 / t'‖ := by
    rw [le_div_iff₀ ho0]; nlinarith [mul_le_mul_of_nonneg_left hto hLam]
  have hprod : ∏ a, c a ≤ (abelian₂ ^ 2) ^ K := by
    calc ∏ a, c a ≤ ∏ _a : Fin K, abelian₂ ^ 2 :=
          Finset.prod_le_prod (fun a _ => (hc a).1) (fun a _ => (hc a).2)
      _ = (abelian₂ ^ 2) ^ K := by simp
  have hT : 0 < ‖t‖ ^ (2 * K) := pow_pos htpos _
  have e : ‖t‖ ^ (-(2 * K : ℤ)) = (‖t‖ ^ (2 * K))⁻¹ := by
    rw [zpow_neg]; norm_cast
  rw [e] at hA
  have hA' : Nt ≤ ‖t‖ ^ (2 * K) * ((∏ a, c a) * S) := (inv_mul_le_iff₀ hT).mp hA
  have hX0 : 0 ≤ (2 * abelian₂ / ‖1 / t - 1 / t'‖) ^ K := pow_nonneg (div_nonneg (by linarith) ho0.le) K
  have hNtX : Nt ≤ ((2 * abelian₂ / ‖1 / t - 1 / t'‖) ^ K) ^ 2 * S := by
    calc Nt ≤ ‖t‖ ^ (2 * K) * ((∏ a, c a) * S) := hA'
      _ ≤ ‖t‖ ^ (2 * K) * ((abelian₂ ^ 2) ^ K * S) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hS) hT.le
      _ = ((‖t‖ * abelian₂) ^ K) ^ 2 * S := by ring
      _ ≤ ((2 * abelian₂ / ‖1 / t - 1 / t'‖) ^ K) ^ 2 * S :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (pow_nonneg (mul_nonneg (norm_nonneg _) hLam) K)
            (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hLam) hL K) 2) hS
  have hsq : ‖Ntt‖ ^ 2 ≤ ((2 * abelian₂ / ‖1 / t - 1 / t'‖) ^ K * ((S + Nt') / 2)) ^ 2 := by
    calc ‖Ntt‖ ^ 2 ≤ Nt * Nt' := hG
      _ ≤ ((2 * abelian₂ / ‖1 / t - 1 / t'‖) ^ K) ^ 2 * S * Nt' := mul_le_mul_of_nonneg_right hNtX hNt'
      _ ≤ ((2 * abelian₂ / ‖1 / t - 1 / t'‖) ^ K) ^ 2 * ((S + Nt') / 2) ^ 2 := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (S - Nt')]) (sq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hX0 (by linarith)) two_ne_zero).mp hsq

theorem unipotent_degree_three_of_parts : UnnormalisedLiftBoundFromComponents := by
  intro K d grid q w e o W0 W RL RV he hq hR hD hS
  unfold LiftLeadingCoefficientIdentity at hD
  unfold NodeDualityBound at hS
  have hne : ‖e‖ = 1 := by rcases he with rfl | rfl <;> simp
  calc ‖o‖ ^ K * ‖W0‖ = ‖(e * o) ^ K * W0‖ := by rw [norm_mul, norm_pow, norm_mul, hne, one_mul]
    _ = ‖∑ j, ((coProd grid j : ℝ) : ℂ) * W j‖ := by rw [hD]
    _ ≤ ∑ j, ‖((coProd grid j : ℝ) : ℂ) * W j‖ := norm_sum_le _ _
    _ ≤ ∑ j, |coProd grid j| * Real.sqrt (RL j * RV j / qProd q w grid j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h := Real.abs_le_sqrt (hS j)
        rw [abs_norm] at h
        exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

theorem herm_of_psd {V : Type} [AddCommGroup V] [Module ℂ V] (R : Formalism.FourierDecayAlt.F7.Sesq V) (hR : PSD R)
    (x y : V) : (starRingEnd ℂ) (R x y) = R y x := by
  have h1 := (hR (x + y)).1
  have h2 := (hR (x + Complex.I • y)).1
  have hx := (hR x).1
  have hy := (hR y).1
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, map_smulₛₗ, Complex.conj_I,
    smul_eq_mul] at h1 h2
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im] at h1 h2
  apply Complex.ext
  · simp only [Complex.conj_re]; nlinarith
  · simp only [Complex.conj_im]; nlinarith

theorem cs_of_psd {V : Type} [AddCommGroup V] [Module ℂ V] (R : Formalism.FourierDecayAlt.F7.Sesq V) (hR : PSD R)
    (x y : V) : ‖R x y‖ ^ 2 ≤ (R x x).re * (R y y).re := by
  let c : PreInnerProductSpace.Core ℂ V :=
    { inner := fun x y => R y x
      conj_inner_symm := fun x y => herm_of_psd R hR x y
      re_inner_nonneg := fun x => (hR x).2
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ V _ _ _ c x y
  have e : ‖R y x‖ = ‖R x y‖ := by rw [← herm_of_psd R hR x y, Complex.norm_conj]
  rw [sq]
  calc ‖R x y‖ * ‖R x y‖ = ‖R y x‖ * ‖R x y‖ := by rw [e]
    _ ≤ _ := h

theorem second_polynomial_first_clause : PairingGramBound := by
  intro V _ _ R x wt bw hR hbw hwt t t'
  have hcs := cs_of_psd R hR (x t) (x t')
  have hk : 0 ≤ wt t * wt t' / bw := div_nonneg (mul_nonneg (hwt t) (hwt t')) hbw.le
  have e1 : ‖Npair R x wt bw t t'‖ = wt t * wt t' / bw * ‖R (x t) (x t')‖ := by
    rw [Npair, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk]
  have e2 : (Npair R x wt bw t t).re * (Npair R x wt bw t' t').re =
      (wt t * wt t' / bw) ^ 2 * ((R (x t) (x t)).re * (R (x t') (x t')).re) := by
    simp only [Npair, Complex.re_ofReal_mul]; ring
  rw [e1, e2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk]
  exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (Real.abs_le_sqrt hcs)) hk

theorem third_polynomial_prime_combination : LeadingBlockSeveralPlacesBound := by
  intro ι _ _ K abelian₂ t t' Ntt Nt Nt' S1 S2 ht hLam hNt hNt' hS1 hS2 hG hA hB
  obtain ⟨m, hm⟩ : ∃ m : ι → ℝ, m = fun v => minFac (2 * abelian₂ v) (oAbs t t' v) K := ⟨_, rfl⟩
  have hm0 : ∀ v, 0 ≤ m v := by
    intro v; rw [hm]; dsimp only; unfold minFac; split_ifs with h
    · exact pow_nonneg (div_nonneg (by linarith [hLam v]) (norm_nonneg _)) _
    · exact zero_le_one
  have key : ∀ v (s : ℝ), 0 ≤ s → s * oAbs t t' v ≤ 2 → 2 * abelian₂ v < oAbs t t' v →
      (s * abelian₂ v) ^ (2 * K) ≤ m v ^ 2 := by
    intro v s hs hso hlt
    have ho : 0 < oAbs t t' v := lt_of_le_of_lt (by linarith [hLam v]) hlt
    have hmv : m v = (2 * abelian₂ v / oAbs t t' v) ^ K := by rw [hm]; dsimp only; rw [minFac, if_pos hlt]
    rw [hmv, ← pow_mul, mul_comm K 2]
    apply pow_le_pow_left₀ (mul_nonneg hs (hLam v))
    rw [le_div_iff₀ ho]; nlinarith [mul_le_mul_of_nonneg_right hso (hLam v)]
  have h1 : ∀ v, oAbs t t' v ≤ 1 / ‖t v‖ + 1 / ‖t' v‖ := by
    intro v; unfold oAbs
    calc _ ≤ ‖1 / t v‖ + ‖1 / t' v‖ := norm_sub_le _ _
      _ = _ := by rw [norm_div, norm_div, norm_one]
  have hto : ∀ v, ‖t v‖ ≤ ‖t' v‖ → ‖t v‖ * oAbs t t' v ≤ 2 := by
    intro v hle
    have ha : 0 < ‖t v‖ := norm_pos_iff.mpr (ht v).1
    have hb : 0 < ‖t' v‖ := norm_pos_iff.mpr (ht v).2
    calc ‖t v‖ * oAbs t t' v ≤ ‖t v‖ * (1 / ‖t v‖ + 1 / ‖t' v‖) := mul_le_mul_of_nonneg_left (h1 v) ha.le
      _ = 1 + ‖t v‖ / ‖t' v‖ := by rw [mul_add, mul_one_div_cancel ha.ne', mul_one_div]
      _ ≤ 2 := by linarith [(div_le_one hb).mpr hle]
  have hto' : ∀ v, ¬ ‖t v‖ ≤ ‖t' v‖ → ‖t' v‖ * oAbs t t' v ≤ 2 := by
    intro v hle
    have ha : 0 < ‖t v‖ := norm_pos_iff.mpr (ht v).1
    have hb : 0 < ‖t' v‖ := norm_pos_iff.mpr (ht v).2
    calc ‖t' v‖ * oAbs t t' v ≤ ‖t' v‖ * (1 / ‖t v‖ + 1 / ‖t' v‖) := mul_le_mul_of_nonneg_left (h1 v) hb.le
      _ = ‖t' v‖ / ‖t v‖ + 1 := by rw [mul_add, mul_one_div_cancel hb.ne', mul_one_div]
      _ ≤ 2 := by linarith [(div_le_one ha).mpr (le_of_lt (not_le.mp hle))]
  have hPA : (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖),
      (‖t v‖ * abelian₂ v) ^ (2 * K)) ≤
      ∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖), m v ^ 2 :=
    Finset.prod_le_prod (fun v _ => pow_nonneg (mul_nonneg (norm_nonneg _) (hLam v)) _)
      (fun v hv => by
        obtain ⟨hv1, hv2⟩ := (Finset.mem_filter.mp hv).2
        exact key v _ (norm_nonneg _) (hto v hv2) hv1)
  have hPB : (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖),
      (‖t' v‖ * abelian₂ v) ^ (2 * K)) ≤
      ∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖), m v ^ 2 :=
    Finset.prod_le_prod (fun v _ => pow_nonneg (mul_nonneg (norm_nonneg _) (hLam v)) _)
      (fun v hv => by
        obtain ⟨hv1, hv2⟩ := (Finset.mem_filter.mp hv).2
        exact key v _ (norm_nonneg _) (hto' v hv2) hv1)
  have hdisj : Disjoint (univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖))
      (univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖)) :=
    Finset.disjoint_filter.mpr fun v _ hv1 hv2 => hv2.2 hv1.2
  have hM : (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖), m v ^ 2) *
      (∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖), m v ^ 2) =
      (∏ v, m v) ^ 2 := by
    rw [← Finset.prod_union hdisj, ← Finset.prod_pow]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro v _ hv
    have hnot : ¬ 2 * abelian₂ v < oAbs t t' v := by
      intro hlt
      apply hv
      by_cases hle : ‖t v‖ ≤ ‖t' v‖
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hle⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hle⟩)
    rw [hm]; dsimp only; rw [minFac, if_neg hnot, one_pow]
  have hM0 : 0 ≤ ∏ v, m v := Finset.prod_nonneg fun v _ => hm0 v
  have hgoal : ∏ v, minFac (2 * abelian₂ v) (oAbs t t' v) K = ∏ v, m v := by rw [hm]
  rw [hgoal]
  have hsq : ‖Ntt‖ ^ 2 ≤ ((∏ v, m v) * ((S1 + S2) / 2)) ^ 2 := by
    calc ‖Ntt‖ ^ 2 ≤ Nt * Nt' := hG
      _ ≤ ((∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖),
            (‖t v‖ * abelian₂ v) ^ (2 * K)) * S1) *
          ((∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖),
            (‖t' v‖ * abelian₂ v) ^ (2 * K)) * S2) :=
          mul_le_mul hA hB hNt' (le_trans hNt hA)
      _ ≤ ((∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ‖t v‖ ≤ ‖t' v‖), m v ^ 2) * S1) *
          ((∏ v ∈ univ.filter (fun v => 2 * abelian₂ v < oAbs t t' v ∧ ¬ ‖t v‖ ≤ ‖t' v‖), m v ^ 2) * S2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hPA hS1) (mul_le_mul_of_nonneg_right hPB hS2)
            (mul_nonneg (Finset.prod_nonneg fun v _ => pow_nonneg (mul_nonneg (norm_nonneg _) (hLam v)) _) hS2)
            (mul_nonneg (Finset.prod_nonneg fun v _ => sq_nonneg _) hS1)
      _ = (∏ v, m v) ^ 2 * (S1 * S2) := by rw [← hM]; ring
      _ ≤ (∏ v, m v) ^ 2 * ((S1 + S2) / 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (S1 - S2)]) (sq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hM0 (by linarith)) two_ne_zero).mp hsq

theorem lagCo_ne_zero {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (j : Fin (d + 1)) :
    Formalism.FourierDecayAlt.F7.lagCo y j ≠ 0 := by
  unfold Formalism.FourierDecayAlt.F7.lagCo
  exact Finset.prod_ne_zero_iff.mpr fun i hi =>
    inv_ne_zero (sub_ne_zero.mpr (hy.ne (Finset.ne_of_mem_erase hi).symm))

theorem cg_pos {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hg : ∀ a, Function.Injective (grid a)) (a : Fin K) :
    0 < cg grid a := by
  unfold cg
  exact Finset.sum_pos' (fun i _ => abs_nonneg _)
    ⟨0, Finset.mem_univ _, abs_pos.mpr (lagCo_ne_zero (grid a) (hg a) 0)⟩

theorem co_eq {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hg : ∀ a, Function.Injective (grid a))
    (j : Fin K → Fin (d + 1)) : |coProd grid j| = (∏ a, cg grid a) * Formalism.FourierDecayAlt.F7.thGrid grid j := by
  have hc : ∀ a, ∑ i, |Formalism.FourierDecayAlt.F7.lagCo (grid a) i| ≠ 0 := fun a => (cg_pos grid hg a).ne'
  unfold coProd Formalism.FourierDecayAlt.F7.thGrid cg
  rw [Finset.abs_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  have h := hc a
  field_simp

theorem p2cOfParts_ok : LowerBlockNormalisedBoundFromComponents := by
  intro K d grid q nn w o W0 RL RV wt wt' bw Qw BB hinj hpos hQ hnn hBB hwt hwt' hbw hR H
  have hQw : K = 0 ∨ 0 ≤ Qw := by
    rcases Nat.eq_zero_or_pos K with hK | hK
    · exact Or.inl hK
    · right
      have h1 := hQ ⟨0, hK⟩ 0
      have h2 := (hpos ⟨0, hK⟩ 0).1
      have h3 := (hpos ⟨0, hK⟩ 0).2.1
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_neg_of_neg_of_pos hneg h3]
  have hZ2 : (Real.sqrt Qw * BB) ^ K * (Real.sqrt Qw * BB) ^ K = Qw ^ K * (BB ^ 2) ^ K := by
    rcases hQw with hK | hQ0
    · subst hK; simp
    · rw [← mul_pow, ← mul_pow]
      congr 1
      linear_combination (BB ^ 2) * Real.mul_self_sqrt hQ0
  have hN : ∀ j, nnProd nn 0 grid j * nnProd nn 1 grid j ≤ Qw ^ K * (BB ^ 2) ^ K * qProd q w grid j := by
    intro j
    unfold nnProd qProd
    rw [← Finset.prod_mul_distrib]
    have e : Qw ^ K * (BB ^ 2) ^ K * ∏ a, F7.qW q w (grid a (j a)) =
        ∏ a, (Qw * BB ^ 2 * F7.qW q w (grid a (j a))) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    rw [e]
    refine Finset.prod_le_prod (fun a _ => ?_) (fun a _ => ?_)
    · rw [add_zero]; exact mul_nonneg (hpos a (j a)).2.2.1.le (hpos a (j a)).2.2.2.le
    · rw [add_zero]
      have h1 := (div_le_iff₀ (hpos a (j a)).1).mp (hnn a (j a))
      have h2 := hQ a (j a)
      nlinarith [mul_nonneg (sq_nonneg BB) (sub_nonneg.mpr h2)]
  have hj : ∀ j, wt * wt' / bw * Real.sqrt (RL j * RV j / qProd q w grid j) ≤
      (Real.sqrt Qw * BB) ^ K * ((wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) +
        wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j)) / 2) := by
    intro j
    have hq0 : 0 < qProd q w grid j := Finset.prod_pos fun a _ => (hpos a (j a)).2.1
    have hN0 : 0 < nnProd nn 0 grid j := Finset.prod_pos fun a _ => by
      rw [add_zero]; exact (hpos a (j a)).2.2.1
    have hN1 : 0 < nnProd nn 1 grid j := Finset.prod_pos fun a _ => (hpos a (j a)).2.2.2
    have hX : 0 ≤ wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) :=
      div_nonneg (mul_nonneg (sq_nonneg _) (hR j).1) (mul_pos hbw hN0).le
    have hY : 0 ≤ wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j) :=
      div_nonneg (mul_nonneg (sq_nonneg _) (hR j).2) (mul_pos hbw hN1).le
    have hZ : 0 ≤ (Real.sqrt Qw * BB) ^ K := pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) hBB) K
    have hc : 0 ≤ wt ^ 2 * wt' ^ 2 * RL j * RV j / bw ^ 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hR j).1) (hR j).2)
        (sq_nonneg _)
    have hL0 : 0 ≤ wt * wt' / bw * Real.sqrt (RL j * RV j / qProd q w grid j) :=
      mul_nonneg (div_nonneg (mul_nonneg hwt hwt') hbw.le) (Real.sqrt_nonneg _)
    have e1 : (wt * wt' / bw * Real.sqrt (RL j * RV j / qProd q w grid j)) ^ 2 =
        (wt ^ 2 * wt' ^ 2 * RL j * RV j / bw ^ 2) * (1 / qProd q w grid j) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg (mul_nonneg (hR j).1 (hR j).2) hq0.le)]; ring
    have h3 : 1 / qProd q w grid j ≤ Qw ^ K * (BB ^ 2) ^ K / (nnProd nn 0 grid j * nnProd nn 1 grid j) := by
      rw [div_le_div_iff₀ hq0 (mul_pos hN0 hN1)]; linarith [hN j]
    have e2 : (Real.sqrt Qw * BB) ^ K * (Real.sqrt Qw * BB) ^ K *
        (wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) * (wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j))) =
        (wt ^ 2 * wt' ^ 2 * RL j * RV j / bw ^ 2) *
          (Qw ^ K * (BB ^ 2) ^ K / (nnProd nn 0 grid j * nnProd nn 1 grid j)) := by
      rw [hZ2]; ring
    apply (pow_le_pow_iff_left₀ hL0 (mul_nonneg hZ (by linarith)) two_ne_zero).mp
    calc (wt * wt' / bw * Real.sqrt (RL j * RV j / qProd q w grid j)) ^ 2
        = (wt ^ 2 * wt' ^ 2 * RL j * RV j / bw ^ 2) * (1 / qProd q w grid j) := e1
      _ ≤ (wt ^ 2 * wt' ^ 2 * RL j * RV j / bw ^ 2) *
          (Qw ^ K * (BB ^ 2) ^ K / (nnProd nn 0 grid j * nnProd nn 1 grid j)) :=
          mul_le_mul_of_nonneg_left h3 hc
      _ = (Real.sqrt Qw * BB) ^ K * (Real.sqrt Qw * BB) ^ K *
          (wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) * (wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j))) := e2.symm
      _ ≤ (Real.sqrt Qw * BB) ^ K * (Real.sqrt Qw * BB) ^ K *
          ((wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) + wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j)) / 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) -
            wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j))]) (mul_nonneg hZ hZ)
      _ = _ := by ring
  have hk : 0 ≤ wt * wt' / bw := div_nonneg (mul_nonneg hwt hwt') hbw.le
  have hcg0 : 0 ≤ ∏ a, cg grid a := Finset.prod_nonneg fun a _ => (cg_pos grid hinj a).le
  have hth : ∀ j, 0 ≤ F7.thGrid grid j := fun j =>
    Finset.prod_nonneg fun a _ => div_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _)
  calc ‖o‖ ^ K * (wt * wt' / bw * ‖W0‖) = wt * wt' / bw * (‖o‖ ^ K * ‖W0‖) := by ring
    _ ≤ wt * wt' / bw * ∑ j, |coProd grid j| * Real.sqrt (RL j * RV j / qProd q w grid j) :=
        mul_le_mul_of_nonneg_left H hk
    _ = (∏ a, cg grid a) * ∑ j, F7.thGrid grid j *
          (wt * wt' / bw * Real.sqrt (RL j * RV j / qProd q w grid j)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [co_eq grid hinj j]; ring
    _ ≤ (∏ a, cg grid a) * ∑ j, F7.thGrid grid j * ((Real.sqrt Qw * BB) ^ K *
          ((wt ^ 2 * RL j / (bw * nnProd nn 0 grid j) + wt' ^ 2 * RV j / (bw * nnProd nn 1 grid j)) / 2)) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hj j) (hth j)) hcg0
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

end Formalism.FourierDecayAlt.P.SecondPolynomialClauses

theorem Formalism.FourierDecayAlt.P.third_polynomial_second_of_first : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockBoundFromRecursion := by
  exact Formalism.FourierDecayAlt.P.SecondPolynomialClauses.p3bOfA_ok
theorem Formalism.FourierDecayAlt.P.unipotent_degree_three_of_clauses : Formalism.FourierDecayAlt.PairingProductCorollary.UnnormalisedLiftBoundFromComponents := by
  exact Formalism.FourierDecayAlt.P.SecondPolynomialClauses.unipotent_degree_three_of_parts
theorem Formalism.FourierDecayAlt.P.second_polynomial_first_identity : Formalism.FourierDecayAlt.PairingProductCorollary.PairingGramBound := by
  exact Formalism.FourierDecayAlt.P.SecondPolynomialClauses.second_polynomial_first_clause
theorem Formalism.FourierDecayAlt.P.third_polynomial_prime_combine : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockSeveralPlacesBound := by
  exact Formalism.FourierDecayAlt.P.SecondPolynomialClauses.third_polynomial_prime_combination
theorem Formalism.FourierDecayAlt.P.second_polynomial_third_of_parts : Formalism.FourierDecayAlt.PairingProductCorollary.LowerBlockNormalisedBoundFromComponents := by
  exact Formalism.FourierDecayAlt.P.SecondPolynomialClauses.p2cOfParts_ok

end
