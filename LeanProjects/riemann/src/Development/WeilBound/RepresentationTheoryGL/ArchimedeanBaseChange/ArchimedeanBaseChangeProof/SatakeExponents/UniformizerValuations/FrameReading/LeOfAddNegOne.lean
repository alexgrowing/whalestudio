import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueCardEqAbsNormStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Tail.PExp.DlB

theorem pair_sum (N : ℕ) (x : Fin N → ℤ) :
    ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (x i - x j) =
      ∑ i : Fin N, ((N : ℤ) - 1 - 2 * (i : ℕ)) * x i := by
  have hswap : ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), x j =
      ∑ j : Fin N, ∑ i ∈ Finset.univ.filter (fun i => i < j), x j :=
    Finset.sum_comm' (fun i j => by simp)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hswap]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc1 : (Finset.univ.filter (fun j => i < j)).card = N - 1 - i := by
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  have hc2 : (Finset.univ.filter (fun j => j < i)).card = i := by
    rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
  rw [hc1, hc2]
  have hi := i.isLt
  have h : (((N - 1 - (i : ℕ) : ℕ)) : ℤ) = (N : ℤ) - 1 - (i : ℕ) := by omega
  rw [h]
  ring

theorem prod_zpow' (a : ℝ) (ha : a ≠ 0) {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ ha, ih]

theorem le_ofAdd_neg_one (b : WithZero (Multiplicative ℤ)) (h : b < 1) :
    b ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  induction b using WithZero.recZeroCoe with
  | zero => exact zero_le
  | coe a =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
    rw [WithZero.coe_le_coe]
    have h' : Multiplicative.toAdd a < 0 := h
    show Multiplicative.toAdd a ≤ -1
    omega

theorem unif_of_ordL (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (h : ordL (ϖ : w.adicCompletion E) = 1) :
    valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) = uniformizer (w.adicCompletion E) := by
  set K := w.adicCompletion E
  have hv : Valued.v (ϖ : K) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    unfold ordL at h
    split_ifs at h with h0
    · exact absurd h (by norm_num)
    rw [← WithZero.coe_unzero h0]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    omega
  have key : ∀ a b : K, valuation K a ≤ valuation K b ↔ Valued.v a ≤ Valued.v b := fun a b =>
    (Valuation.Compatible.vle_iff_le (v := valuation K) a b).symm.trans Iff.rfl
  have hlt : ∀ a : K, valuation K a < 1 ↔ Valued.v a < 1 := fun a => by
    rw [← map_one (valuation K), ← map_one (Valued.v : Valuation K (WithZero (Multiplicative ℤ))),
      lt_iff_not_ge, lt_iff_not_ge, key]
  apply le_antisymm
  · rw [le_uniformizer_iff, hlt, hv, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero,
      Multiplicative.ofAdd_lt]
    norm_num
  · obtain ⟨a, ha⟩ := valuation_surjective (uniformizer K)
    have h1 : valuation K a < 1 := ha ▸ uniformizer_lt_one
    rw [← ha, key, hv]
    exact le_ofAdd_neg_one _ ((hlt a).1 h1)

end PositivityTheory.Rg.BcB.F.Tail.PExp.DlB

namespace PositivityTheory.Rg.BcB.F.Tail.PExp

open DlB in
theorem dlBridge' : DlBridge := by
  intro E _ _ _ w ϖ hord
  have hu := unif_of_ordL E w ϖ hord
  refine ⟨hu, fun N x => ?_⟩
  set q : ℝ := ((qV E w : ℕ) : ℝ) with hq
  have hn : nabs (w.adicCompletion E) ϖ = q⁻¹ := by
    rw [GlobalTheory.GLDoubling.nabs_unif hu, GlobalTheory.T.residue_card_eq_abs_norm]
    rfl
  have hqpos : 0 < q := by
    have := nabs_pos' (w.adicCompletion E) ϖ
    rw [hn] at this
    exact inv_pos.1 this
  have hz : ∀ n : ℤ, nabs (w.adicCompletion E) (ϖ ^ n) = q ^ (-n) := by
    intro n
    have h2 := hn
    unfold nabs at h2 ⊢
    rw [map_zpow, NNReal.coe_zpow, h2, _root_.inv_zpow']
  set S : ℤ := ∑ i : Fin N, ((N : ℤ) - 1 - 2 * (i : ℕ)) * x i with hS
  have hdB : deltaB (fun i => ϖ ^ x i) = q ^ (-S) := by
    unfold deltaB
    have e1 : ∀ i j : Fin N, nabs (w.adicCompletion E) (ϖ ^ x i / ϖ ^ x j) = q ^ (-(x i - x j)) := fun i j => by
      rw [show ϖ ^ x i / ϖ ^ x j = ϖ ^ (x i - x j) by rw [_root_.zpow_sub, div_eq_mul_inv], hz]
    simp only [e1]
    rw [Finset.prod_congr rfl fun i _ => prod_zpow' q hqpos.ne' _ _, prod_zpow' q hqpos.ne',
      hS, ← pair_sum]
    congr 1
    simp only [Finset.sum_neg_distrib]
  have hdH : (deltaHalf (w.adicCompletion E) (fun _ : Fin N => Unit) (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i) : ℂ) =
      ((√(deltaB (fun i => ϖ ^ x i)) : ℝ) : ℂ) := by
    rw [val_deltaHalf, deltaB_eq_modulus]
  rw [hdH, hdB]
  set r : ℝ := √q with hr
  have hrpos : 0 < r := Real.sqrt_pos.2 hqpos
  have e : q ^ (-S) = (r ^ (-S)) ^ 2 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hr, Real.sq_sqrt hqpos.le]
  have hqh : GlobalTheory.BCT.qh w = (r : ℂ) := rfl
  rw [hqh, e, Real.sqrt_sq (zpow_nonneg hrpos.le _), ← Complex.ofReal_mul, ← Complex.ofReal_zpow]
  congr 1
  rw [← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_neg, ← zpow_add₀ hrpos.ne']
  congr 1
  push_cast
  ring

end PositivityTheory.Rg.BcB.F.Tail.PExp

end
