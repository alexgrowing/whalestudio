import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionSelfDualWittSplitAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviDiagonalMemLatticeStabilizerOfUnits
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemUnitaryAdelicSupportedSubgro
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodPlacePointConditionTorusInverseDiagIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodPlaceShiftConditionTorusDiagIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicConditionLastTorusDiagonalIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.OneCosetGood

variable {D : D7}

theorem ell_mul {ρ : ℕ} (u : GL (Fin ρ) (AE D)) (hu : u ∈ UX D ρ) (j : Fin ρ) :
    ∑ l, ell D ρ l * u.1 l j = ell D ρ j := by
  have hu' := mem_UX.1 hu
  have hρ : 0 < ρ := Fin.pos j
  set m : Fin ρ := ⟨ρ - 1, by omega⟩ with hmdef
  have hm : m.1 + 1 = ρ := by rw [hmdef]; simp only; omega
  have hne : ∀ b : Fin ρ, b ≠ m → ¬ (b.1 + 1 = ρ) := fun b hb h => hb (Fin.ext (by rw [hmdef]; simp only; omega))
  rw [Finset.sum_eq_single m]
  · rw [show ell D ρ m = 1 from if_pos hm, one_mul]
    by_cases hj : j = m
    · rw [hj, (hu' m m).2, show ell D ρ m = 1 from if_pos hm]
    · have hlt : j < m := by
        rw [Fin.lt_iff_val_lt_val]
        have h1 := j.2
        have h2 : j.1 ≠ m.1 := fun h => hj (Fin.ext h)
        rw [hmdef] at h2 ⊢
        simp only at h2 ⊢
        omega
      rw [(hu' m j).1 hlt, show ell D ρ j = 0 from if_neg (hne j hj)]
  · intro b _ hb
    rw [show ell D ρ b = 0 from if_neg (hne b hb), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem yZero_mul {V₀ : HSp D} {ρ : ℕ} (z : Fin V₀.rank → D.host.E) (u : GL (Fin ρ) (AE D)) (hu : u ∈ UX D ρ) :
    yZero V₀ ρ z ⬝ u.1 = yZero V₀ ρ z := by
  ext k j
  simp only [yZero, zEll, Matrix.neg_mul, Matrix.neg_apply, Matrix.mul_apply, vecMulVec_apply, neg_mul,
    Finset.sum_neg_distrib, neg_inj]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ell_mul u hu j]

set_option maxHeartbeats 1000000 in

theorem cond_red : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V₀ W W₀ : HSp D) (ρ : ℕ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (z : Fin V₀.rank → D.host.E) (P : GlobalTheory.FinPl.Pl D → Prop) (r g : GA D W), r ∈ Rgrp W (xZero dW) → Cond dW p (xZero dW) (yZero V₀ ρ z) ψ P (r * g) → Cond dW p (xZero dW) (yZero V₀ ρ z) ψ P g := by
  intro D ψ V₀ W W₀ ρ dW p z P r g hr H
  have hr' : r⁻¹ ∈ Rgrp W (xZero dW) := inv_mem hr
  obtain ⟨u, hu, hru⟩ := hr
  obtain ⟨u', hu', hru'⟩ := hr'
  have hinv : mt W (r * g)⁻¹ = mt W g⁻¹ ⬝ mt W r⁻¹ := by rw [_root_.mul_inv_rev, mt_mul]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨w, a, ha, hw⟩ := H.pt
    refine ⟨⟨u' * w.1, mul_mem hu' w.2⟩, a, ha, ?_⟩
    have e : mt W (r * g)⁻¹ ⬝ (xZero dW ⬝ w.1.1) = mt W g⁻¹ ⬝ (xZero dW ⬝ (u' * w.1).1) := by
      rw [hinv, Matrix.mul_assoc, ← Matrix.mul_assoc (mt W r⁻¹), hru', Units.val_mul, Matrix.mul_assoc]
    rw [← e]; exact hw
  · intro N hN hup hmem
    have hU := mem_UX.1 (inv_mem hu')
    have h1 : MxAt P ((u'⁻¹).1 ⬝ N) := fun i j => by
      simp only [Matrix.mul_apply]
      exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hN k j)
    have h2 : ∀ i j, j ≤ i → ((u'⁻¹).1 ⬝ N) i j = 0 := by
      intro i j hij
      simp only [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k < i
      · rw [(hU i k).1 hk, zero_mul]
      · rw [hup k j (le_trans hij (not_lt.1 hk)), mul_zero]
    have h3 : mt W (r * g)⁻¹ ⬝ (xZero dW ⬝ ((u'⁻¹).1 ⬝ N)) = mt W g⁻¹ ⬝ (xZero dW ⬝ N) := by
      rw [hinv, Matrix.mul_assoc, ← Matrix.mul_assoc (mt W r⁻¹), hru']
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (u'.1) ((u'⁻¹).1) N, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    have h4 : upSum ((u'⁻¹).1 ⬝ N) = upSum N := by
      unfold upSum
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · simp only [Matrix.mul_apply]
        rw [Finset.sum_eq_single i]
        · rw [(hU i i).2, one_mul]
        · intro k _ hk
          rcases lt_or_gt_of_ne hk with hk | hk
          · rw [(hU i k).1 hk, zero_mul]
          · rw [hup k j (by rw [Fin.le_iff_val_le_val]; have := Fin.lt_iff_val_lt_val.1 hk; omega), mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rfl
    rw [← h4]
    exact H.shift _ h1 h2 (h3 ▸ hmem)
  · intro ξ hξ ξ' hP he
    have e : mt W (r * g) ⬝ dW.incX V₀ ξ = dW.incX V₀ (u.1 ⬝ ξ') := by
      rw [mt_mul, Matrix.mul_assoc, he, HypDec.incX_apply, HypDec.incX_apply, ← Matrix.mul_assoc,
        show mt W r ⬝ dW.jX = dW.jX ⬝ u.1 from hru, Matrix.mul_assoc]
    rw [← H.iso ξ hξ (u.1 ⬝ ξ') hP e]
    congr 1
    rw [GlobalTheory.OrientedHeis.symplO_skew (dW.incX V₀ ξ') (dW.incAdj V₀ _),
      GlobalTheory.OrientedHeis.symplO_skew (dW.incX V₀ (u.1 ⬝ ξ')) (dW.incAdj V₀ _), HypDec.symplO_incX_incAdj,
      HypDec.symplO_incX_incAdj, ← Matrix.mul_assoc, yZero_mul z u hu]

end GlobalTheory.OneCosetGood

namespace GlobalTheory.OneCosetGood

open GlobalTheory.FinPl (Lat idAt intAt grpAt InK)

set_option maxHeartbeats 1000000 in

theorem oneCoset_good : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (z : Fin V₀.rank → D.host.E) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → (0 < ρ → ∀ a ∈ idAt D (· = v), dW.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) (· = v) ↔ a ∈ intAt D (· = v)) → ∀ h ∈ grpAt W (· = v), (∀ κ, GlobalTheory.FinPl.InK W LW (· = v) κ → Cond dW p (xZero dW) (yZero V₀ ρ z) ψ (· = v) (h * κ)) → CosetAt W (Rgrp W (xZero dW)) LW v h := by
  intro D ψ hψ V V₀ W W₀ ρ dV dW p z LV LV₀ LW LW₀ v hG hS hlast h hh hC
  obtain ⟨n, hnN, hnG, t, ht, htG, γ, hγ, κ, hκ, rfl⟩ :=
    GlobalTheory.IwaPlace.iwasawa_at_place D W W₀ ρ dW LW LW₀ v (GlobalTheory.FinPl.TamePlaces.tame D v) hG.sdW hG.sdW₀ hG.monoW h hh
  have hR : Rgrp W (xZero dW) = jacGrp dW := (GlobalTheory.Unf.base_point D W W₀ ρ dW).2.2.2.1
  have hr : n * dW.emb0 γ ∈ Rgrp W (xZero dW) := by
    rw [hR]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hnN) (Subgroup.mem_sup_right ⟨γ, rfl⟩)
  have heq : n * dW.levi t * dW.emb0 γ * κ * κ⁻¹ = n * dW.emb0 γ * dW.levi t := by
    rw [mul_inv_cancel_right, mul_assoc n, ← dW.wittHyperbolic_anisotropic_commute_levi, mul_assoc]
  have hc := cond_red D ψ V₀ W W₀ ρ dW p z (· = v) _ _ hr (heq ▸ hC κ⁻¹ (inK_inv hκ))
  have hinv := GlobalTheory.T.goodPlace_pointCondition_torus_inverseDiag_integral D ψ hψ V V₀ W W₀ ρ dV dW p LV LV₀ LW LW₀ v hG hS t ht htG hc.pt
  have hint : ∀ i : Fin ρ, t.1 i i - 1 ∈ intAt D (· = v) := by
    intro i
    by_cases hi : i.1 + 1 < ρ
    · exact GlobalTheory.T.goodPlace_shiftCondition_torus_diag_integral D ψ hψ V V₀ W W₀ ρ dV dW p LV LV₀ LW LW₀ v hG hS t ht htG hc.shift i ⟨i.1 + 1, hi⟩ rfl
    · exact GlobalTheory.T.isotropic_condition_last_torus_diagonal_integral D ψ hψ V V₀ W W₀ ρ dV dW p z LV LV₀ LW LW₀ v hG hS hlast t ht htG hc.iso i (by omega)
  have hK := GlobalTheory.FinPl.LeviUnitK.inK_levi D W W₀ ρ dW LW LW₀ v hG.sdW hG.monoW t ht htG (fun i => ⟨hint i, hinv i⟩)
  refine ⟨n * dW.emb0 γ, hr, ?_, dW.levi t * κ, inK_mul hK hκ, ?_⟩
  · exact Subgroup.mul_mem _ hnG (GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup D W W₀ ρ dW (· = v) γ hγ)
  · rw [mul_assoc n (dW.levi t), ← dW.wittHyperbolic_anisotropic_commute_levi γ t]
    simp only [mul_assoc]

end GlobalTheory.OneCosetGood

end
