import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedCompW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharValueProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesAbsNormProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdealMemIffOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitIffOrderZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleWithGivenOrdersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPiecewiseConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricSeriesMultiIndexStatement

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)

namespace GlobalTheory.TateUnr

open scoped Classical

theorem tate_unr : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ν : Chr F E) (v : Pl F),
    (∀ w ∈ aboveF (L := E) F v, UnrAt ν w) → ∀ μ : Measure (idelesAt E (evFin F v)), IsNormE E v μ →
    ∀ 𝔞 : FractionalIdeal (𝓞 E)⁰ E, 𝔞 ≠ 0 → ∀ s : ℕ, 1 ≤ s →
    ∫ l : idelesAt E (evFin F v), (if compFin F E v (l.1 : AE F E) ∈ locId v 𝔞 then
      (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ s else 0) ∂μ = unrFac ν 𝔞 (s : ℂ) v := by
  intro F E _ _ _ _ _ ν v hν μ hμ 𝔞 h𝔞 s hs
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI := hμ.1
  let N : aboveF (L := E) F v → ℂ := fun w : aboveF (L := E) F v => ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ)
  let r : aboveF (L := E) F v → ℂ := fun w : aboveF (L := E) F v => (val ν w.1 : ℂ) * (N w ^ s)⁻¹
  let a : aboveF (L := E) F v → ℤ := fun w : aboveF (L := E) F v => FractionalIdeal.count E w.1 𝔞
  let g : (aboveF (L := E) F v → ℤ) → ℂ := fun k => if (∀ i, a i ≤ k i) then ∏ i, r i ^ k i else 0
  have hN1 : ∀ w : aboveF (L := E) F v, (1 : ℝ) < ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ) := fun w => by
    exact_mod_cast one_lt_absNorm w.1
  have hN0 : ∀ w, N w ≠ 0 := fun w => by
    have := hN1 w
    simp only [N]; exact_mod_cast (by linarith : ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ) ≠ 0)
  have hr0 : ∀ w, r w ≠ 0 := fun w => mul_ne_zero (Units.ne_zero _) (inv_ne_zero (pow_ne_zero _ (hN0 w)))
  have hr1 : ∀ w, ‖r w‖ < 1 := fun w => by
    simp only [r, N, norm_mul, norm_val, one_mul, norm_inv, norm_pow, Complex.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (hN1 w) (by omega))
  obtain ⟨hsum, htsum⟩ := GlobalTheory.T.geometric_series_multi_index a r hr0 hr1

  choose b hb using GlobalTheory.T.idele_with_given_orders (E := E) v
  let U : Set (idelesAt E (evFin F v)) := {l | l.1 ∈ unitsAt E v}
  let S : (aboveF (L := E) F v → ℤ) → Set (idelesAt E (evFin F v)) := fun k => (fun l => (b k)⁻¹ * l) ⁻¹' U
  have hS : ∀ k l, l ∈ S k ↔ ordV v l = k := fun k l => by
    change ((b k)⁻¹ * l).1 ∈ unitsAt E v ↔ _
    rw [GlobalTheory.T.local_unit_iff_order_zero, ordV_mul, ordV_inv, hb, neg_add_eq_zero, eq_comm]
  have hSm : ∀ k, MeasurableSet (S k) := fun k =>
    ((isCompact_isOpen_unitsAt (E := E) v).2.preimage (continuous_const_mul _)).measurableSet
  have hSμ : ∀ k, μ (S k) = 1 := fun k => by
    change μ ((fun l => (b k)⁻¹ * l) ⁻¹' U) = 1
    rw [measure_preimage_mul]; exact hμ.2
  have hSd : Pairwise (Function.onFun Disjoint S) := fun k k' hk => by
    refine Set.disjoint_left.2 fun l h1 h2 => hk ?_
    rw [hS] at h1 h2; rw [← h1, ← h2]
  have hSc : ∀ l, ∃ k, l ∈ S k := fun l => ⟨ordV v l, (hS _ l).2 rfl⟩
  rw [GlobalTheory.T.integral_piecewise_constant μ S hSm hSd hSc hSμ g hsum _ ?_, htsum]
  ·
    rw [unrFac, Lv, ← Finset.prod_coe_sort (aboveF (L := E) F v), ← Finset.prod_coe_sort (aboveF (L := E) F v),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [locL, charFam_of_unrAt (hν w.1 w.2), eulerFac_singleton]
    have e1 : npow w.1 (-(s : ℂ)) = (N w ^ s)⁻¹ := by
      rw [npow, Complex.cpow_neg, Complex.cpow_natCast]
    have e2 : npow w.1 (-((s : ℂ) * (FractionalIdeal.count E w.1 𝔞 : ℂ))) = (N w ^ s)⁻¹ ^ a w := by
      rw [npow, show -((s : ℂ) * (FractionalIdeal.count E w.1 𝔞 : ℂ)) = ((-((s : ℤ) * a w) : ℤ) : ℂ) by push_cast; ring,
        Complex.cpow_intCast, inv_zpow', ← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    rw [e1, e2, Units.val_zpow_eq_zpow_val]
    simp only [r, a, mul_zpow]
  · intro k l hl
    rw [hS] at hl
    subst hl
    simp only [g]
    rw [GlobalTheory.T.local_ideal_mem_iff_order v 𝔞 h𝔞 l]
    split_ifs with h
    · rw [GlobalTheory.T.unramified_char_value_product ν v hν l, GlobalTheory.T.ideles_abs_norm_product v l, Complex.ofReal_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun w _ => ?_
      simp only [r]
      rw [Units.val_zpow_eq_zpow_val, mul_zpow, Complex.ofReal_zpow, Complex.ofReal_natCast]
      congr 1
      rw [inv_zpow', ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
      congr 1
      ring
    · rfl

end GlobalTheory.TateUnr

end
