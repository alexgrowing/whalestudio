import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
open MeasureTheory Topology GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold
open scoped ENNReal

namespace GlobalTheory

open MeasureTheory Topology in
open scoped ENNReal in

theorem _root_.GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction :
    ∀ (T T' : Type) [Group T] [MeasurableSpace T] [MeasurableMul₂ T] [Group T'] [MeasurableSpace T']
      [MeasurableMul T'] [MeasurableInv T'] (j : T' →* T), Measurable j →
      ∀ (m : Measure T) [SFinite m] [m.IsMulLeftInvariant] (m' : Measure T') [SFinite m']
        [m'.IsMulRightInvariant] [m'.IsInvInvariant] (b : T → ℝ≥0∞), Measurable b →
        (∀ t, ∫⁻ s, b (j s * t) ∂m' = 1) → ∃ ν, _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.IsQuotientMeasure j m' m ν := by
  intro T T' _ _ _ _ _ _ _ j hj m _ _ m' _ _ _ b hb hint
  refine ⟨(m.withDensity b).map (Quotient.mk'' : T → _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j), ?_⟩
  intro f hf
  set F : T → ℝ≥0∞ := fun t => ∫⁻ s, f (j s * t) ∂m' with hFdef
  have hF : Measurable F := by
    have hprod : Measurable fun p : T × T' => f (j p.2 * p.1) :=
      hf.comp ((hj.comp measurable_snd).mul measurable_fst)
    exact hprod.lintegral_prod_right'
  have hG : ∀ t : T,
      ∫⁻ s, f (j s * Quotient.out (Quotient.mk'' t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j)) ∂m' = F t := by
    intro t
    have hrel := Quotient.mk_out (s := QuotientGroup.rightRel j.range) t
    obtain ⟨u, hu⟩ := QuotientGroup.rightRel_apply.mp hrel
    have ht : t = j u * Quotient.out (Quotient.mk'' t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j) := by
      change t = j u * Quotient.out (Quotient.mk (QuotientGroup.rightRel j.range) t)
      rw [hu, inv_mul_cancel_right]
    simp only [hFdef]
    conv_rhs => rw [ht]
    simp_rw [← mul_assoc, ← map_mul]
    exact (lintegral_mul_right_eq_self
      (fun s => f (j s * Quotient.out (Quotient.mk'' t : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j))) u).symm
  set G : _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j → ℝ≥0∞ := fun c => ∫⁻ s, f (j s * Quotient.out c) ∂m' with hGdef
  have hGmeas : Measurable G := by
    refine (measurable_from_quotient (s := QuotientGroup.rightRel j.range)).mpr ?_
    convert hF using 1
    funext t
    exact hG t
  have key : ∫⁻ t, f t ∂m = ∫⁻ t, b t * F t ∂m := by
    calc ∫⁻ t, f t ∂m = ∫⁻ t, (∫⁻ s, b (j s * t) ∂m') * f t ∂m :=
          lintegral_congr fun t => by rw [hint t, one_mul]
      _ = ∫⁻ t, ∫⁻ s, b (j s * t) * f t ∂m' ∂m :=
          lintegral_congr fun t => (lintegral_mul_const _ (hb.comp (hj.mul_const t))).symm
      _ = ∫⁻ s, ∫⁻ t, b (j s * t) * f t ∂m ∂m' :=
          lintegral_lintegral_swap
            ((hb.comp ((hj.comp measurable_snd).mul measurable_fst)).mul
              (hf.comp measurable_fst)).aemeasurable
      _ = ∫⁻ s, ∫⁻ t, b t * f (j s⁻¹ * t) ∂m ∂m' := lintegral_congr fun s => by
          have h := lintegral_mul_left_eq_self (μ := m) (fun t => b t * f (j s⁻¹ * t)) (j s)
          simp only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at h
          exact h
      _ = ∫⁻ t, ∫⁻ s, b t * f (j s⁻¹ * t) ∂m' ∂m :=
          lintegral_lintegral_swap
            ((hb.comp measurable_snd).mul
              (hf.comp ((hj.comp measurable_fst.inv).mul measurable_snd))).aemeasurable
      _ = ∫⁻ t, b t * F t ∂m := lintegral_congr fun t => by
          have hmeas : Measurable fun s : T' => f (j s⁻¹ * t) :=
            hf.comp ((hj.comp measurable_inv).mul_const t)
          rw [lintegral_const_mul _ hmeas]
          congr 1
          exact lintegral_inv_eq_self (fun s => f (j s * t))
  calc ∫⁻ t, f t ∂m = ∫⁻ t, b t * F t ∂m := key
    _ = ∫⁻ t, b t * G (Quotient.mk'' t) ∂m := lintegral_congr fun t => by rw [← hG t]
    _ = ∫⁻ t, G (Quotient.mk'' t) ∂(m.withDensity b) :=
        (lintegral_withDensity_eq_lintegral_mul _ hb (hGmeas.comp measurable_quotient_mk'')).symm
    _ = ∫⁻ c, G c ∂((m.withDensity b).map (Quotient.mk'' : T → _root_.GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold.RightCosets j)) :=
        (lintegral_map hGmeas measurable_quotient_mk'').symm

end GlobalTheory
