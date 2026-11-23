import Mathlib
import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
import Formalism.GaussJetBounds.Statement

open scoped BigOperators

namespace UpperTheory.ColumnLengthWeights

open Formalism.MainNotions.product_zeroth_first_parts

private theorem card_eq_sum_colLen (μ : YoungDiagram) :
    μ.cells.card = ∑ c : Fin (μ.rowLen 0), μ.colLen c := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.range (μ.rowLen 0))]
  · rw [← Fin.sum_univ_eq_sum_range (fun j => (μ.cells.filter fun c => c.2 = j).card)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [YoungDiagram.colLen_eq_card]
    rfl
  · rintro ⟨i, j⟩ h
    rw [Finset.mem_coe, Finset.mem_range]
    have h0 : (0, j) ∈ μ := μ.up_left_mem (Nat.zero_le i) le_rfl (Finset.mem_coe.mp h)
    exact YoungDiagram.mem_iff_lt_rowLen.mp h0

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) (a : Lt → ℕ)

private def wt : XZ Lt N0 N1 → ℕ := Sum.elim (fun _ => 0) (fun z => a z.1)

omit [Fintype Lt] [DecidableEq Lt] in
private theorem minorXZ_hom (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) :
    MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a) (minorXZ N0 N1 s p I) (p • a s) := by
  have hent : ∀ i k : Fin p, MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a)
      (∑ b : Fin N0, MvPolynomial.X (Sum.inl (s, (i : ℕ), b)) * MvPolynomial.X (Sum.inr (s, b, I k)) :
        MvPolynomial (XZ Lt N0 N1) ℤ) (a s) := by
    intro i k
    refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    have := (MvPolynomial.isWeightedHomogeneous_X ℤ (wt N0 N1 a) (Sum.inl (s, (i : ℕ), b))).mul
      (MvPolynomial.isWeightedHomogeneous_X ℤ (wt N0 N1 a) (Sum.inr (s, b, I k)))
    simpa only [wt, Sum.elim_inl, Sum.elim_inr, zero_add] using this
  unfold minorXZ
  rw [Matrix.det_apply]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  rw [Units.smul_def]
  apply Submodule.smul_mem (MvPolynomial.weightedHomogeneousSubmodule ℤ (wt N0 N1 a) _)
  have := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ (fun _ => a s)
    (fun i _ => hent (σ i) i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at this
  exact this

omit [DecidableEq Lt] in
private theorem Gxz_hom (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) :
    MvPolynomial.IsWeightedHomogeneous (wt N0 N1 a) (Gxz N0 N1 nu I)
      (∑ s, (nu s).cells.card • a s) := by
  unfold Gxz
  have h := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun s => ∏ c : Fin ((nu s).rowLen 0), minorXZ N0 N1 s ((nu s).colLen (c : ℕ)) (I s c))
    (fun s => ∑ c : Fin ((nu s).rowLen 0), (nu s).colLen (c : ℕ) • a s)
    (fun s _ => MvPolynomial.IsWeightedHomogeneous.prod Finset.univ _ _
      (fun c _ => minorXZ_hom N0 N1 a s _ (I s c)))
  convert h using 2 with s
  rw [← Finset.sum_smul, card_eq_sum_colLen]

private theorem deg_of_mem_support (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) (μ : XZ Lt N0 N1 →₀ ℕ)
    (hμ : μ ∈ (Gxz N0 N1 nu I).support) (t : Lt) :
    ∑ ab : Fin N0 × Fin N1, (Finsupp.sumFinsuppEquivProdFinsupp μ).2 (t, ab) = (nu t).cells.card := by
  classical
  set a : Lt → ℕ := fun z => if z = t then 1 else 0 with ha
  have hw := Gxz_hom N0 N1 a nu I (MvPolynomial.mem_support_iff.mp hμ)
  have hr : ∑ s, (nu s).cells.card • a s = (nu t).cells.card := by
    rw [Finset.sum_eq_single t]
    · simp [ha]
    · intro b _ hb
      simp [ha, hb]
    · simp
  set T : Finset (XZ Lt N0 N1) := Finset.univ.map
    ⟨fun ab : Fin N0 × Fin N1 => (Sum.inr (t, ab) : XZ Lt N0 N1), fun x y h => by simpa using h⟩ with hT
  have hwt : Finsupp.weight (wt N0 N1 a) μ = ∑ ab : Fin N0 × Fin N1, μ (Sum.inr (t, ab)) := by
    rw [Finsupp.weight_apply,
      Finsupp.sum_of_support_subset μ (Finset.subset_union_left (s₂ := T)) _ (by simp)]
    rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := μ.support) (s₂ := T))]
    · rw [hT, Finset.sum_map]
      refine Finset.sum_congr rfl fun ab _ => ?_
      change μ (Sum.inr (t, ab)) • wt N0 N1 a (Sum.inr (t, ab)) = μ (Sum.inr (t, ab))
      simp [wt, ha]
    · intro x _ hx
      cases x with
      | inl y => simp [wt]
      | inr z =>
        obtain ⟨t', ab⟩ := z
        have hne : t' ≠ t := by
          rintro rfl
          exact hx (Finset.mem_map.mpr ⟨ab, Finset.mem_univ _, rfl⟩)
        simp [wt, ha, hne]
  simp only [Finsupp.snd_sumFinsuppEquivProdFinsupp]
  rw [← hwt, hw, hr]

end UpperTheory.ColumnLengthWeights

open UpperTheory.ColumnLengthWeights in
theorem UpperTheory.kvalGe_of_norm_mfact_mul_coeff_le :
    ∀ (l : ℕ) [Fact l.Prime] (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (B : ℝ),
    (∀ κ : Lt × Fin N0 × Fin N1 →₀ ℕ, (∀ t, ∑ ab : Fin N0 × Fin N1, κ (t, ab) = (nu t).cells.card) →
      ‖((Formalism.DworkPowerSeriesWeights.mfact κ : ℕ) : ℂ_[l]) * MvPowerSeries.coeff κ Th‖ ≤ (l : ℝ) ^ (-B)) →
    Formalism.MainNotions.product_zeroth_first_parts.KvalGe N0 N1 l nu Th B := by
  intro l _ Lt _ _ N0 N1 nu Th B h I m
  classical
  have hpos : (0 : ℝ) ≤ (l : ℝ) ^ (-B) := Real.rpow_nonneg (Nat.cast_nonneg l) _
  unfold Formalism.MainNotions.product_zeroth_first_parts.applyAt0
  rw [MvPolynomial.coeff_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hpos fun μ hμ => ?_
  rw [MvPolynomial.coeff_monomial]
  split_ifs with hm
  · have h1 := h _ (deg_of_mem_support N0 N1 nu I μ hμ)
    have h2 : ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) =
        ((Formalism.DworkPowerSeriesWeights.mfact (Finsupp.sumFinsuppEquivProdFinsupp μ).2 : ℕ) : ℂ_[l]) := by
      unfold Formalism.DworkPowerSeriesWeights.mfact Finsupp.prod
      rw [Nat.cast_prod]
    rw [h2, mul_assoc, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _)).trans h1
  · rw [norm_zero]; exact hpos
