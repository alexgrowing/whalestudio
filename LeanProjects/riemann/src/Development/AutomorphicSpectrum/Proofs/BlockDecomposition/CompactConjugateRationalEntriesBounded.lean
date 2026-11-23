import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.GrowthEntries

open GlobalTheory.CompanionTheory.BoxBound

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem norm_entry_le_toL (A : Matrix (Fin a) (Fin a) (Cinf E)) (i j : Fin a) (w : InfinitePlace E) :
    ‖A i j w‖ ≤ ‖toL A‖ :=
  (norm_le_pi_norm (A i j) w).trans
    ((norm_le_pi_norm (toL A i) j).trans (norm_le_pi_norm (toL A) i))

theorem norm_toL_le_height (y : GL (Fin a) (Cinf E)) : ‖toL y.val‖ ≤ height y := by
  have := norm_nonneg (toL (y⁻¹).val)
  unfold height
  linarith

theorem norm_toL_inv_le_height (y : GL (Fin a) (Cinf E)) : ‖toL (y⁻¹).val‖ ≤ height y := by
  have := norm_nonneg (toL y.val)
  unfold height
  linarith

theorem norm_toL_mul_le_of_le {u v : GL (Fin a) (Cinf E)} {p r : ℝ} (hu : ‖toL u.val‖ ≤ p)
    (hv : ‖toL v.val‖ ≤ r) : ‖toL (u * v).val‖ ≤ a * (p * r) :=
  (norm_toL_mul_le u.val v.val).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hu hv (norm_nonneg _) ((norm_nonneg _).trans hu)) (Nat.cast_nonneg a))

theorem gFin_mul (g h : GA E a) : gFin (g * h) = gFin g * gFin h := map_mul _ g h

theorem gFin_inv (g : GA E a) : gFin g⁻¹ = (gFin g)⁻¹ := map_inv _ g

theorem gFin_zpow (g : GA E a) (n : ℤ) : gFin (g ^ n) = gFin g ^ n := map_zpow _ g n

theorem gInf_mul (g h : GA E a) : gInf (g * h) = gInf g * gInf h := map_mul _ g h

theorem gInf_inv (g : GA E a) : gInf g⁻¹ = (gInf g)⁻¹ := map_inv _ g

theorem gFin_splitCentre (t : ℝ) : gFin (splitCentre E a t) = 1 := pFin_infGL _

theorem exists_bound_splitCentre (n₀ : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ m : ℤ, |m| ≤ n₀ →
    ‖toL (gInf (splitCentre E a 1 ^ m)).val‖ ≤ B := by
  refine ⟨∑ m ∈ Finset.Icc (-(n₀ : ℤ)) n₀, ‖toL (gInf (splitCentre E a 1 ^ m)).val‖,
    Finset.sum_nonneg fun _ _ => norm_nonneg _, fun m hm => ?_⟩
  exact Finset.single_le_sum (f := fun m : ℤ => ‖toL (gInf (splitCentre E a 1 ^ m)).val‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_Icc.2 (abs_le.1 hm))

theorem place_eq_norm_pInf (x : E) (w : InfinitePlace E) :
    w x = ‖pInf E (algebraMap E (Ad E) x) w‖ := by
  rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq]

theorem entries_bound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (g₀ : GA E a)
    (Q : Set (GA E a)), IsCompact Q → ∀ n₀ : ℕ, ∃ (Qf : Set (Af E)) (C : ℝ), IsCompact Qf ∧ 0 ≤ C ∧
      ∀ (y : GL (Fin a) (Cinf E)) (γ : GL (Fin a) E) (n : ℤ), |n| ≤ n₀ →
        (g₀ * infGL E a y)⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * (g₀ * infGL E a y) ∈ Q →
        ∀ i j, algebraMap E (Af E) (γ.val i j) ∈ Qf ∧ ∀ w : InfinitePlace E, w (γ.val i j) ≤ C * height y ^ 2 := by
  intro E _ _ _ a g₀ Q hQ n₀
  have hK : IsCompact ((fun q : GA E a => gFin g₀ * gFin q * (gFin g₀)⁻¹) '' Q) :=
    hQ.image ((continuous_const.mul continuous_gFin).mul continuous_const)
  have hent : ∀ i j : Fin a, Continuous fun g : GL (Fin a) (Af E) => g.val i j := fun i j =>
    (Units.continuous_val : Continuous fun g : GL (Fin a) (Af E) => (g.val : Matrix (Fin a) (Fin a) (Af E))).matrix_elem i j
  obtain ⟨B, hB0, hB⟩ := exists_height_bound (E := E) (a := a) hQ
  obtain ⟨Z, hZ0, hZ⟩ := exists_bound_splitCentre (E := E) (a := a) n₀
  set g1 : ℝ := ‖toL (gInf g₀).val‖ with hg1
  set g2 : ℝ := ‖toL ((gInf g₀)⁻¹).val‖ with hg2
  have hg10 : 0 ≤ g1 := norm_nonneg _
  have hg20 : 0 ≤ g2 := norm_nonneg _
  refine ⟨⋃ i, ⋃ j, (fun g : GL (Fin a) (Af E) => g.val i j) '' ((fun q : GA E a => gFin g₀ * gFin q * (gFin g₀)⁻¹) '' Q),
    (a : ℝ) ^ 5 * (g1 * g2 * B * Z),
    isCompact_iUnion fun i => isCompact_iUnion fun j => hK.image (hent i j),
    mul_nonneg (pow_nonneg (Nat.cast_nonneg a) 5) (mul_nonneg (mul_nonneg (mul_nonneg hg10 hg20) hB0) hZ0), ?_⟩
  intro y γ n hn hq i j
  set X : GA E a := g₀ * infGL E a y with hX
  set q : GA E a := X⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * X with hqdef
  have h1 : ratGL E a γ * splitCentre E a 1 ^ n = X * q * X⁻¹ := by
    rw [hqdef]; group
  have hfin : gFin (ratGL E a γ) = gFin g₀ * gFin q * (gFin g₀)⁻¹ := by
    have e1 : gFin X = gFin g₀ := by
      rw [hX, gFin_mul, show gFin (infGL E a y) = 1 from pFin_infGL y, mul_one]
    have e2 : gFin (splitCentre E a 1 ^ n) = 1 := by
      rw [gFin_zpow, gFin_splitCentre, _root_.one_zpow]
    have h := congrArg gFin h1
    rw [gFin_mul, e2, mul_one, gFin_mul, gFin_mul, gFin_inv, e1] at h
    exact h
  have hinf : gInf (ratGL E a γ) =
      gInf g₀ * y * gInf q * y⁻¹ * (gInf g₀)⁻¹ * gInf (splitCentre E a 1 ^ (-n)) := by
    have h2 : ratGL E a γ = X * q * X⁻¹ * splitCentre E a 1 ^ (-n) := by
      rw [← h1, _root_.zpow_neg, mul_inv_cancel_right]
    have e1 : gInf X = gInf g₀ * y := by
      rw [hX, gInf_mul, show gInf (infGL E a y) = y from pInf_infGL y]
    have h := congrArg gInf h2
    rw [gInf_mul, gInf_mul, gInf_mul, gInf_inv, e1] at h
    rw [h]
    group
  refine ⟨?_, fun w => ?_⟩
  · refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
    exact ⟨gFin (ratGL E a γ), ⟨q, hq, hfin.symm⟩, rfl⟩
  · have hy := norm_toL_le_height y
    have hy' := norm_toL_inv_le_height y
    have hR : ‖toL (gInf q).val‖ ≤ B := (norm_toL_le_height _).trans (hB q hq)
    have hZn : ‖toL (gInf (splitCentre E a 1 ^ (-n))).val‖ ≤ Z := hZ (-n) (by rwa [abs_neg])
    have hM := norm_toL_mul_le_of_le (norm_toL_mul_le_of_le (norm_toL_mul_le_of_le
      (norm_toL_mul_le_of_le (norm_toL_mul_le_of_le (le_refl g1) hy) hR) hy') (le_refl g2)) hZn
    rw [← hinf] at hM
    rw [place_eq_norm_pInf]
    have he : ‖pInf E (algebraMap E (Ad E) (γ.val i j)) w‖ ≤ ‖toL (gInf (ratGL E a γ)).val‖ :=
      norm_entry_le_toL (gInf (ratGL E a γ)).val i j w
    refine he.trans (hM.trans_eq ?_)
    ring

end GlobalTheory.CompanionTheory.GrowthEntries

end
