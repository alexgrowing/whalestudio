import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHVolP
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.VolUDensity
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.UnGrpHaarProbExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.BridgeA

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.GV

abbrev εT (k : ℕ) : Fin k → Bool := fun _ => true

theorem mem_iff (k : ℕ) (g : (Matrix (Fin k) (Fin k) ℂ)ˣ) :
    g ∈ Formalism.REAL.UJ (εT k) ↔ g ∈ ReciprocityTheory.ChartRestriction.DS.UNgrp k := Iff.rfl

theorem ujEq (k : ℕ) : Formalism.REAL.UJ (εT k) = ReciprocityTheory.ChartRestriction.DS.UNgrp k := Subgroup.ext (mem_iff k)

def eU (k : ℕ) : ↥(Formalism.REAL.UJ (εT k)) ≃* ↥(ReciprocityTheory.ChartRestriction.DS.UNgrp k) := MulEquiv.subgroupCongr (ujEq k)

theorem eU_val (k : ℕ) (g : ↥(Formalism.REAL.UJ (εT k))) : ((eU k g : (Matrix (Fin k) (Fin k) ℂ)ˣ)) = g := rfl

theorem cont_eU (k : ℕ) : Continuous (eU k) := continuous_induced_rng.2 continuous_subtype_val
theorem cont_eU_symm (k : ℕ) : Continuous (eU k).symm := continuous_induced_rng.2 continuous_subtype_val

def hU (k : ℕ) : ↥(Formalism.REAL.UJ (εT k)) ≃ₜ ↥(ReciprocityTheory.ChartRestriction.DS.UNgrp k) :=
  { (eU k).toEquiv with continuous_toFun := cont_eU k, continuous_invFun := cont_eU_symm k }

instance compact (k : ℕ) : CompactSpace ↥(Formalism.REAL.UJ (εT k)) := by
  have := ReciprocityTheory.ChartRestriction.DS.unGrp_compactSpace k
  exact (hU k).symm.compactSpace

end Formalism.L2.SG.Pf.GV

namespace Formalism.L2.SG.Pf.GV

open Formalism.MainNotions.S

variable {k : ℕ}

def RLk : Matrix (Fin k) (Fin k) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin k × Fin k × Bool) where
  toFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  map_add' X Y := by
    ext p
    rcases p with ⟨i, j, b⟩
    cases b <;> simp [realifyFun]
  map_smul' c X := by
    ext p
    rcases p with ⟨i, j, b⟩
    cases b <;> simp [realifyFun]

theorem unrealify_RLk (X : Matrix (Fin k) (Fin k) ℂ) : unrealify (RLk X) = X := by
  ext i j
  apply Complex.ext <;> simp [RLk, unrealify, realifyFun]

theorem RLk_injective : Function.Injective (RLk (k := k)) := by
  intro X Y h
  rw [← unrealify_RLk X, ← unrealify_RLk Y, h]

theorem RLk_sq (M : Matrix (Fin k) (Fin k) ℂ) : ‖RLk M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp [RLk, realifyFun, sq_abs]
  ring

def skewH (k : ℕ) : Submodule ℝ (Matrix (Fin k) (Fin k) ℂ) where
  carrier := {X | Xᴴ = -X}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.conjTranspose_add, hX, hY, neg_add]
  zero_mem' := by simp
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at *
    rw [← Complex.coe_smul, Matrix.conjTranspose_smul, hX, Complex.star_def, Complex.conj_ofReal, smul_neg]

theorem lieOf_U : lieOf {g : Matrix (Fin k) (Fin k) ℂ | Formalism.REAL.inUJ (εT k) g} = (skewH k : Set (Matrix (Fin k) (Fin k) ℂ)) := by
  have hJ : Formalism.REAL.Jm (εT k) = 1 := by
    unfold Formalism.REAL.Jm; ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]
  ext X
  simp only [lieOf, Set.mem_setOf_eq, Formalism.REAL.inUJ, hJ, Matrix.mul_one, SetLike.mem_coe]
  constructor
  · intro h
    show Xᴴ = -X
    apply Formalism.MainNotions.BridgeCSB.exp_smul_inj
    intro t
    have h1 := h t
    have hinv : (NormedSpace.exp ((t : ℂ) • X))ᴴ = (NormedSpace.exp ((t : ℂ) • X))⁻¹ :=
      (Matrix.inv_eq_left_inv h1).symm
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      ← Matrix.exp_neg, ← smul_neg] at hinv
    exact hinv
  · intro hX t
    show (NormedSpace.exp ((t : ℂ) • X))ᴴ * NormedSpace.exp ((t : ℂ) • X) = 1
    have hX' : Xᴴ = -X := hX
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, hX',
      smul_neg, ← Matrix.exp_add_of_commute _ _ ((Commute.refl ((t : ℂ) • X)).neg_left), neg_add_cancel,
      NormedSpace.exp_zero]

theorem gLie_eq : Gauge.gLie (εT k) = (skewH k).map RLk := by
  unfold Gauge.gLie lieE
  rw [lieOf_U]
  have : (fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' (skewH k : Set (Matrix (Fin k) (Fin k) ℂ)) =
      (RLk : Matrix (Fin k) (Fin k) ℂ → _) '' (skewH k : Set (Matrix (Fin k) (Fin k) ℂ)) := rfl
  rw [this, Submodule.span_image, Submodule.span_eq]

end Formalism.L2.SG.Pf.GV

namespace Formalism.L2.SG.Pf.GV

open Formalism.MainNotions.S ReciprocityTheory.ChartRestriction.DS

variable {k : ℕ}

def Bρ (k : ℕ) (ρ : ℝ) : Set (UCo k) := {x | ‖RLk (skMat x)‖ < ρ}

theorem skMat_mem (x : UCo k) : skMat x ∈ skewH k := by
  show (skMat x)ᴴ = -skMat x
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, skMat]
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h, h.ne, h.ne', not_lt.2 h.le]
  · simp
  · simp [h, h.ne, h.ne', not_lt.2 h.le]

theorem expSet_eq (ρ : ℝ) :
    Gauge.expSet (εT k) (Metric.ball 0 ρ) = (eU k) ⁻¹' (volUSet (Bρ k ρ)) := by
  ext g
  simp only [Gauge.expSet, Set.mem_preimage, volUSet, Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right, Bρ]
  constructor
  · rintro ⟨Y, hY, hg⟩
    have hY2 : (Y : EuclideanSpace ℝ (Fin k × Fin k × Bool)) ∈ (skewH k).map RLk := by rw [← gLie_eq]; exact Y.2
    obtain ⟨X, hX, hXY⟩ := hY2
    refine ⟨PolarCoordinateComparison.coords X, ?_, ?_⟩
    · rw [PolarCoordinateComparison.skMat_coords X hX, hXY]; exact hY
    · show uMat g = _
      rw [hg, ← hXY, unrealify_RLk, PolarCoordinateComparison.skMat_coords X hX]
  · rintro ⟨x, hx, hg⟩
    have hmem : RLk (skMat x) ∈ Gauge.gLie (εT k) := by rw [gLie_eq]; exact ⟨skMat x, skMat_mem x, rfl⟩
    refine ⟨⟨RLk (skMat x), hmem⟩, hx, ?_⟩
    show uMat g = _
    rw [unrealify_RLk]; exact hg

def skL (k : ℕ) : UCo k →ₗ[ℝ] Matrix (Fin k) (Fin k) ℂ where
  toFun := skMat
  map_add' x y := by
    ext a b
    simp only [skMat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> (try push_cast) <;> (try simp [star_add]) <;> (try ring)
  map_smul' c x := by
    ext a b
    show skMat (c • x) a b = c • skMat x a b
    unfold skMat
    split_ifs <;> (try simp [Complex.real_smul]) <;> (try ring)

theorem finrank_gLie : Module.finrank ℝ ↥(Gauge.gLie (εT k)) =
    k + 2 * Fintype.card {ab : Fin k × Fin k // ab.2 < ab.1} := by
  rw [gLie_eq, ← (Submodule.equivMapOfInjective _ RLk_injective (skewH k)).finrank_eq]
  have hs : ∀ x, skL k x = skMat x := fun x => rfl
  have hrange : LinearMap.range (skL k) = skewH k := by
    ext X
    constructor
    · rintro ⟨x, rfl⟩; rw [hs]; exact skMat_mem x
    · intro hX; exact ⟨PolarCoordinateComparison.coords X, by rw [hs]; exact PolarCoordinateComparison.skMat_coords X hX⟩
  rw [← hrange, LinearMap.finrank_range_of_inj (fun x y h => volU_skMat_injective (by rwa [hs, hs] at h))]
  rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, mul_comm]

end Formalism.L2.SG.Pf.GV

namespace Formalism.L2.SG.Pf.GV

open Formalism.MainNotions.S ReciprocityTheory.ChartRestriction.DS

variable {k : ℕ}

abbrev Low (k : ℕ) : Type := {ab : Fin k × Fin k // ab.2 < ab.1}

theorem skMat_low (x : UCo k) (p : Low k) : skMat x p.1.1 p.1.2 = x.2 p := skMat_low_om x p

theorem skMat_up (x : UCo k) (p : Low k) : ‖skMat x p.1.2 p.1.1‖ = ‖x.2 p‖ := by
  obtain ⟨⟨a, b⟩, h⟩ := p
  simp [skMat, h, h.ne, not_lt.2 h.le]

theorem norm_skMat_sq (x : UCo k) :
    ‖RLk (skMat x)‖ ^ 2 = ∑ a, (x.1 a) ^ 2 + 2 * ∑ p : Low k, ‖x.2 p‖ ^ 2 := by
  have key : ∀ a b : Fin k, ‖skMat x a b‖ ^ 2 = (if a = b then (x.1 a) ^ 2 else 0) +
      (if h : b < a then ‖x.2 ⟨(a, b), h⟩‖ ^ 2 else 0) +
      (if h : a < b then ‖x.2 ⟨(b, a), h⟩‖ ^ 2 else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [skMat, h, h.ne, not_lt.2 h.le]
    · simp [skMat, sq_abs]
    · simp [skMat, h, h.ne', not_lt.2 h.le]
  have hL : ∑ a : Fin k, ∑ b : Fin k, (if h : b < a then ‖x.2 ⟨(a, b), h⟩‖ ^ 2 else 0) =
      ∑ p : Low k, ‖x.2 p‖ ^ 2 := by
    rw [← Fintype.sum_prod_type' (f := fun a b => if h : b < a then ‖x.2 ⟨(a, b), h⟩‖ ^ 2 else 0),
      ← Fintype.sum_subtype_add_sum_subtype (fun ab : Fin k × Fin k => ab.2 < ab.1)]
    have h1 : ∀ i : {ab : Fin k × Fin k // ¬ (ab.2 < ab.1)},
        (if h : i.1.2 < i.1.1 then ‖x.2 ⟨(i.1.1, i.1.2), h⟩‖ ^ 2 else 0) = 0 := fun i => dif_neg i.2
    have h2 : ∀ i : Low k,
        (if h : i.1.2 < i.1.1 then ‖x.2 ⟨(i.1.1, i.1.2), h⟩‖ ^ 2 else 0) = ‖x.2 i‖ ^ 2 :=
      fun i => by rw [dif_pos i.2]
    simp only [h1, h2, Finset.sum_const_zero, add_zero]
  rw [RLk_sq]
  simp only [key, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun a b => if h : a < b then ‖x.2 ⟨(b, a), h⟩‖ ^ 2 else 0), hL]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

end Formalism.L2.SG.Pf.GV

namespace Formalism.L2.SG.Pf.GV

open Formalism.MainNotions.S ReciprocityTheory.ChartRestriction.DS Formalism.L2.SG.Pf.BH.Model

variable {k : ℕ}

theorem meas_ind_lt (ρ : ℝ) : Measurable fun t : ℝ => (if t < ρ ^ 2 then (1 : ℝ≥0∞) else 0) := Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const

theorem euclid_ball_int (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫⁻ z : EuclideanSpace ℝ (Fin n), (if ‖z‖ ^ 2 < ρ ^ 2 then (1 : ℝ≥0∞) else 0) =
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ρ) := by
  rw [← lintegral_indicator_one measurableSet_ball]
  refine lintegral_congr fun z => ?_
  have h : ‖z‖ ^ 2 < ρ ^ 2 ↔ ‖z‖ < ρ :=
    ⟨fun h => by nlinarith [norm_nonneg z], fun h => by nlinarith [norm_nonneg z]⟩
  simp only [h]
  by_cases hz : ‖z‖ < ρ
  · have hm : z ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ρ := by simpa using hz
    simp [hz, hm]
  · have hm : z ∉ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ρ := by simpa using hz
    simp [hz, hm]

theorem vol_Bρ {ρ : ℝ} (hρ : 0 < ρ) : volume (Bρ k ρ) = (2 ^ Fintype.card (Low k))⁻¹ *
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * Fintype.card (Low k) + k))) ρ) := by
  set M := Fintype.card (Low k) with hM
  set G : ℝ → ℝ≥0∞ := fun t => if t < ρ ^ 2 then 1 else 0 with hG
  have hGm : Measurable G := meas_ind_lt ρ
  have hB : Bρ k ρ = {x : UCo k | ∑ a, (x.1 a) ^ 2 + 2 * ∑ p : Low k, ‖x.2 p‖ ^ 2 < ρ ^ 2} := by
    ext x
    simp only [Bρ, Set.mem_setOf_eq]
    rw [← norm_skMat_sq]
    constructor
    · intro h; exact pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
    · intro h; exact lt_of_pow_lt_pow_left₀ 2 hρ.le h
  have hBm : MeasurableSet {x : UCo k | ∑ a, (x.1 a) ^ 2 + 2 * ∑ p : Low k, ‖x.2 p‖ ^ 2 < ρ ^ 2} :=
    measurableSet_lt (by fun_prop) measurable_const
  rw [hB, ← lintegral_indicator_one hBm]
  have e1 : ∀ x : UCo k, {x : UCo k | ∑ a, (x.1 a) ^ 2 + 2 * ∑ p : Low k, ‖x.2 p‖ ^ 2 < ρ ^ 2}.indicator 1 x =
      G (2 * ∑ p : Low k, ‖x.2 p‖ ^ 2 + sqs x.1) := by
    intro x
    simp only [Set.indicator, Set.mem_setOf_eq, Pi.one_apply, hG, sqs]
    congr 1; apply propext; constructor <;> intro h <;> linarith
  simp_rw [e1]
  rw [Measure.volume_eq_prod, lintegral_prod _ ?meas]
  swap
  · exact (hGm.comp (by unfold sqs; fun_prop)).aemeasurable
  rw [lintegral_lintegral_swap ?meas2]
  swap
  · exact (hGm.comp (by unfold sqs; fun_prop)).aemeasurable

  have hA := PiLp.volume_preserving_ofLp (Fin k)
  have hEa : MeasurableEmbedding (@WithLp.ofLp 2 (Fin k → ℝ)) := (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm.measurableEmbedding
  have step1 : ∀ c : ℝ, ∫⁻ x1 : Fin k → ℝ, G (c + sqs x1) = ∫⁻ y : EuclideanSpace ℝ (Fin k), G (c + ‖y‖ ^ 2) := by
    intro c
    rw [← hA.lintegral_comp_emb hEa (fun x1 => G (c + sqs x1))]
    refine lintegral_congr fun y => ?_
    rw [norm_sq_euclid]; rfl
  simp_rw [step1]

  let e : Low k ≃ Fin M := Fintype.equivFin (Low k)
  have hP := volume_measurePreserving_piCongrLeft (fun _ : Low k => ℂ) e.symm
  have hPe := (MeasurableEquiv.piCongrLeft (fun _ : Low k => ℂ) e.symm).measurableEmbedding
  rw [← hP.lintegral_comp_emb hPe (fun x2 => ∫⁻ y : EuclideanSpace ℝ (Fin k),
    G (2 * ∑ p : Low k, ‖x2 p‖ ^ 2 + ‖y‖ ^ 2))]
  have hsum : ∀ u : Fin M → ℂ, ∑ p : Low k, ‖(MeasurableEquiv.piCongrLeft (fun _ : Low k => ℂ) e.symm) u p‖ ^ 2 =
      ∑ i, ‖u i‖ ^ 2 := by
    intro u
    rw [← Equiv.sum_comp e.symm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp_rw [hsum]
  rw [cpow_step M k G hGm, euclid_ball_int _ hρ]

end Formalism.L2.SG.Pf.GV

namespace Formalism.L2.SG.Pf.GV

open Formalism.MainNotions.S ReciprocityTheory.ChartRestriction.DS Formalism.L2.SG.Pf.BH.Model

variable {k : ℕ}

theorem ball_cast' (a b : ℕ) (h : a = b) (s : ℝ) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin a)) s) = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin b)) s) := by
  subst h
  rfl

theorem vol_gLie_ball (ρ : ℝ) : volume (Metric.ball (0 : ↥(Gauge.gLie (εT k))) ρ) =
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * Fintype.card (Low k) + k))) ρ) := by
  rw [Formalism.L2.SG.Pf.BH.ballDim]
  exact ball_cast' _ _ (by have h := finrank_gLie (k := k); change _ = k + 2 * Fintype.card (Low k) at h; omega) ρ

theorem norm_lt_of_Bρ {ρ : ℝ} (hρ : 0 < ρ) {x : UCo k} (hx : x ∈ Bρ k ρ) : ‖x‖ < ρ := by
  have hx' : ‖RLk (skMat x)‖ < ρ := hx
  refine lt_of_le_of_lt ?_ hx'
  have hsq := norm_skMat_sq x
  have hnn : 0 ≤ ‖RLk (skMat x)‖ := norm_nonneg _
  have h2 : 0 ≤ ∑ p : Low k, ‖x.2 p‖ ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have h3 : 0 ≤ ∑ a, (x.1 a) ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  refine norm_prod_le_iff.2 ⟨(pi_norm_le_iff_of_nonneg hnn).2 fun a => ?_,
    (pi_norm_le_iff_of_nonneg hnn).2 fun p => ?_⟩
  · have h1 : (x.1 a) ^ 2 ≤ ∑ b, (x.1 b) ^ 2 :=
      Finset.single_le_sum (f := fun b => (x.1 b) ^ 2) (fun b _ => sq_nonneg (x.1 b)) (Finset.mem_univ a)
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (x.1 a), abs_nonneg (x.1 a)]
  · have h1 : ‖x.2 p‖ ^ 2 ≤ ∑ q : Low k, ‖x.2 q‖ ^ 2 :=
      Finset.single_le_sum (f := fun q => ‖x.2 q‖ ^ 2) (fun q _ => sq_nonneg _) (Finset.mem_univ p)
    nlinarith [norm_nonneg (x.2 p)]

theorem card_low (k : ℕ) : Fintype.card (Low k) = k * (k - 1) / 2 := by
  have h1 : ∀ a : Fin k, ∑ b : Fin k, (if b < a then 1 else 0) = (a : ℕ) := by
    intro a
    rw [Finset.sum_boole]
    have : (Finset.univ.filter fun b : Fin k => b < a) = Finset.Iio a := by ext b; simp
    simp only [this, Fin.card_Iio, Nat.cast_id]
  rw [← Finset.sum_range_id, ← Fin.sum_univ_eq_sum_range (fun i => i) k, Fintype.card_subtype,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => h1 a

private theorem prod_two_pi_pow_div_factorial_eq_two_pow_mul_prod (n : ℕ) :
    ∏ i ∈ Finset.range n, (2 * Real.pi) ^ (i + 1) / (i.factorial : ℝ) =
      2 ^ (∑ i ∈ Finset.range n, i) * ∏ i ∈ Finset.range n, 2 * Real.pi ^ (i + 1) / (i.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ, ih, pow_add]
    ring

theorem volU_ratio (k : ℕ) : Formalism.MainNotions.S.UnitaryVolumeMass.volU k = 2 ^ Fintype.card (Low k) * ReciprocityTheory.ChartRestriction.DS.volU k := by
  rw [card_low, ← Finset.sum_range_id]
  exact prod_two_pi_pow_div_factorial_eq_two_pow_mul_prod k

end Formalism.L2.SG.Pf.GV

namespace Formalism.L2.SG.Pf.GV

open Formalism.MainNotions.S ReciprocityTheory.ChartRestriction.DS Formalism.L2.SG.Pf.BH.Model

variable {k : ℕ}

theorem isOpen_Bρ (ρ : ℝ) : IsOpen (Bρ k ρ) := by
  have hc : Continuous fun x : UCo k => RLk (skMat x) :=
    (RLk.comp (skL k)).continuous_of_finiteDimensional
  exact isOpen_lt (continuous_norm.comp hc) continuous_const

theorem ratio_bounds {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < δ →
      (Formalism.REAL.muG (εT k) Set.univ).toReal * (1 - η) / (ReciprocityTheory.ChartRestriction.DS.volU k * 2 ^ Fintype.card (Low k)) ≤
                Gauge.ratioAt (εT k) ρ ∧
        Gauge.ratioAt (εT k) ρ ≤
          (Formalism.REAL.muG (εT k) Set.univ).toReal * (1 + η) / (ReciprocityTheory.ChartRestriction.DS.volU k * 2 ^ Fintype.card (Low k)) := by
  set mG := Formalism.REAL.muG (εT k) with hmG
  have hfin : mG Set.univ ≠ ⊤ := measure_ne_top mG _
  have h0 : mG Set.univ ≠ 0 := (isOpen_univ.measure_pos mG Set.univ_nonempty).ne'
  set μ : Measure ↥(Formalism.REAL.UJ (εT k)) := (mG Set.univ)⁻¹ • mG with hμ
  have : μ.IsHaarMeasure := Measure.IsHaarMeasure.smul mG (ENNReal.inv_ne_zero.2 hfin) (ENNReal.inv_ne_top.2 h0)
  have : IsProbabilityMeasure μ := ⟨by rw [hμ, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hfin]⟩
  set E := (hU k).toMeasurableEquiv with hE
  set μK : Measure ↥(ReciprocityTheory.ChartRestriction.DS.UNgrp k) := μ.map E with hμK
  have : μK.IsHaarMeasure := MulEquiv.isHaarMeasure_map μ (eU k) (cont_eU k) (cont_eU_symm k)
  have : IsProbabilityMeasure μK := Measure.isProbabilityMeasure_map E.measurable.aemeasurable
  obtain ⟨δ, hδ, hd⟩ := volU_density μK η hη
  refine ⟨δ, hδ, fun ρ hρ hρδ => ?_⟩
  have hBm : MeasurableSet (Bρ k ρ) := (isOpen_Bρ ρ).measurableSet
  have hBs : ∀ x ∈ Bρ k ρ, ‖x‖ < δ := fun x hx => lt_trans (norm_lt_of_Bρ hρ hx) hρδ
  obtain ⟨hup, hlo⟩ := hd (Bρ k ρ) hBm hBs
  have hK : μK (volUSet (Bρ k ρ)) = μ (Gauge.expSet (εT k) (Metric.ball 0 ρ)) := by
    rw [hμK, MeasurableEquiv.map_apply, expSet_eq]; rfl
  have hV := vol_Bρ (k := k) hρ
  rw [← vol_gLie_ball] at hV
  set V := volume (Metric.ball (0 : ↥(Gauge.gLie (εT k))) ρ) with hVdef
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos _ _ hρ).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have hVr : 0 < V.toReal := ENNReal.toReal_pos hV0 hVt
  have hK' : μK {k_1 | ∃ x ∈ Bρ k ρ, S7.toM k_1 = NormedSpace.exp (skMat x)} =
      μ (Gauge.expSet (εT k) (Metric.ball 0 ρ)) := hK
  rw [hK', hV] at hup hlo
  set vL := ReciprocityTheory.ChartRestriction.DS.volU k with hvL
  have hvL0 : 0 < vL := ReciprocityTheory.ChartRestriction.DS.volU_pos' k
  set M := Fintype.card (Low k)
  have h2M : (0 : ℝ) < 2 ^ M := by positivity

  set m := μ (Gauge.expSet (εT k) (Metric.ball 0 ρ)) with hm
  have hmt : m ≠ ⊤ := ne_top_of_le_ne_top (by simp [ENNReal.mul_eq_top, hVt]) hup
  have e2 : ((2 : ℝ≥0∞) ^ M)⁻¹ * V = ENNReal.ofReal ((2 ^ M)⁻¹ * V.toReal) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hVt, ENNReal.ofReal_inv_of_pos h2M,
      ENNReal.ofReal_pow (by norm_num)]; simp
  rw [e2, ← ENNReal.ofReal_mul (by positivity)] at hup
  have hup' : m.toReal ≤ (1 + η) / vL * ((2 ^ M)⁻¹ * V.toReal) :=
    (ENNReal.toReal_le_of_le_ofReal (by positivity) hup)

  have hlo' : (1 - η) / vL * ((2 ^ M)⁻¹ * V.toReal) ≤ m.toReal := by
    rcases le_or_gt (1 - η) 0 with hneg | hpos
    · have : (1 - η) / vL * ((2 ^ M)⁻¹ * V.toReal) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hneg hvL0.le) (by positivity)
      exact le_trans this ENNReal.toReal_nonneg
    · rw [e2, ← ENNReal.ofReal_mul (div_nonneg hpos.le hvL0.le)] at hlo
      exact (ENNReal.ofReal_le_iff_le_toReal hmt).1 hlo

  have hratio : Gauge.ratioAt (εT k) ρ = (mG Set.univ).toReal * m.toReal / V.toReal := by
    unfold Gauge.ratioAt
    congr 1
    have : mG (Gauge.expSet (εT k) (Metric.ball 0 ρ)) = mG Set.univ * m := by
      rw [hm, hμ, Measure.smul_apply, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel h0 hfin, one_mul]
    rw [this, ENNReal.toReal_mul]
  have hZ : 0 ≤ (mG Set.univ).toReal := ENNReal.toReal_nonneg
  rw [hratio]
  constructor
  · rw [le_div_iff₀ hVr]
    have := mul_le_mul_of_nonneg_left hlo' hZ
    calc (mG Set.univ).toReal * (1 - η) / (vL * 2 ^ M) * V.toReal
        = (mG Set.univ).toReal * ((1 - η) / vL * ((2 ^ M)⁻¹ * V.toReal)) := by field_simp
      _ ≤ (mG Set.univ).toReal * m.toReal := this
  · rw [div_le_iff₀ hVr]
    have := mul_le_mul_of_nonneg_left hup' hZ
    calc (mG Set.univ).toReal * m.toReal ≤ (mG Set.univ).toReal * ((1 + η) / vL * ((2 ^ M)⁻¹ * V.toReal)) := this
      _ = (mG Set.univ).toReal * (1 + η) / (vL * 2 ^ M) * V.toReal := by field_simp

end Formalism.L2.SG.Pf.GV

namespace Formalism.L2.SG.Pf.GV

open Formalism.MainNotions.S ReciprocityTheory.ChartRestriction.DS

variable {k : ℕ}

theorem ratio_tendsto (k : ℕ) :
    Tendsto (Gauge.ratioAt (εT k)) (𝓝[>] (0 : ℝ))
      (𝓝 ((Formalism.REAL.muG (εT k) Set.univ).toReal / (ReciprocityTheory.ChartRestriction.DS.volU k * 2 ^ Fintype.card (Low k)))) := by
  set Z := (Formalism.REAL.muG (εT k) Set.univ).toReal with hZ
  set D := ReciprocityTheory.ChartRestriction.DS.volU k * 2 ^ Fintype.card (Low k) with hD
  have hDp : 0 < D := mul_pos (ReciprocityTheory.ChartRestriction.DS.volU_pos' k) (by positivity)
  have hZp : 0 < Z := by
    have h0 : Formalism.REAL.muG (εT k) Set.univ ≠ 0 := (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'
    exact ENNReal.toReal_pos h0 (measure_ne_top _ _)
  set c := Z / D with hc
  have hcp : 0 < c := div_pos hZp hDp
  rw [tendsto_order]
  constructor
  · intro a ha
    set η := min (1 / 2) ((c - a) / (2 * c)) with hη
    have hη0 : 0 < η := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
    have hηa : η ≤ (c - a) / (2 * c) := min_le_right _ _
    obtain ⟨δ, hδ, hb⟩ := ratio_bounds (k := k) hη0
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ ⟨hρ0, hρδ⟩
    have h1 := (hb ρ hρ0 hρδ).1
    have : a < Z * (1 - η) / D := by
      have e : Z * (1 - η) / D = c * (1 - η) := by rw [hc]; ring
      rw [e]
      have : c * η ≤ (c - a) / 2 := by
        have := mul_le_mul_of_nonneg_left hηa hcp.le
        have e2 : c * ((c - a) / (2 * c)) = (c - a) / 2 := by field_simp
        linarith
      nlinarith
    linarith
  · intro b hb
    set η := (b - c) / (2 * c) with hη
    have hη0 : 0 < η := div_pos (by linarith) (by positivity)
    obtain ⟨δ, hδ, hbd⟩ := ratio_bounds (k := k) hη0
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ ⟨hρ0, hρδ⟩
    have h1 := (hbd ρ hρ0 hρδ).2
    have : Z * (1 + η) / D < b := by
      have e1 : Z * (1 + η) / D = c * (1 + η) := by rw [hc]; ring
      have e2 : c * (1 + η) = c + (b - c) / 2 := by rw [hη]; field_simp
      rw [e1, e2]; linarith
    linarith

theorem gaugeVolU (k : ℕ) :
    Gauge.GaugeDens (εT k) ∧ Gauge.muGauge (εT k) Set.univ = ENNReal.ofReal (Formalism.MainNotions.S.UnitaryVolumeMass.volU k) := by
  have hT := ratio_tendsto k
  have hg := Gauge.gaugeU_eq hT
  set Z := (Formalism.REAL.muG (εT k) Set.univ).toReal with hZ
  set D := ReciprocityTheory.ChartRestriction.DS.volU k * 2 ^ Fintype.card (Low k) with hD
  have hDp : 0 < D := mul_pos (ReciprocityTheory.ChartRestriction.DS.volU_pos' k) (by positivity)
  have h0 : Formalism.REAL.muG (εT k) Set.univ ≠ 0 := (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'
  have hfin : Formalism.REAL.muG (εT k) Set.univ ≠ ⊤ := measure_ne_top _ _
  have hZp : 0 < Z := ENNReal.toReal_pos h0 hfin
  refine ⟨⟨by rw [hg]; exact hT, by rw [hg]; exact div_pos hZp hDp⟩, ?_⟩
  unfold Gauge.muGauge
  rw [Measure.smul_apply, smul_eq_mul, hg, ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (by positivity),
    volU_ratio]
  congr 1
  rw [← hZ]
  field_simp
  ring

end Formalism.L2.SG.Pf.GV
