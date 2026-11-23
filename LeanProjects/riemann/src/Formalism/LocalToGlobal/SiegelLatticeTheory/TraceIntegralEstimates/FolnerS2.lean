import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FolnerAbs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.ModBase
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnipotentRadicalContracting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.UnitaryWeylCompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.IsClosedS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MaximalCompactIsCompact

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal Pointwise

namespace Formalism.L2.S.Pv.FolnerS

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW PI.QuotSetU.UnitaryGroupMassFormula.ModW PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG
  Formalism.L2.S.Pv.FolnerAbs Formalism.L2.SG.Pf.EnergyAbs

variable {k r : ℕ}

abbrev GH (k r : ℕ) : Type := MG (UH (Hpk k r)) (unitary_hermitian_group k r)

def Sg (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (GH k r) := {g | g.toM ∈ Sset k r z}

def Cg (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (GH k r) := {g | g.toM ∈ UWset k r z}

def nrm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖

theorem continuous_nrm {n : ℕ} : Continuous (nrm (n := n)) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_norm.comp ((continuous_apply j).comp (continuous_apply i))

theorem entry_le_nrm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖M i j‖ ≤ nrm M := by
  unfold nrm
  calc ‖M i j‖ ≤ ∑ j', ‖M i j'‖ := Finset.single_le_sum (f := fun j' => ‖M i j'‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖M i' j'‖ := Finset.single_le_sum (f := fun i' => ∑ j', ‖M i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

def fG (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : GH k r) : ℝ :=
  sInf ((fun c : GH k r => nrm ((c * g).toM - 1)) '' Cg k r z)

variable {z : Fin (2 * r + k + 1) → ℂ}

theorem isClosedEmbedding_toM : Topology.IsClosedEmbedding (toM : GH k r → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  isClosedEmbedding_val

theorem isCompact_Cg (hz : inWb k r z) (hT : 0 < Tz k r z) : IsCompact (Cg k r z) :=
  isClosedEmbedding_toM.isCompact_preimage (unitary_weyl_compact k r z hz hT)

theorem isClosed_Sg (hz : inWb k r z) (hT : 0 < Tz k r z) : IsClosed (Sg k r z) :=
  (isClosed_S (unitary_weyl_compact k r z hz hT)).preimage continuous_toM

theorem one_mem_Cg : (1 : GH k r) ∈ Cg k r z := by
  show (1 : GH k r).toM ∈ UWset k r z; rw [toM_one]; exact one_mem_UW

theorem mul_mem_Cg {a b : GH k r} (ha : a ∈ Cg k r z) (hb : b ∈ Cg k r z) : a * b ∈ Cg k r z := by
  show (a * b).toM ∈ UWset k r z; rw [toM_mul]; exact mul_mem_UW ha hb

theorem inv_mem_Cg {a : GH k r} (ha : a ∈ Cg k r z) : a⁻¹ ∈ Cg k r z := by
  show a⁻¹.toM ∈ UWset k r z; rw [toM_inv]; exact inv_mem_UW ha

theorem continuous_fG (hz : inWb k r z) (hT : 0 < Tz k r z) : Continuous (fG k r z) := by
  have h : Continuous (fun p : GH k r × GH k r => nrm ((p.2 * p.1).toM - 1)) :=
    continuous_nrm.comp ((continuous_toM.comp (continuous_snd.mul continuous_fst)).sub continuous_const)
  exact (isCompact_Cg hz hT).continuous_sInf h

theorem fG_mul_left {c₀ : GH k r} (hc₀ : c₀ ∈ Cg k r z) (g : GH k r) : fG k r z (c₀ * g) = fG k r z g := by
  unfold fG
  congr 1
  ext t
  simp only [Set.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c * c₀, mul_mem_Cg hc hc₀, by rw [mul_assoc]⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c * c₀⁻¹, mul_mem_Cg hc (inv_mem_Cg hc₀), by rw [mul_assoc, inv_mul_cancel_left]⟩

theorem isCompact_ball1 (ρ : ℝ) : IsCompact {x : GH k r | nrm (x.toM - 1) ≤ ρ} := by
  have hK : IsCompact {x : MtM (2 * r + k + 1) | nrm (Matrix.of x - 1) ≤ ρ} := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact isClosed_le (continuous_nrm.comp (continuous_id.sub continuous_const)) continuous_const
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨ρ + 1, fun x hx => ?_⟩
      rw [mem_closedBall_zero_iff]
      have hρ : 0 ≤ ρ := le_trans (by unfold nrm; positivity) hx
      refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => (pi_norm_le_iff_of_nonneg (by linarith)).2 fun j => ?_
      have h1 := le_trans (entry_le_nrm _ i j) hx
      have h2 : ‖(1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j‖ ≤ 1 := by
        rw [Matrix.one_apply]; split_ifs <;> simp
      calc ‖x i j‖ = ‖(Matrix.of x - 1) i j + (1 : Matrix _ _ ℂ) i j‖ := by
            rw [Matrix.sub_apply, sub_add_cancel]; rfl
        _ ≤ ‖(Matrix.of x - 1) i j‖ + ‖(1 : Matrix _ _ ℂ) i j‖ := norm_add_le _ _
        _ ≤ ρ + 1 := add_le_add h1 h2
  exact (isClosedEmbedding_val (hG := unitary_hermitian_group k r)).isCompact_preimage hK

theorem isCompact_sublevel (hz : inWb k r z) (hT : 0 < Tz k r z) (ρ : ℝ) :
    IsCompact ({x | fG k r z x ≤ ρ} ∩ Sg k r z) := by
  have hC := isCompact_Cg (k := k) (r := r) hz hT
  have hB := isCompact_ball1 (k := k) (r := r) ρ
  have hL : IsCompact ((fun p : GH k r × GH k r => p.1⁻¹ * p.2) '' (Cg k r z ×ˢ {x : GH k r | nrm (x.toM - 1) ≤ ρ})) :=
    (hC.prod hB).image (continuous_fst.inv.mul continuous_snd)
  refine hL.of_isClosed_subset ((isClosed_le (continuous_fG hz hT) continuous_const).inter (isClosed_Sg hz hT)) ?_
  rintro g ⟨hg, -⟩
  have hF : Continuous (fun c : GH k r => nrm ((c * g).toM - 1)) :=
    continuous_nrm.comp ((continuous_toM.comp (continuous_id.mul continuous_const)).sub continuous_const)
  obtain ⟨c, hc, hmin⟩ := hC.exists_isMinOn ⟨1, one_mem_Cg⟩ hF.continuousOn
  have hle : nrm ((c * g).toM - 1) ≤ fG k r z g :=
    le_csInf (Set.Nonempty.image _ ⟨1, one_mem_Cg⟩) (by rintro _ ⟨c', hc', rfl⟩; exact hmin hc')
  exact ⟨(c, c * g), ⟨hc, show nrm ((c * g).toM - 1) ≤ ρ from le_trans hle hg⟩, by simp⟩

def aT (k r : ℕ) : GH k r := mk (unitary_hermitian_group k r) (dS k r 2) (dS_mem_UH (by norm_num))

theorem toM_pow (x : GH k r) (m : ℕ) : (x ^ m).toM = x.toM ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, toM_one]
  | succ m ih => rw [pow_succ, pow_succ, toM_mul, ih]

theorem dS_pow (s : ℝ) (m : ℕ) : (dS k r s) ^ m = dS k r (s ^ m) := by
  unfold dS
  rw [Matrix.diagonal_pow]
  congr 1
  funext i
  simp only [Pi.pow_apply]
  push_cast
  rw [← zpow_natCast ((s : ℂ) ^ fexp k r i) m, ← zpow_natCast (s : ℂ) m, ← _root_.zpow_mul, ← _root_.zpow_mul,
    mul_comm]

theorem toM_cjB_aT (m : ℕ) (g : GH k r) :
    (cjB (aT k r ^ m) g).toM = dS k r ((1 / 2 : ℝ) ^ m) * g.toM * (dS k r ((1 / 2 : ℝ) ^ m))⁻¹ := by
  have h2 : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hh : (1 / 2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have e1 : (1 / 2 : ℝ) ^ m = ((2 : ℝ) ^ m)⁻¹ := by rw [one_div, inv_pow]
  unfold cjB
  rw [toM_mul, toM_mul, toM_inv, toM_pow, aT, toM_mk, dS_pow, dS_inv_eq h2, dS_inv_eq hh, e1, inv_inv]

theorem aT_iff (z : Fin (2 * r + k + 1) → ℂ) (s : GH k r) : s ∈ Sg k r z ↔ cjB (aT k r) s ∈ Sg k r z := by
  have e := toM_cjB_aT (k := k) (r := r) 1 s
  rw [pow_one, pow_one] at e
  show s.toM ∈ Sset k r z ↔ (cjB (aT k r) s).toM ∈ Sset k r z
  rw [e, dS_conj_S_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)]

theorem contractV (hz : inWb k r z) (hT : 0 < Tz k r z) (K : Set (GH k r)) (hK : IsCompact K) (hKS : K ⊆ Sg k r z)
    (V : Set (GH k r)) (hV : V ∈ 𝓝 (1 : GH k r)) :
    ∀ᶠ m : ℕ in atTop, ∀ x ∈ K, cjB (aT k r ^ m) x ∈ Cg k r z * V := by
  have hC := isCompact_Cg (k := k) (r := r) hz hT
  have hI := (isClosedEmbedding_val (hG := unitary_hermitian_group k r)).isInducing
  rw [hI.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨t, ht, htV⟩ := hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ht
  set L := (fun p : GH k r × GH k r => p.1⁻¹ * p.2) '' (Cg k r z ×ˢ K) with hLdef
  have hL : IsCompact L := (hC.prod hK).image (continuous_fst.inv.mul continuous_snd)
  obtain ⟨B, hB⟩ := hL.exists_bound_of_continuousOn (continuous_val (hG := unitary_hermitian_group k r)).continuousOn
  have hlim : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m * B) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const B
    rwa [zero_mul] at this
  filter_upwards [hlim.eventually (eventually_lt_nhds hδ)] with m hm
  intro x hx
  obtain ⟨h, hh, n, hn, hxn⟩ := (hKS hx : x.toM ∈ Sset k r z)
  set c : GH k r := mk (unitary_hermitian_group k r) h hh.1 with hcdef
  have hcC : c ∈ Cg k r z := by show c.toM ∈ UWset k r z; rw [hcdef, toM_mk]; exact hh
  set ν : GH k r := c⁻¹ * x with hνdef
  have hνL : ν ∈ L := ⟨(c, x), ⟨hcC, hx⟩, rfl⟩
  have hdet : IsUnit h.det := by
    have := det_ne_zero c; rw [hcdef, toM_mk] at this; exact isUnit_iff_ne_zero.2 this
  have hνN : ν.toM = n := by
    rw [hνdef, toM_mul, toM_inv, hcdef, toM_mk, hxn, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have hxe : x = c * ν := by rw [hνdef, mul_inv_cancel_left]
  have hs0 : (0 : ℝ) < (1 / 2) ^ m := by positivity
  have hs1 : ((1 / 2 : ℝ)) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hcfix : cjB (aT k r ^ m) c = c := by
    ext1
    rw [toM_cjB_aT, dS_inv_eq hs0.ne', hcdef, toM_mk]
    exact dS_conj_UW hs0.ne' hh
  rw [hxe, cjB_mul, hcfix]
  refine Set.mul_mem_mul hcC (htV (hball ?_))
  rw [Metric.mem_ball, dist_pi_lt_iff hδ]
  intro i
  rw [dist_pi_lt_iff hδ]
  intro j
  show dist ((cjB (aT k r ^ m) ν).toM i j) ((1 : GH k r).toM i j) < δ
  rw [toM_one, dist_eq_norm, ← Matrix.sub_apply, toM_cjB_aT, hνN]
  have hbd : ‖n i j‖ ≤ B := by
    rw [← hνN]
    exact le_trans (le_trans (norm_le_pi_norm (ν.val i) j) (norm_le_pi_norm ν.val i)) (hB ν hνL)
  calc ‖(dS k r ((1 / 2 : ℝ) ^ m) * n * (dS k r ((1 / 2 : ℝ) ^ m))⁻¹ - 1) i j‖
      ≤ (1 / 2 : ℝ) ^ m * ‖n i j‖ := norm_dS_conj_le hs0 hs1 hn i j
    _ ≤ (1 / 2 : ℝ) ^ m * B := mul_le_mul_of_nonneg_left hbd hs0.le
    _ < δ := hm

end Formalism.L2.S.Pv.FolnerS
