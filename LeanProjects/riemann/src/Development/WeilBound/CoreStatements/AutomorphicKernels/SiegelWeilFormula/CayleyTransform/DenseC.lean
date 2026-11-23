import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DenseCP

noncomputable section

open Matrix Topology

namespace PositivityTheory.SiegelWeilFormula.Krd.DC

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def InU (J h : Matrix ι ι ℂ) : Prop := hᴴ * J * h = J

def InLie (J Y : Matrix ι ι ℂ) : Prop := Yᴴ * J + J * Y = 0

def cay (Y : Matrix ι ι ℂ) : Matrix ι ι ℂ := (1 + Y) * (1 - Y)⁻¹

def proj (J : Matrix ι ι ℂ) (d : ℂ) (Y : Matrix ι ι ℂ) : Matrix ι ι ℂ := Y - d⁻¹ • (J * Yᴴ * J)

theorem cay_inU {J Y : Matrix ι ι ℂ} (hY : InLie J Y) (hu : IsUnit (1 - Y).det) : InU J (cay Y) := by
  exact PositivityTheory.SiegelWeilFormula.Krd.CP.cay_inU hY hu

theorem cay_surj {J h : Matrix ι ι ℂ} (hh : InU J h) (hu : IsUnit (1 + h).det) :
    ∃ Y, InLie J Y ∧ IsUnit (1 - Y).det ∧ cay Y = h := by
  exact PositivityTheory.SiegelWeilFormula.Krd.CP.cay_surj hh hu

theorem isOpen_dom : IsOpen {Y : Matrix ι ι ℂ | IsUnit (1 - Y).det} := by
  have hc : Continuous fun Y : Matrix ι ι ℂ => (1 - Y).det :=
    (continuous_const.sub continuous_id).matrix_det
  have he : {Y : Matrix ι ι ℂ | IsUnit (1 - Y).det} = (fun Y : Matrix ι ι ℂ => (1 - Y).det) ⁻¹' {0}ᶜ := by
    ext Y
    simp [isUnit_iff_ne_zero]
  rw [he]
  exact isOpen_compl_singleton.preimage hc

theorem continuousOn_cay : ContinuousOn (cay (ι := ι)) {Y | IsUnit (1 - Y).det} := by
  intro Y hY
  apply ContinuousAt.continuousWithinAt
  have hinv : ContinuousAt (fun Z : Matrix ι ι ℂ => (1 - Z)⁻¹) Y := by
    have h1 : ContinuousAt Inv.inv (1 - Y) := by
      apply continuousAt_matrix_inv
      have h2 := NormedRing.inverse_continuousAt hY.unit
      rwa [hY.unit_spec] at h2
    exact h1.comp (continuous_const.sub continuous_id).continuousAt
  show ContinuousAt (fun Z : Matrix ι ι ℂ => (1 + Z) * (1 - Z)⁻¹) Y
  exact (continuous_const.add continuous_id).continuousAt.mul hinv

theorem inLie_proj {J : Matrix ι ι ℂ} {c d : ℂ} (hc : Jᴴ = c • J) (hcc : c * c = 1) (hd : J * J = d • 1) (hd0 : d ≠ 0)
    (hds : star d = d) (Y : Matrix ι ι ℂ) : InLie J (proj J d Y) := by
  have hJJ : ∀ X : Matrix ι ι ℂ, J * (J * X) = d • X := by
    intro X
    rw [← Matrix.mul_assoc, hd, Matrix.smul_mul, Matrix.one_mul]
  have hsd : star d⁻¹ = d⁻¹ := by rw [star_inv₀, hds]
  unfold InLie proj
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, hc, hsd]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_assoc, hJJ, hd, Matrix.mul_one]
  rw [hcc, mul_one, inv_mul_cancel₀ hd0, one_smul, one_smul]
  abel

theorem proj_half {J : Matrix ι ι ℂ} {d : ℂ} (hd : J * J = d • 1) (hd0 : d ≠ 0) {Y : Matrix ι ι ℂ} (hY : InLie J Y) :
    proj J d ((1 / 2 : ℂ) • Y) = Y := by
  have h1 : J * Yᴴ * J = -(d • Y) := by
    have h2 : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
    rw [Matrix.mul_assoc, h2, Matrix.mul_neg, ← Matrix.mul_assoc, hd, Matrix.smul_mul, Matrix.one_mul]
  unfold proj
  rw [conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, h1]
  ext i j
  simp
  field_simp
  ring

theorem continuous_proj (J : Matrix ι ι ℂ) (d : ℂ) : Continuous (proj J d) := by
  unfold proj
  have h1 : Continuous fun Y : Matrix ι ι ℂ => J * Yᴴ * J :=
    (continuous_const.mul continuous_id.matrix_conjTranspose).mul continuous_const
  exact continuous_id.sub (h1.const_smul d⁻¹)

theorem lie_dense {J : Matrix ι ι ℂ} {c d : ℂ} (hc : Jᴴ = c • J) (hcc : c * c = 1) (hd : J * J = d • 1) (hd0 : d ≠ 0)
    (hds : star d = d) {S : Set (Matrix ι ι ℂ)} (hS : Dense S) (hSp : ∀ X ∈ S, proj J d X ∈ S) {Y : Matrix ι ι ℂ}
    (hY : InLie J Y) {U : Set (Matrix ι ι ℂ)} (hU : IsOpen U) (hYU : Y ∈ U) : ∃ X ∈ S, InLie J X ∧ X ∈ U := by
  have hW : IsOpen (proj J d ⁻¹' U) := hU.preimage (continuous_proj J d)
  have hmem : (1 / 2 : ℂ) • Y ∈ proj J d ⁻¹' U := by
    show proj J d ((1 / 2 : ℂ) • Y) ∈ U
    rw [proj_half hd hd0 hY]
    exact hYU
  obtain ⟨X, hXS, hXW⟩ := hS.exists_mem_open hW ⟨_, hmem⟩
  exact ⟨proj J d X, hSp X hXS, inLie_proj hc hcc hd hd0 hds X, hXW⟩

theorem scalar_avoid {J h : Matrix ι ι ℂ} (hh : InU J h) {V : Set (Matrix ι ι ℂ)} (hV : IsOpen V) (hhV : h ∈ V) :
    ∃ μ : ℂ, star μ * μ = 1 ∧ μ • h ∈ V ∧ IsUnit (1 + μ • h).det := by
  exact PositivityTheory.SiegelWeilFormula.Krd.CP.scalar_avoid hh hV hhV

theorem inU_smul {J h : Matrix ι ι ℂ} (hh : InU J h) {μ : ℂ} (hμ : star μ * μ = 1) : InU J (μ • h) := by
  unfold InU at *
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hh]
  rw [mul_comm μ, hμ, one_smul]

theorem densG {J : Matrix ι ι ℂ} {c d : ℂ} (hc : Jᴴ = c • J) (hcc : c * c = 1) (hd : J * J = d • 1) (hd0 : d ≠ 0)
    (hds : star d = d) {S : Set (Matrix ι ι ℂ)} (hS : Dense S) (hSp : ∀ X ∈ S, proj J d X ∈ S)
    (hSc : ∀ X ∈ S, IsUnit (1 - X).det → cay X ∈ S) {V : Set (Matrix ι ι ℂ)} (hV : IsOpen V) {h : Matrix ι ι ℂ}
    (hhV : h ∈ V) (hh : InU J h) : ∃ h' ∈ V, h' ∈ S ∧ InU J h' := by
  obtain ⟨μ, hμ, hμV, hμu⟩ := scalar_avoid hh hV hhV
  obtain ⟨Y, hYL, hYu, hYc⟩ := cay_surj (inU_smul hh hμ) hμu
  have hU : IsOpen ({Y : Matrix ι ι ℂ | IsUnit (1 - Y).det} ∩ cay ⁻¹' V) :=
    continuousOn_cay.isOpen_inter_preimage isOpen_dom hV
  have hYU : Y ∈ {Y : Matrix ι ι ℂ | IsUnit (1 - Y).det} ∩ cay ⁻¹' V := by
    refine ⟨hYu, ?_⟩
    show cay Y ∈ V
    rw [hYc]
    exact hμV
  obtain ⟨X, hXS, hXL, hXU⟩ := lie_dense hc hcc hd hd0 hds hS hSp hYL hU hYU
  exact ⟨cay X, hXU.2, hSc X hXS hXU.1, cay_inU hXL hXU.1⟩

end PositivityTheory.SiegelWeilFormula.Krd.DC

end
