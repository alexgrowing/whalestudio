import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvGrp

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

def HaarWAll : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW : Measure (Mt k r)), inWb k r z → 0 < Tz k r z →
    IsHaarOn (UWset k r z) μW → μW Set.univ = 1 →
    (∀ h ∈ UWset k r z, MeasurePreserving (fun x : Mt k r => fun i j => (Matrix.of x * h) i j) μW μW) ∧
    MeasurePreserving (fun x : Mt k r => fun i j => (Matrix.of x)⁻¹ i j) μW μW

def HaarNAll : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (κ : ENNReal), inWb k r z → 0 < Tz k r z →
    haarLie (Nset k r) κ {x | Matrix.of x ∉ Nset k r} = 0 ∧
    (∀ h ∈ UWset k r z, ∀ m ∈ Nset k r,
      MeasurePreserving (fun x : Mt k r => fun i j => (h⁻¹ * Matrix.of x * h * m) i j)
        (haarLie (Nset k r) κ) (haarLie (Nset k r) κ)) ∧
    ∀ h ∈ UWset k r z,
      MeasurePreserving (fun x : Mt k r => fun i j => (h * (Matrix.of x)⁻¹ * h⁻¹) i j)
        (haarLie (Nset k r) κ) (haarLie (Nset k r) κ)

def PiContAll : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (π : Mx k r → (Wp →L[ℂ] Wp)),
    inWb k r z → 0 < Tz k r z → IsHCTypeW k r z u π → ∀ x : Wp, ContinuousOn (fun g => π g x) (UWset k r z)

section Meas

variable {k r : ℕ}

theorem measurable_matInv : Measurable (fun x : Mt k r => (fun i j => (Matrix.of x)⁻¹ i j : Mt k r)) := by
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Mx k r)) := continuous_id
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact hc.matrix_det.measurable.inv.mul (hc.matrix_adjugate.matrix_elem i j).measurable

def minvM (x : Mt k r) : Mt k r := fun i j => (Matrix.of x)⁻¹ i j

def tripleMatrixProduct (q : Mt k r × Mt k r × Mt k r) : Mt k r := fun i j => (Matrix.of q.1 * Matrix.of q.2.1 * Matrix.of q.2.2) i j

theorem measurable_minvM : Measurable (minvM (k := k) (r := r)) := measurable_matInv

theorem triple_matrix_product_continuous : Continuous (tripleMatrixProduct (k := k) (r := r)) := by
  have h1 : Continuous (fun q : Mt k r × Mt k r × Mt k r => (Matrix.of q.1 : Mx k r)) := continuous_fst
  have h2 : Continuous (fun q : Mt k r × Mt k r × Mt k r => (Matrix.of q.2.1 : Mx k r)) :=
    continuous_fst.comp continuous_snd
  have h3 : Continuous (fun q : Mt k r × Mt k r × Mt k r => (Matrix.of q.2.2 : Mx k r)) :=
    continuous_snd.comp continuous_snd
  exact (h1.matrix_mul h2).matrix_mul h3

theorem uh_inv_eq {a : Mx k r} (ha : a ∈ UH (Hpk k r)) : a⁻¹ = Hpk k r * aᴴ * Hpk k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have h1 : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
    rw [mul_assoc, mul_assoc, ← mul_assoc aᴴ, ha', hpk_sq]
  exact Matrix.inv_eq_left_inv h1

theorem isClosed_uw (z : Fin (2 * r + k + 1) → ℂ) : IsClosed {x : Mt k r | Matrix.of x ∈ UWset k r z} := by
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Mx k r)) := continuous_id
  simp only [UWset, UH, Set.mem_setOf_eq, Set.setOf_and, Set.setOf_forall]
  refine (isClosed_eq ((hc.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hc)
    continuous_const).inter ((isClosed_iInter fun a => (isClosed_eq
      (hc.matrix_mulVec continuous_const) continuous_const).inter (isClosed_eq
      (hc.matrix_mulVec continuous_const) continuous_const)).inter
    (isClosed_eq (hc.matrix_mulVec continuous_const) continuous_const))

theorem piInv_aesm {z : Fin (2 * r + k + 1) → ℂ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] {π : Mx k r → (Wp →L[ℂ] Wp)} (hπc : ∀ x : Wp, ContinuousOn (fun g => π g x) (UWset k r z))
    {μW : Measure (Mt k r)} (hμ : μW {x | Matrix.of x ∉ UWset k r z} = 0) :
    AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x)⁻¹) μW := by
  have hc : Continuous (fun x : Mt k r => (Matrix.of x : Mx k r)) := continuous_id
  have hS : MeasurableSet {x : Mt k r | Matrix.of x ∈ UWset k r z} := (isClosed_uw z).measurableSet
  have hμS : μW.restrict {x : Mt k r | Matrix.of x ∈ UWset k r z} = μW :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμ)
  rw [← hμS]
  have hπ' : ContinuousOn π (UWset k r z) := continuousOn_clm_apply.mpr hπc
  have hcont : ContinuousOn (fun x : Mt k r => π (Hpk k r * (Matrix.of x)ᴴ * Hpk k r))
      {x : Mt k r | Matrix.of x ∈ UWset k r z} := by
    refine hπ'.comp (Continuous.continuousOn
      ((continuous_const.matrix_mul hc.matrix_conjTranspose).matrix_mul continuous_const)) ?_
    intro x hx
    have hx' : Matrix.of x ∈ UWset k r z := hx
    show Hpk k r * (Matrix.of x)ᴴ * Hpk k r ∈ UWset k r z
    rw [← uh_inv_eq hx'.1]
    exact uw_inv hx'
  refine (hcont.aestronglyMeasurable hS).congr ?_
  filter_upwards [ae_restrict_mem hS] with x hx
  have hx' : Matrix.of x ∈ UWset k r z := hx
  show π (Hpk k r * (Matrix.of x)ᴴ * Hpk k r) = π (Matrix.of x)⁻¹
  rw [uh_inv_eq hx'.1]

theorem measF_of {z : Fin (2 * r + k + 1) → ℂ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] {π : Mx k r → (Wp →L[ℂ] Wp)} {μW μN : Measure (Mt k r)} [SigmaFinite μW]
    [SFinite μN]
    (hWr : ∀ h ∈ UWset k r z, MeasurePreserving (fun x : Mt k r => fun i j => (Matrix.of x * h) i j) μW μW)
    (hWi : MeasurePreserving (fun x : Mt k r => fun i j => (Matrix.of x)⁻¹ i j) μW μW)
    (hW0 : μW {x | Matrix.of x ∉ UWset k r z} = 0) (hN0 : μN {x | Matrix.of x ∉ Nset k r} = 0)
    (hNc : ∀ h ∈ UWset k r z, ∀ m ∈ Nset k r,
      MeasurePreserving (fun x : Mt k r => fun i j => (h⁻¹ * Matrix.of x * h * m) i j) μN μN)
    (hNi : ∀ h ∈ UWset k r z,
      MeasurePreserving (fun x : Mt k r => fun i j => (h * (Matrix.of x)⁻¹ * h⁻¹) i j) μN μN)
    (hπc : ∀ x : Wp, ContinuousOn (fun g => π g x) (UWset k r z)) : MeasF z π μW μN := by
  refine ⟨?_, ?_, ?_, piInv_aesm hπc hW0⟩
  · have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z :=
      Measure.quasiMeasurePreserving_fst.ae (ae_iff.mpr hW0)
    have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r :=
      Measure.quasiMeasurePreserving_snd.ae (ae_iff.mpr hN0)
    filter_upwards [h1, h2] with p hp1 hp2 using ⟨hp1, hp2⟩
  · intro h hh m hm
    exact (hWr h hh).prod (hNc h hh m hm)
  · have hgm : Measurable (Function.uncurry fun (x : Mt k r) (y : Mt k r) =>
        (fun i j => (Matrix.of x * (Matrix.of y)⁻¹ * (Matrix.of x)⁻¹) i j : Mt k r)) := by
      have e : (Function.uncurry fun (x : Mt k r) (y : Mt k r) =>
          (fun i j => (Matrix.of x * (Matrix.of y)⁻¹ * (Matrix.of x)⁻¹) i j : Mt k r)) =
          tripleMatrixProduct ∘ (fun p : Mt k r × Mt k r => (p.1, minvM p.2, minvM p.1)) := by
        funext p
        rfl
      rw [e]
      exact triple_matrix_product_continuous.measurable.comp (measurable_fst.prodMk
        ((measurable_minvM.comp measurable_snd).prodMk (measurable_minvM.comp measurable_fst)))
    have hg : ∀ᵐ x ∂μW, Measure.map (fun (y : Mt k r) =>
        (fun i j => (Matrix.of x * (Matrix.of y)⁻¹ * (Matrix.of x)⁻¹) i j : Mt k r)) μN = μN := by
      filter_upwards [ae_iff.mpr hW0] with x hx
      exact (hNi _ hx).map_eq
    exact hWi.skew_product hgm hg

end Meas

end PI.WBL.Cv
