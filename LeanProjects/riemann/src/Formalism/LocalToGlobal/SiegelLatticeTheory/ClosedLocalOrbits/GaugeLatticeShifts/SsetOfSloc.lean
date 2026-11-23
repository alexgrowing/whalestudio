import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MeasurableSetNotUH
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MulVecMapMem

noncomputable section

open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open Formalism.L2.SG.RealObj.EnergyIntTor Formalism.L2.SG.RealObj.EnergyIntLoc Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.EnergyConvJ

section Model

variable {k r : ℕ}

theorem uw_fix {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) {w : Fin (2 * r + k + 1) → ℂ} (hw : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k → w i = 0) :
    h *ᵥ w = w := by
  obtain ⟨-, hfix, -⟩ := hh
  have key : ∀ i : Fin (2 * r + k + 1), w i • (h *ᵥ Pi.single i (1:ℂ)) = w i • Pi.single i (1:ℂ) := by
    intro i
    have hlt := i.isLt
    by_cases h1 : i.val < r
    · have he : eI k r ⟨i.val, h1⟩ = i := Fin.ext rfl
      have := (hfix ⟨i.val, h1⟩).1
      rw [he] at this
      exact congrArg (fun v => w i • v) this
    · by_cases h2 : r + k < i.val
      · have he : esI k r ⟨2 * r + k - i.val, by omega⟩ = i := Fin.ext (by
          show 2 * r + k - (2 * r + k - i.val) = i.val
          omega)
        have := (hfix ⟨2 * r + k - i.val, by omega⟩).2
        rw [he] at this
        exact congrArg (fun v => w i • v) this
      · rw [hw i (by omega) (by omega), zero_smul, zero_smul]
  have hw' : w = ∑ i, w i • Pi.single i (1:ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw']
  rw [show h *ᵥ (∑ i, w i • Pi.single i (1:ℂ)) = ∑ i, w i • (h *ᵥ Pi.single i (1:ℂ)) by
      simp only [← Matrix.mulVecLin_apply, map_sum, map_smul]]
  rw [Finset.sum_congr rfl (fun i _ => key i), ← hw']

private theorem mulVec_single_one_apply_gauge_lattice_shifts {n : ℕ} (m : Matrix (Fin n) (Fin n) ℂ) (j i : Fin n) :
    (m *ᵥ Pi.single j (1:ℂ)) i = m i j := by
  first
  | simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  | simp [Pi.single_apply]

theorem sset_col {z : Fin (2 * r + k + 1) → ℂ} {M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hM : M ∈ Sset k r z) (a : Fin r) (i : Fin (2 * r + k + 1)) (hi : a.val ≤ i.val) :
    ((M - 1) *ᵥ bvec (eI k r a)) i = 0 := by
  have ha := a.isLt
  delta Sset at hM
  simp only [Set.mem_setOf_eq] at hM
  obtain ⟨h, hh, m, hm, rfl⟩ := hM
  delta Nset at hm
  simp only [Set.mem_setOf_eq] at hm
  obtain ⟨-, hm1, -⟩ := hm
  have hfix : h *ᵥ (m *ᵥ bvec (eI k r a)) = m *ᵥ bvec (eI k r a) := by
    apply uw_fix hh
    intro j hj1 hj2
    have hne : j ≠ eI k r a := fun e => by
      have := congrArg Fin.val e
      change j.val = a.val at this
      omega
    have := hm1 a j (by omega)
    rw [show bvec (eI k r a) = Pi.single (eI k r a) (1:ℂ) from rfl, mulVec_single_one_apply_gauge_lattice_shifts, this]
    simp [hne]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hfix]
  rw [show bvec (eI k r a) = Pi.single (eI k r a) (1:ℂ) from rfl, Pi.sub_apply, mulVec_single_one_apply_gauge_lattice_shifts, hm1 a i hi]
  simp [Pi.single_apply]

theorem sub_one_mulVec_apply_eq_zero_of_mem_Sset {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hM : M ∈ Sset k r z) (i : Fin (2 * r + k + 1))
    (hi : r ≤ i.val) : ((M - 1) *ᵥ z) i = 0 := by
  delta inWb at hz
  delta Sset at hM
  simp only [Set.mem_setOf_eq] at hM
  obtain ⟨h, hh, m, hm, rfl⟩ := hM
  delta Nset at hm
  simp only [Set.mem_setOf_eq] at hm
  obtain ⟨-, -, hm2⟩ := hm
  obtain ⟨-, -, hz'⟩ := id hh
  have hmz : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → (m *ᵥ z) i = z i := by
    intro i hi
    have hterm : ∀ j, m i j * z j = if i = j then z j else 0 := by
      intro j
      by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
      · rw [hm2 i j hj.1 hj.2 hi]
        split_ifs <;> simp
      · rw [hz j (by omega)]
        simp
    simp [Matrix.mulVec, dotProduct, hterm]
  have hv : h *ᵥ (m *ᵥ z - z) = m *ᵥ z - z := by
    apply uw_fix hh
    intro j hj1 hj2
    rw [Pi.sub_apply, hmz j hj1, sub_self]
  have hfix : h *ᵥ (m *ᵥ z) = m *ᵥ z := by
    have hsplit : m *ᵥ z = z + (m *ᵥ z - z) := by abel
    rw [hsplit, Matrix.mulVec_add, hz', hv]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hfix, Pi.sub_apply, hmz i hi, sub_self]

theorem sum_low {n : ℕ} (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ) (a : ℕ) (ha : a ≤ r)
    (w : Fin (2 * r + k + 1) → ℂ) (hw : ∀ i : Fin (2 * r + k + 1), a ≤ i.val → w i = 0) :
    Q *ᵥ w = ∑ b : Fin r, (if b.val < a then w (eI k r b) else 0) • (Q *ᵥ bvec (eI k r b)) := by
  have hv : ∀ b : Fin r, (eI k r b).val = b.val := fun b => rfl
  have hw' : w = ∑ b : Fin r, (if b.val < a then w (eI k r b) else 0) • bvec (eI k r b) := by
    ext j
    rw [Finset.sum_apply]
    by_cases hj : j.val < a
    · rw [Finset.sum_eq_single ⟨j.val, by omega⟩]
      · have he : eI k r ⟨j.val, by omega⟩ = j := Fin.ext rfl
        simp [he, hj, bvec]
      · intro b _ hb
        have hne : j ≠ eI k r b := fun h => hb (Fin.ext (by
          have := congrArg Fin.val h
          rw [hv] at this
          simp only [Fin.val_mk]
          omega))
        simp [bvec, Pi.single_apply, hne]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [hw j (by omega)]
      refine (Finset.sum_eq_zero fun b _ => ?_).symm
      split_ifs with hb
      · have hne : j ≠ eI k r b := fun h => hj (by
          have := congrArg Fin.val h
          rw [hv] at this
          omega)
        simp [bvec, Pi.single_apply, hne]
      · simp
  conv_lhs => rw [hw']
  simp only [← Matrix.mulVecLin_apply, map_sum, map_smul]

end Model

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem qcs_e (C : Choice X θ) (τ : D.what₂.Tau) (b : Fin D.R.rS) :
    Qcs C τ *ᵥ bvec (eI D.R.k D.R.rS b) = cfS D ^ (D.R.rS - (b : ℕ)) • rv X.B.I (vOf X τ) (X.eR b) :=
  ((transpC' C τ).2.2.2 b b rfl).1

theorem qics_e (C : Choice X θ) (τ : D.what₂.Tau) (b : Fin D.R.rS) :
    Qics C τ *ᵥ rv X.B.I (vOf X τ) (X.eR b) = (cfS D ^ (D.R.rS - (b : ℕ)))⁻¹ • bvec (eI D.R.k D.R.rS b) := by
  have h1 := (transpC' C τ).1
  have hc : cfS D ^ (D.R.rS - (b : ℕ)) ≠ 0 := pow_ne_zero _ (Formalism.L2.SG.Pf.cfS_ne D)
  have e := congrArg (fun v => Qics C τ *ᵥ v) (qcs_e C τ b)
  simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_smul] at e
  rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem qcs_span (C : Choice X θ) (τ : D.what₂.Tau) (a : ℕ) (ha : a ≤ D.R.rS)
    (w : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (hw : ∀ i : Fin (2 * D.R.rS + D.R.k + 1), a ≤ i.val → w i = 0) :
    Qcs C τ *ᵥ w ∈ spanLt (fun b => rv X.B.I (vOf X τ) (X.eR b)) a := by
  rw [sum_low (Qcs C τ) a ha w hw]
  refine Submodule.sum_mem _ fun b _ => ?_
  split_ifs with hb
  · rw [qcs_e C τ b]
    apply Submodule.smul_mem
    apply Submodule.smul_mem
    delta spanLt
    exact Submodule.subset_span ⟨b, hb, rfl⟩
  · rw [zero_smul]
    exact Submodule.zero_mem _

theorem sloc_of_sset (C : Choice X θ) (τ : D.what₂.Tau) (u : D.what₂.Word) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (hx : Matrix.of (Tm C τ x) ∈ Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ)) :
    x ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ) := by
  have h2 := (transpC' C τ).2.1
  set M := Matrix.of (Tm C τ x) with hMdef
  have hU : uMat x - 1 = Qcs C τ * (M - 1) * Qics C τ := by
    show uMat x - 1 = Qcs C τ * (Qics C τ * uMat x * Qcs C τ - 1) * Qics C τ
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h2,
      show Qcs C τ * (Qics C τ * uMat x * Qcs C τ) * Qics C τ = (Qcs C τ * Qics C τ) * uMat x * (Qcs C τ * Qics C τ) by
        simp only [Matrix.mul_assoc], h2, Matrix.one_mul, Matrix.mul_one]
  refine ⟨fun a => ?_, ?_⟩
  · rw [hU, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, qics_e C τ a, Matrix.mulVec_smul, Matrix.mulVec_smul]
    refine Submodule.smul_mem _ _ (qcs_span C τ a.val a.isLt.le _ fun i hi => sset_col hx a i hi)
  · rw [hU, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, zc_eq C u τ]
    exact qcs_span C τ D.R.rS le_rfl _ fun i hi => sub_one_mulVec_apply_eq_zero_of_mem_Sset (Formalism.L2.SG.Pf.zTr C u τ).1 hx i hi

theorem bvec_supSub (a : ℕ) (b : Fin D.R.rS) (hb : b.val < a) :
    bvec (eI D.R.k D.R.rS b) ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.supSub D.R.k D.R.rS a := by
  show ∀ i : Fin (2 * D.R.rS + D.R.k + 1), a ≤ i.val → bvec (eI D.R.k D.R.rS b) i = 0
  intro i hi
  have hne : i ≠ eI D.R.k D.R.rS b := fun e => by
    have := congrArg Fin.val e
    change i.val = b.val at this
    omega
  show (Pi.single (eI D.R.k D.R.rS b) (1:ℂ) : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) i = 0
  simp only [Pi.single_apply, hne, if_false]

theorem qics_span (C : Choice X θ) (τ : D.what₂.Tau) (a : ℕ) (w : Fin X.B.I.n → ℂ)
    (hw : w ∈ spanLt (fun b => rv X.B.I (vOf X τ) (X.eR b)) a) :
    Qics C τ *ᵥ w ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.supSub D.R.k D.R.rS a := by
  have hle : spanLt (fun b => rv X.B.I (vOf X τ) (X.eR b)) a ≤
      (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.supSub D.R.k D.R.rS a).comap (Matrix.mulVecLin (Qics C τ)) := by
    delta spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    show Matrix.mulVecLin (Qics C τ) (rv X.B.I (vOf X τ) (X.eR b)) ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.supSub D.R.k D.R.rS a
    rw [Matrix.mulVecLin_apply, qics_e C τ b]
    exact Submodule.smul_mem _ _ (bvec_supSub a b hb)
  have := hle hw
  rwa [Submodule.mem_comap, Matrix.mulVecLin_apply] at this

theorem sset_of_sloc (C : Choice X θ) (τ : D.what₂.Tau) (u : D.what₂.Word) (x : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (hx : x ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u (vOf X τ)) :
    Matrix.of (Tm C τ x) ∈ Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
  have h1 := (transpC' C τ).1
  have h2 := (transpC' C τ).2.1
  refine Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.fwd _ _ (Tm_mem C τ x) (Formalism.L2.SG.Pf.zTr C u τ).1 ⟨fun a => ?_, ?_⟩
  · have hM : (Matrix.of (Tm C τ x) - 1) *ᵥ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.SetCorrespondence.stdX D.R.k D.R.rS a =
        cfS D ^ (D.R.rS - (a : ℕ)) • (Qics C τ *ᵥ ((uMat x - 1) *ᵥ rv X.B.I (vOf X τ) (X.eR a))) := by
      show (Qics C τ * uMat x * Qcs C τ - 1) *ᵥ bvec (eI D.R.k D.R.rS a) = _
      rw [show Qics C τ * uMat x * Qcs C τ - 1 = Qics C τ * (uMat x - 1) * Qcs C τ by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1], ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        qcs_e C τ a, Matrix.mulVec_smul, Matrix.mulVec_smul]
    rw [hM]
    exact Submodule.smul_mem _ _ (qics_span C τ a.val _ (hx.1 a))
  · have hz : Qcs C τ *ᵥ zB X (C.Qi τ) u τ = rv X.B.I (vOf X τ) (X.zR u) := by
      rw [← zc_eq C u τ, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    have hM : (Matrix.of (Tm C τ x) - 1) *ᵥ zB X (C.Qi τ) u τ =
        Qics C τ *ᵥ ((uMat x - 1) *ᵥ rv X.B.I (vOf X τ) (X.zR u)) := by
      show (Qics C τ * uMat x * Qcs C τ - 1) *ᵥ zB X (C.Qi τ) u τ = _
      rw [show Qics C τ * uMat x * Qcs C τ - 1 = Qics C τ * (uMat x - 1) * Qcs C τ by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1], ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz]
    rw [hM]
    exact qics_span C τ D.R.rS _ hx.2

end Formalism.L2.SG.RealObj.EnergyConvJ
