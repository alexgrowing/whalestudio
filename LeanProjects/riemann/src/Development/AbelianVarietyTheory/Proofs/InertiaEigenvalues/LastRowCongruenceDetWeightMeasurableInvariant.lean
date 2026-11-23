import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WtOfLastRowOfDetPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NegOneNotMemNatLat
import GroundTheory.GlobalFields.Adele.Compact
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.ZUnfWt

open GlobalTheory.ZUnf

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

omit [IsTotallyComplex E] in

theorem lastRow_mul_of_mem {h : GA E (m + 1)} (hh : h ∈ mirU (Ad E) (m + 1) m) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (h * g) = GlobalTheory.ZEul.lastRow g := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [(mem_mirU_last.1 hh) (Fin.last m), if_pos rfl, one_mul]
  · intro l _ hl
    rw [(mem_mirU_last.1 hh) l, if_neg hl, zero_mul]
  · simp

omit [NumberField E] [IsTotallyComplex E] in

theorem det_blkU {R : Type} [CommRing R] {a k : ℕ} (y : UnipotentBlockColumnIndex a k k → R) : (blkU y : GL (Fin a) R).val.det = 1 := by
  have h := mem_mirU_zero.1 (blkU_mem_mirU 0 y)
  rw [Matrix.det_of_upperTriangular (fun i j hij => h.1 i j hij)]
  simp [h.2]

omit [IsTotallyComplex E] in
theorem detPow_blkU (x : ℝ) {k : ℕ} (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) : detPow E (m + 1) x (blkU y) = 1 := by
  have hd : Matrix.GeneralLinearGroup.det (blkU y : GA E (m + 1)) = 1 := Units.ext (det_blkU y)
  unfold detPow chiDet
  rw [MonoidHom.comp_apply, hd, map_one]
  simp

omit [IsTotallyComplex E] in

theorem isClosed_natLat (N : ℕ) : IsClosed (natLat E N) := by
  haveI : T2Space (Af E) := inferInstanceAs (T2Space (RestrictedProduct _ _ _))
  have e : natLat E N = (fun z => (N : Af E) * z) '' (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
  rw [e]
  exact ((GroundTheory.Global.isCompact_integralFiniteAdeles E).image (continuous_const.mul continuous_id)).isClosed

omit [IsTotallyComplex E] in
theorem continuous_yFin : Continuous (yFin (E := E) (m := m)) :=
  continuous_pi fun i => (continuous_snd : Continuous (GlobalTheory.RSJ.pFin E)).comp
    ((Units.continuous_val : Continuous fun g : GA E (m + 1) => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))).matrix_elem
      (Fin.last m) i)

omit [IsTotallyComplex E] in
theorem continuous_detPow (x : ℝ) : Continuous (detPow E (m + 1) x) :=
  continuous_norm.comp (Units.continuous_val.comp
    ((GlobalTheory.HeckeGal.Model.absPow E x).2.1.comp Matrix.GeneralLinearGroup.continuous_det))

omit [IsTotallyComplex E] in
theorem measurable_wt (N : ℕ) (x : ℝ) : Measurable (wt (E := E) (m := m) N x) := by
  let S : Set (Fin (m + 1) → Af E) := {y | ∀ i : Fin (m + 1), y i - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ natLat E N}
  have hS : IsClosed S := by
    have e : S = ⋂ i : Fin (m + 1),
        (fun y : Fin (m + 1) → Af E => y i - (if (i : ℕ) + 1 = m + 1 then 1 else 0)) ⁻¹' natLat E N := by
      ext y; simp [S]
    rw [e]
    exact isClosed_iInter fun i => (isClosed_natLat N).preimage ((continuous_apply i).sub continuous_const)
  have hm : MeasurableSet {g : GA E (m + 1) | yFin g ∈ S} := (hS.preimage continuous_yFin).measurableSet
  have hind : Measurable fun g : GA E (m + 1) => indN N (yFin g) := by
    unfold indN
    exact Measurable.ite hm measurable_const measurable_const
  exact ((Complex.measurable_re.comp hind).mul (continuous_detPow x).measurable).real_toNNReal

theorem wt_measurable_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m N : ℕ) (x : ℝ),
    Measurable (GlobalTheory.ZUnf.wt (E := E) (m := m) N x) ∧
    (∀ γ ∈ mirU E (m + 1) m, ∀ g, GlobalTheory.ZUnf.wt N x (ratGL E (m + 1) γ * g) = GlobalTheory.ZUnf.wt N x g) ∧
    ∀ (k : ℕ) (y : UnipotentBlockColumnIndex (m + 1) k k → Ad E) (g : GA E (m + 1)), GlobalTheory.ZUnf.wt N x (blkU y * g) = GlobalTheory.ZUnf.wt N x g := by
  intro E _ _ _ m N x
  refine ⟨measurable_wt N x, fun γ hγ g => ?_, fun k y g => ?_⟩
  · refine wt_of_lastRow_of_detPow (lastRow_mul_of_mem (map_mem_mirU _ hγ) g) ?_
    rw [GlobalTheory.RSJ.Model.detPow_mul, GlobalTheory.RSJ.Model.detPow_ratGL, one_mul]
  · refine wt_of_lastRow_of_detPow (lastRow_mul_of_mem (blkU_mem_mirU m y) g) ?_
    rw [GlobalTheory.RSJ.Model.detPow_mul, detPow_blkU, one_mul]

end GlobalTheory.ZUnfWt
