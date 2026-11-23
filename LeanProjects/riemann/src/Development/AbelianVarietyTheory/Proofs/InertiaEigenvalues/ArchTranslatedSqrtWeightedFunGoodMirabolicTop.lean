import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WtOfLastRowOfDetPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.ZUnf

section H

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

omit [NumberField E] [IsTotallyComplex E] in
theorem secRow_eq_rowMat {R : Type} [CommRing R] (y : Fin (m + 1) → R) :
    secRow y = GlobalTheory.RSTheta.rowMat (Fin.last m) y := by
  ext i j
  simp only [secRow, GlobalTheory.RSTheta.rowMat, Matrix.of_apply, Matrix.updateRow_apply]
  by_cases h : i = Fin.last m
  · subst h; simp
  · rw [if_neg h, if_neg (fun e => h (Fin.ext (by simpa using e)))]

omit [NumberField E] [IsTotallyComplex E] in

theorem secInv_eq_inv_rowGL {y : Fin (m + 1) → Cinf E} (hy : y ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m)) :
    secInv y = (GlobalTheory.RSTheta.rowGL (Fin.last m) y)⁻¹ := by
  have hu := GlobalTheory.RSTheta.isUnit_of_mem_rowSet hy
  have hd : IsUnit (secRow y).det := by rw [secRow_eq_rowMat, GlobalTheory.RSTheta.det_rowMat]; exact hu
  rw [secInv, dif_pos hd]
  congr 1
  apply Units.ext
  rw [GlobalTheory.RSTheta.val_rowGL hu, ← secRow_eq_rowMat]
  rfl

theorem continuous_yInf : Continuous (yInf : GA E (m + 1) → Fin (m + 1) → Cinf E) :=
  continuous_pi fun i => GlobalTheory.ShortVecDecay.continuous_pInf.comp
    (Units.continuous_val.matrix_elem (Fin.last m) i)

omit [NumberField E] [IsTotallyComplex E] in
theorem continuous_sqrtC {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : Continuous Φ) : Continuous (sqrtC Φ) :=
  Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (Complex.continuous_re.comp hΦ))

theorem lastRow_mul_of_row {h g : GA E (m + 1)}
    (hr : ∀ l, (h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l) :
    GlobalTheory.ZEul.lastRow (h * g) = GlobalTheory.ZEul.lastRow g := by
  funext j
  simp only [GlobalTheory.ZEul.lastRow, Units.val_mul, Matrix.mul_apply, hr]
  rw [← Matrix.mul_apply, Matrix.one_mul]

theorem blkU_lastRow {r : ℕ} (hr : r ≤ m) (x : UnipotentBlockColumnIndex (m + 1) r m → Ad E) (l : Fin (m + 1)) :
    ((blkU x : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l := by
  change (1 + posM Subtype.val x : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l = _
  rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero]
  intro t _
  rw [Matrix.single_apply_of_ne]
  rintro ⟨e1, -⟩
  have h1 : (t.1.1 : ℕ) = m := by rw [e1]; simp
  have h2 := t.2.1
  omega

omit [IsTotallyComplex E] in
theorem ratGL_lastRow {γ : GL (Fin (m + 1)) E} (hγ : IsMir m γ) (l : Fin (m + 1)) :
    ((ratGL E (m + 1) γ : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l =
      (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l := by
  change algebraMap E (Ad E) (γ.val (Fin.last m) l) = _
  rw [hγ (Fin.last m) l (Or.inl (by simp))]
  by_cases h : Fin.last m = l
  · simp [Matrix.one_apply, h]
  · simp [Matrix.one_apply, h]

theorem continuous_fT {φ : GA E (m + 1) → ℂ} (hφ : Continuous φ) {Φ : (Fin (m + 1) → Cinf E) → ℂ}
    (hΦ : Continuous Φ) (hs : tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m)) : Continuous (fT φ Φ) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  by_cases hp : yInf g ∈ tsupport Φ
  · have hU : GlobalTheory.RSTheta.rowSet E (Fin.last m) ∈ nhds (yInf g) :=
      (GlobalTheory.RSTheta.isOpen_rowSet (E := E) (Fin.last m)).mem_nhds (hs hp)
    have hc : ContinuousOn (fun u => infGL E (m + 1) (secInv u)) (GlobalTheory.RSTheta.rowSet E (Fin.last m)) := by
      refine (GlobalTheory.RSTheta.continuousOn_inv_rowGL (E := E) (Fin.last m)).congr fun u hu => ?_
      simp only [secInv_eq_inv_rowGL hu, map_inv]
    have h1 : ContinuousAt (fun g : GA E (m + 1) => g * infGL E (m + 1) (secInv (yInf g))) g :=
      continuousAt_id.mul ((hc.continuousAt hU).comp continuous_yInf.continuousAt)
    exact (hφ.continuousAt.comp h1).mul ((continuous_sqrtC hΦ).comp continuous_yInf).continuousAt
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [continuous_yInf.continuousAt.eventually (notMem_tsupport_iff_eventuallyEq.1 hp)] with q hq
    simp [fT, sqrtC, hq]

end H

theorem good_fT : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (φ : GA E (m + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => φ (blkU x * g)) = 0) →
    ∀ Φ : (Fin (m + 1) → Cinf E) → ℂ, Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    ∀ ψ : AddChar (Ad E) ℂ, Good ψ m (GlobalTheory.ZUnf.fT φ Φ) := by
  intro E _ _ _ m φ hφ hl hv Φ hΦ hs ψ
  refine ⟨continuous_fT hφ hΦ hs, ?_, ?_, ?_⟩
  · intro γ hγ g
    rw [fT_of_lastRow (lastRow_mul_of_row (ratGL_lastRow hγ)), mul_assoc, hl, fT]
  · intro k hk y g
    have he : IsEmpty (UnipotentBlockColumnIndex (m + 1) k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
    have hy : y = 0 := Subsingleton.elim _ _
    subst hy
    have hd : dot (eLast (m + 1) k) (0 : UnipotentBlockColumnIndex (m + 1) k k → Ad E) = 0 := by simp [dot]
    rw [hd, AddChar.map_zero_eq_one, one_mul]
    unfold blkU
    rw [posU_zero, one_mul]
  · intro r hr hrm g
    have e : (fun x : UnipotentBlockColumnIndex (m + 1) r m → Ad E => fT φ Φ (blkU x * g)) = fun x =>
        sqrtC Φ (yInf g) * φ (blkU x * (g * infGL E (m + 1) (secInv (yInf g)))) := by
      funext x
      rw [fT_of_lastRow (lastRow_mul_of_row (blkU_lastRow hrm x)), mul_comm, mul_assoc]
    rw [e, avg_const_mul, hv r hr hrm, mul_zero]

end GlobalTheory.ZUnf

end
