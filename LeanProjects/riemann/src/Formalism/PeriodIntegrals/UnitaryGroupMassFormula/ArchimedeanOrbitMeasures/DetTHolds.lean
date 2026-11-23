import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamDer

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def gramH {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) D.host.E :=
  Matrix.of fun i j => (VS D).hT (wF X u' i) (wF X u' j)

theorem gram_sq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) :
    gramH X u' * gramH X u' =
    Matrix.diagonal (Fin.append (Fin.snoc (fun _ : Fin D.R.rS => (1 : D.host.E))
      ((((D.mem u').A.T : ℕ) : D.host.E) * (((D.mem u').A.T : ℕ) : D.host.E))) (fun _ : Fin D.R.rS => 1)) := by
  have h1 : ∀ b : Fin D.R.rS, Fin.last D.R.rS ≠ b.castSucc := fun b h => (Fin.castSucc_lt_last b).ne' h
  have h1' : ∀ b : Fin D.R.rS, b.castSucc ≠ Fin.last D.R.rS := fun b h => (Fin.castSucc_lt_last b).ne h
  have h2 : ∀ (x : Fin (D.R.rS + 1)) (y : Fin D.R.rS), Fin.castAdd D.R.rS x ≠ Fin.natAdd (D.R.rS + 1) y := by
    intro x y h
    have := congrArg Fin.val h
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
    omega
  have h2' : ∀ (x : Fin (D.R.rS + 1)) (y : Fin D.R.rS), Fin.natAdd (D.R.rS + 1) y ≠ Fin.castAdd D.R.rS x :=
    fun x y h => h2 x y h.symm
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_add, Fin.sum_univ_castSucc]
  refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i <;> refine Fin.addCases (fun j1 => ?_) (fun j2 => ?_) j
  · refine Fin.lastCases ?_ (fun a => ?_) i1 <;> refine Fin.lastCases ?_ (fun b => ?_) j1 <;>
      simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
        hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]
  · refine Fin.lastCases ?_ (fun a => ?_) i1 <;>
      simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
        hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]
  · refine Fin.lastCases ?_ (fun b => ?_) j1 <;>
      simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
        hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]
  · simp [gramH, wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ff, X.ef,
      hT_fe, hT_ze, hT_zf, (X.zu_orth u' _).1, (X.zu_orth u' _).2, X.zu_norm, Matrix.diagonal_apply, h1, h1', h2, h2', eq_comm]

theorem detT_holds : DetT := by
  intro D X u' ψ hT μinf νinf fibInf hP v
  have hGH : gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) = (gramH X u').map X.ιE.symm := by
    ext i j
    rw [gram_eq]
    rfl
  have hdet : (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det = X.ιE.symm (gramH X u').det := by
    rw [hGH]
    exact (RingHom.map_det (X.ιE.symm : D.host.E →+* X.B.I.E) _).symm
  have hsq : (gramH X u').det ^ 2 = (((D.mem u').A.T : ℕ) : D.host.E) ^ 2 := by
    have h := congrArg Matrix.det (gram_sq X u')
    rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_add, Fin.prod_univ_castSucc] at h
    simp only [Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const_one,
      one_mul, mul_one] at h
    rw [sq, sq]
    exact h
  have hz : (X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det) ^ 2 =
      ((((D.mem u').A.T : ℕ) : ℂ)) ^ 2 := by
    rw [hdet, ← map_pow, ← map_pow, hsq, map_pow, map_pow, map_natCast, map_natCast]
  have hn : ‖X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det‖ ^ 2 = (Tw u') ^ 2 := by
    rw [← norm_pow, hz, norm_pow, Complex.norm_natCast]
    rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (by unfold Tw; positivity)).1 hn

end PI.AprimeInfW
