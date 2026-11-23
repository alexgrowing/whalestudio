import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.LamDer

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

theorem rowsZ_holds : RowsZ := by
  intro D X u' ψ hT μinf νinf fibInf hP hb c S hc v i0 hi0 b
  classical
  let d : Fin X.B.I.n → ℂ := fun j => if j = i0 then -1 else 1
  have hdd : ∀ j, d j * d j = 1 := by intro j; simp only [d]; split_ifs <;> norm_num
  let Dm : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ := Matrix.diagonal d
  have hDD : Dm * Dm = 1 := by
    show Matrix.diagonal d * Matrix.diagonal d = 1
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    exact hdd j
  let Du : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ := ⟨Dm, Dm, hDD, hDD⟩
  have hDmem : Du ∈ Formalism.REAL.UJ (X.B.I.ε v) := by
    show Dmᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Dm = Formalism.REAL.Jm (X.B.I.ε v)
    simp only [Dm, Formalism.REAL.Jm, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    simp only [d, Pi.star_apply]
    split_ifs <;> simp
  let g : X.B.I.Ginf := Pi.mulSingle v ⟨Du, hDmem⟩
  have hstd : ∀ w, InStd (S w) (g w) := by
    intro w i hi j
    by_cases hw : w = v
    · subst hw
      have hgi : g w = ⟨Du, hDmem⟩ := Pi.mulSingle_eq_same _ _
      rw [hgi]
      show Dm j i = _
      have hne : i ≠ i0 := fun e => hi (e ▸ hi0)
      simp only [Dm, Matrix.diagonal_apply, d]
      by_cases hji : j = i
      · subst hji; simp [hne]
      · simp [hji]
    · have hgi : g w = 1 := Pi.mulSingle_eq_of_ne hw _
      rw [hgi]
      simp [Matrix.one_apply]
  have hmem := (hc.2 g).2 hstd
  have hfix := (stabInfV_holds X u' hb (c * g * c⁻¹)).1 hmem v b
  have hgv : g v = ⟨Du, hDmem⟩ := Pi.mulSingle_eq_same _ _
  have hm : uMat ((c * g * c⁻¹) v) = uMat (c v) * Dm * uMat (c v)⁻¹ := by
    simp only [uMat, Pi.mul_apply, Pi.inv_apply, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hgv]
    rfl
  have hci : uMat (c v)⁻¹ * uMat (c v) = 1 := by simp [uMat]
  rw [hm] at hfix
  set x := uMat (c v)⁻¹ *ᵥ wV X u' v b with hxdef
  have hx : Dm *ᵥ x = x := by
    have h' := congrArg (fun y => uMat (c v)⁻¹ *ᵥ y) hfix
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hci, Matrix.one_mul] at h'
    rw [hxdef, Matrix.mulVec_mulVec]
    exact h'
  have hx0 : x i0 = 0 := by
    have h1 := congrFun hx i0
    simp only [Dm, Matrix.mulVec_diagonal, d, ↓reduceIte] at h1
    calc x i0 = ((-1) * x i0 - x i0) * (-1 / 2) := by ring
      _ = 0 := by rw [h1, sub_self, zero_mul]
  rw [beta_frame_coordinates]
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact hx0

end PI.AprimeInfW
