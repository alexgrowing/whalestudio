import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemExpSolCons
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology

namespace GlobalTheory.HCF

theorem expCurve_eq_diagUnits (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (t : ℝ) :
    expCurve E a t = GroundTheory.Automorphic.Reduction.diagUnits a
      (fun _ : Fin a => GroundTheory.Automorphic.Reduction.posIdele (K := E) (Real.exp t) (Real.exp_pos t)) := by
  rw [GlobalTheory.CuspBoundSiegel.posIdele_exp]
  have e : t • (1 : Cinf E) = fun _ => (t : ℂ) := by
    funext w; simp
  unfold expCurve
  rw [e]
  refine Units.ext ?_
  rw [GroundTheory.Automorphic.Reduction.coe_diagUnits]
  rfl

theorem absDetA_mul_expCurve (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (g : GA E a) (t : ℝ) :
    absDetA (g * expCurve E a t) = absDetA g * Real.exp (t * (a * Module.finrank ℚ E)) := by
  unfold absDetA
  rw [GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E), GroundTheory.Automorphic.Reduction.adeleAbs_units (K := E),
    map_mul, map_mul, Positive.val_mul, expCurve_eq_diagUnits, GlobalTheory.CuspBoundSiegel.ideleModule_det_diagUnits_posIdele,
    ← Real.exp_nat_mul]
  congr 2
  push_cast; ring

end GlobalTheory.HCF

end
