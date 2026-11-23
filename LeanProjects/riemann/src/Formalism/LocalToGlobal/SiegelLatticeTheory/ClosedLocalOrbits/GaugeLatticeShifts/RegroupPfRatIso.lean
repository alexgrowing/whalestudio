import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfTermCar
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp
open Formalism.L2.SG.HidaSetting Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

theorem rational_isomorphism_holds : RatIsoC := by
  intro D X γ hγ
  obtain ⟨g, hgU, h1, h2⟩ := PI.UnitaryGroupMassFormula.LCG.mem_gf X.B.I ⟨γ, hγ⟩
  let φ := (X.ιE : X.B.I.E →+* D.host.E).mapMatrix (m := Fin X.B.I.n)
  let Mg := φ (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  let Mi := φ ((g⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)
  have hmul1 : Mg * Mi = 1 := by
    simp only [Mg, Mi]
    rw [← map_mul, Units.mul_inv, map_one]
  have hmul2 : Mi * Mg = 1 := by
    simp only [Mg, Mi]
    rw [← map_mul, Units.inv_mul, map_one]
  let σ : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
    LinearEquiv.ofLinear (Matrix.toLin X.bas X.bas Mg) (Matrix.toLin X.bas X.bas Mi)
      (by rw [← Matrix.toLin_mul, hmul1, Matrix.toLin_one])
      (by rw [← Matrix.toLin_mul, hmul2, Matrix.toLin_one])
  have hcrd : ∀ y, X.crd (σ y) = (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := by
    intro y
    funext i
    show X.ιE.symm (X.bas.repr (Matrix.toLin X.bas X.bas Mg y) i) = _
    rw [Matrix.toLin_apply, Module.Basis.repr_sum_self]
    simp [Mg, φ, Matrix.mulVec, dotProduct, Formalism.L2.SG.HidaSetting.HidaSetting.crd,
      Formalism.L2.SG.HidaSetting.crdOf, map_sum, map_mul]
  refine ⟨σ, ⟨g, hgU, h1, h2, hcrd⟩, fun x y => ?_⟩
  rw [← Formalism.L2.SG.PoincareInHH.Cut.hform_crd (X := X) (σ x) (σ y),
    ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd (X := X) x y, hcrd, hcrd,
    Formalism.L2.SG.PoincareInHH.Cut.hform_mulVec _ _ _ hgU]

end Formalism.L2.SG.Pf.RegroupPf
