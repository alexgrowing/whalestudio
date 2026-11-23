import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FormHermitianPositive
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviOntoSEnd
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianModuleBetaCongruence
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.SlabMajPt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_supp {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    ∃ (h : Hfin X u') (κ : X.B.I.Gf), κ ∈ X.K2 ∧
      t.pt.2⁻¹ * Formalism.L2.SG.Pf.Slab.aB Y u t.lam = (h : X.B.I.Gf) * X.xu u' * κ := by
  have hTF := Full.frameTie (X := X) u u'
  have hKk := Formalism.L2.SG.Closed.TermK_holds (F0 := X.Fu u) (F0' := X.Fu u') (Y.cs u) (Y.cs u') t
  have hNk := Formalism.L2.SG.Closed.AdmN_holds (Y.cs u) (Y.cs u') hTF t
  have hGk := Formalism.L2.SG.Closed.AdmPar_holds (Y.cs u) (Y.cs u') hTF t
  obtain ⟨h, hc, -, hlev⟩ := Formalism.L2.SG.Pf.NormSteps.levi_onto_reduction Y.TR (Y.cs u')
    ⟨t.lam', t.mem'⟩
    (levi Y.TR (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
      ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.pt))⁻¹
  have hNc := Formalism.L2.SG.NormCut.ncong_colDiff u' _ _ hc
  have hGc := Formalism.L2.SG.NormCut.good_of_ncong X hc hNc
  have hKkc := Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I hKk hc
  have hNkc := Formalism.L2.SG.NormCut.ncong_mul X hKk hNk hNc
  have hGkc := Formalism.L2.SG.NormCut.good_mul X hGk hGc
  have hlevkc := Formalism.L2.SG.NormCut.levi_mul Y.TR hGk hGc
  rw [hlev, mul_inv_cancel] at hlevkc
  have hK2 := Formalism.L2.SG.NormCut.mem_level_of_unitriangular Y.TR hGkc hNkc (fun v => by
    rw [hlevkc, Pi.one_apply]
    exact Formalism.L2.SG.GGMirabolic.isUni_one)
  refine ⟨h, _, Y.hK.2.2.1 _ hK2, ?_⟩
  simp only [Formalism.L2.SG.Pf.Slab.aB, kOf, Formalism.L2.SG.Pf.NormSteps.colDS]
  group

end Formalism.L2.SG.Pf.SlabMajPt
