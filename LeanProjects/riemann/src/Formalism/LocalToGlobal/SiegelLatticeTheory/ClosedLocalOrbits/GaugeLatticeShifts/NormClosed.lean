import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormLinks
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsColLatRepS
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNMul
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormHSBlocks

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.NormCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NormExpSatC' : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') →
    NormExpSat (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u')

def SatGramC' : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    SatGram (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (Y.tO u u').genSet
        (Aset Y.TR (Y.cs u)) (Aset Y.TR (Y.cs u')) ∧
      SatGram (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') (Y.tO u u').ngSet
        (Aset Y.TR (Y.cs u)) (Aset Y.TR (Y.cs u'))

def ChiNBiC : Prop := ∀ (D : D7) (X : HidaSetting D), ChiNBi X

def NeatC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK

def LeviOntoC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.Pf.NormSteps.LeviOntoS Y.TR (Y.cs u)

theorem colLatRepC (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) :
    Formalism.L2.SG.Pf.NormSteps.ColLatRepS (Y.cs u) Y.hK :=
  Formalism.L2.SG.Pf.NormSteps.column_lattice_representatives (Y.cs u) Y.hK (Y.rowsOK u)

def MassAC : Prop := ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), MassA Y.TR (X.Fu u) (Y.cs u)

theorem chiNIndepC_holds : ChiNIndepC := fun _ X Y u u' =>
  chiNIndep_of_frameTie (cs := Y.cs u) (cs' := Y.cs u') (hTF := Full.frameTie (X := X) u u')

theorem normExpSatC'_of (hCL : NeatC) (hO : LeviOntoC) (hM : MassAC) (hS : SatGramC') : NormExpSatC' := by
  intro D X Y u u' _ _ _ hAbs
  obtain ⟨hSg, hSn⟩ := hS D X Y u u' ‹_› ‹_› ‹_›
  have hTF := Full.frameTie (X := X) u u'
  have hF := colFree_steps (TR := Y.TR) (F0 := X.Fu u) (cs := Y.cs u) (hK := Y.hK) (hR := Y.colReps u)
    (hCL := hCL D X Y u) (hO := hO D X Y u) (hRep := colLatRepC D X Y u) (hMass := hM D X Y u)
  have hF' := colFree_steps (TR := Y.TR) (F0 := X.Fu u') (cs := Y.cs u') (hK := Y.hK) (hR := Y.colReps u')
    (hCL := hCL D X Y u') (hO := hO D X Y u') (hRep := colLatRepC D X Y u') (hMass := hM D X Y u')
  exact normExpSat_of (TR := Y.TR) (cs := Y.cs u) (cs' := Y.cs u') (FdN := Y.FN u) (FdN' := Y.FN u')
    (hHS := hilbert_schmidt_blocks) (hGam := Formalism.L2.SG.NormCut.gamma_product_sum_holds)
    (hPsi := Formalism.L2.SG.NormCut.psi_natural_equiv_holds) (hAbs := hAbs)
    (hChi := chiNIndep_of_frameTie (cs := Y.cs u) (cs' := Y.cs u') (hTF := hTF))
    (sc := scOf Y.TR (Y.cs u)) (sc' := scOf Y.TR (Y.cs u'))
    (hPh := colPhase_holds (TR := Y.TR) (cs := Y.cs u) (cs' := Y.cs u') (hTF := hTF))
    (A := Aset Y.TR (Y.cs u)) (A' := Aset Y.TR (Y.cs u')) (hF := hF) (hF' := hF') (hSg := hSg) (hSn := hSn)

end Formalism.L2.SG.NormCut
