import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstanceIotaReadoutRealTrivialStabilizerUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.KsetAt

theorem mem_Kset_iff_moves : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (v : GlobalTheory.FinPl.Pl D) (κ : GA D (D.sp.Y 0)), κ ∈ grpAt (D.sp.Y 0) (· = v) → ((iotaX X h κ).2 ∈ X.B.I.Kset ↔ Moves (D.sp.Y 0) κ (latS D) (latS D) (· = v)) := by
  intro D X h v κ hκ
  have hlat : Submodule.IsLattice D.host.E (latS D) :=
    GlobalTheory.StdFrames.isLattice_crdLat (D.sp.Y 0) (D.sp.Y 0).standardTuple_isLattice
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ (latS D) hlat
  have h1 := ((GlobalTheory.SeeConjReadIota.read_iota X h β hβ κ).2.1)
  have h2 := GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_of_fg (D.sp.Y 0) β (latS D) hβ hlat.fg κ
  have h3 : κ ∈ GlobalTheory.AdelicU.levelOpen D.sp.cm.sig (D.sp.Y 0).gram (latS D) ↔
      Moves (D.sp.Y 0) κ (latS D) (latS D) (· = v) :=
    ⟨fun hk => GlobalTheory.FinPl.KOpen.moves_of_levelOpen (D.sp.Y 0) (latS D) hlat.fg (· = v) hk,
     fun hm => GlobalTheory.FinPl.KOpen.levelOpen_of_inK (D.sp.Y 0) (latS D) hlat.fg (· = v) ⟨hκ, hm⟩⟩
  exact h1.trans (h2.trans (GlobalTheory.AdelicU.mem_levelOpen.symm.trans h3))

end GlobalTheory.Core.Mi.KsetAt
