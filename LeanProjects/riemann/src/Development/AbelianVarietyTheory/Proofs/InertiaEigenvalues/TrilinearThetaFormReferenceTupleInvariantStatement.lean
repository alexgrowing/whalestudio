import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrilinearThetaFormReferenceTupleInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacteristicFunctionIntegralApply
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

open GlobalTheory.RefPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trilinearThetaForm_referenceTuple_invariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → GlobalTheory.Mem.R3.Holds R F → R.toRealDat.ExAt → ∀ (M : MtFam D) (Ad : GlobalTheory.HeightCounting.MtAd Y M) (i : Fin D.R.m) (X : GlobalTheory.NPin.RowMod D (GlobalTheory.RefTheta.repY Y) (i.1 + 1)) (hc : GlobalTheory.RefTheta.IsCanonR Y i rfl X) (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r) (φ : (R.cV i).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D i) (Formalism.IndefR.Links.Wc D i) → ℂ)), φ ∈ GlobalTheory.RefTheta.Om Ad i hc → ∀ (Fm Fm' : ↥(NG.AFall D.host.E D.R.nV (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.ρ)) (y y' : ↥X.C), (Fm' : GAf D.host.E D.R.nV → (M D.what₂.mu0 (i.1 + 1) (by omega) (by omega)).wt.W) = NG.rt D.host.E D.R.nV h Fm → (y' : X.A) = X.ρ g y → GlobalTheory.RefTheta.lamV Ad i hc (GlobalTheory.ThetaTri.valAct1 (GlobalTheory.RefTheta.omStd Ad i (GlobalTheory.RefTheta.t0 Y)) (h, g) φ) Fm' y' = GlobalTheory.RefTheta.lamV Ad i hc φ Fm y := by
  first | exact @GlobalTheory.RefTheta.lamV_inv | exact GlobalTheory.RefTheta.lamV_inv | (intros; apply GlobalTheory.RefTheta.lamV_inv <;> assumption)
