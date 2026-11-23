import Formalism.LocalToGlobal.Columns.LevPackPSameCar
import Formalism.LocalToGlobal.Columns.LastVectorMemSpan
import Formalism.LocalToGlobal.Columns.TiedXpU
import Formalism.LocalToGlobal.Columns.CharactersLevelZeroAgree

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d)

theorem gram_eq_one_of_standard (hS : SpStd d.toColBase) : d.sp.X'.gram = 1 := by
  refine Matrix.ext fun x y => ?_
  show d.sp.X'.hT (d.sp.X'.frame x) (d.sp.X'.frame y) = _
  rw [hS.P_on, Matrix.one_apply]

theorem coordLattice_selfDual_auxiliary (hS : SpStd d.toColBase) : Formalism.L2.Herm.crdLat d.sp.X' d.sp.X'.L0 = stdLat d.X.E d.sp.X'.rank := by
  unfold Formalism.L2.Herm.crdLat
  rw [hS.selfDual_span_frame_auxiliary]
  refine th_map_span_std (Formalism.L2.Herm.crd d.sp.X') _ (Equiv.refl _) fun a => ?_
  funext j
  show d.sp.X'.frame.equivFun (d.sp.X'.frame a) j = _
  rw [Basis.equivFun_self, Pi.single_apply]
  congr 1
  exact propext eq_comm

theorem hp_crdLat_map (L : Submodule (𝓞 d.host.E) (Fin (d.R.N d.R.m - 1) → d.host.E)) :
    Formalism.L2.Herm.crdLat d.sp.X' (L.map (((CF.crdP (d.colRec a)).symm :
      (Fin (d.R.N d.R.m - 1) → d.host.E) →ₗ[d.host.E] d.sp.X'.V).restrictScalars (𝓞 d.host.E))) =
      Formalism.L2.Forms.reL (CF.rankP (d.colRec a)).symm L := by
  unfold Formalism.L2.Herm.crdLat Formalism.L2.Forms.reL
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  funext j
  show d.sp.X'.frame.equivFun ((CF.crdP (d.colRec a)).symm x) j = _
  unfold CF.crdP
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rfl

def hCrdP (u : d.what₂.Word) : HCrdP d.X (d.R.N d.R.m - 1) fun c : PCl d => (d.reprP c).1.N where
  n' := d.sp.X'.rank
  hn := CF.rankP (d.colRec a)
  J := d.sp.X'.gram
  hJ := gram_eq_one_of_standard hS
  l0 := Formalism.L2.Herm.crdLat d.sp.X' d.sp.X'.L0
  hl0 := by rw [hp_baseLb_empty, th_reL_std, coordLattice_selfDual_auxiliary hS]
  lat := fun c => Formalism.L2.Herm.crdLat d.sp.X' (hqLatP (parabolicClassAgreement a hS hH hP u) c)
  hlat := fun c => hp_crdLat_map a _

def hermPackP (u : d.what₂.Word) :=
  levPackP d.sp.cm d.hPr d.σ₀ d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c) (hCrdP a hS hH hP u)

set_option maxHeartbeats 4000000 in

def levelExponentAtT (u : d.what₂.Word) : AtTXp (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi) :=
  xpOf (tildeLatticeAgreement a hS hH hP u)
    (LevPackP.toStep (S := d.sp.X') (lat := hqLatP (parabolicClassAgreement a hS hH hP u)) (hermPackP a hS hH hP u))
    (LevPackP.toCls (S := d.sp.X') (lat := hqLatP (parabolicClassAgreement a hS hH hP u)) (hermPackP a hS hH hP u))

theorem th_carP (u : d.what₂.Word) :
    Formalism.L2.Forms.SameCar (CF.rankP (d.colRec a)) (Formalism.L2.Herm.crdLat d.sp.X' d.sp.X'.L0) (parabolicClassAgreement a hS hH hP u).lev.Lb
      (levelExponentAtT a hS hH hP u).levP.Uloc (parabolicClassAgreement a hS hH hP u).lev.Uloc
      (levelExponentAtT a hS hH hP u).levP.U (parabolicClassAgreement a hS hH hP u).lev.U
      (fun c => ((levelExponentAtT a hS hH hP u).clsP.y c).1) (fun c => ((parabolicClassAgreement a hS hH hP u).y c).1)
      (fun c t => ((levelExponentAtT a hS hH hP u).clsP.stabI c t).1) (fun c t => ((parabolicClassAgreement a hS hH hP u).stabI c t).1) :=
  levelPacking_sameCarrier d.sp.cm d.hPr d.σ₀ d.levP.inv d.reprP hP _ (hCrdP a hS hH hP u) (crdPr a hS hH)

theorem th_latP (u : d.what₂.Word) (c : PCl d) :
    (parabolicClassAgreement a hS hH hP u).lat c = ((levelExponentAtT a hS hH hP u).lattice₂ c).map
      ((CF.crdP (d.colRec a) : d.sp.X'.V →ₗ[d.host.E] (Fin (d.R.N d.R.m - 1) → d.host.E)).restrictScalars (𝓞 d.host.E)) :=
  hqLatP_crd (parabolicClassAgreement a hS hH hP u) c

theorem joint_lastVector (u : d.what₂.Word) :
    (tildeLatticeAgreement a hS hH hP u).z0 = CF.crdN (d.colRec a) d.R.m le_rfl (levelExponentAtT a hS hH hP u).z0 :=
  lastVector_coords (tildeLatticeAgreement a hS hH hP u)

theorem th_ga (u : d.what₂.Word) (c : PCl d) :
    ((tildeLatticeAgreement a hS hH hP u).ga c).1 = Formalism.L2.Forms.reGL (CF.rankN (d.colRec a) d.R.m le_rfl) _
      (Formalism.L2.Herm.toGLb (d.sp.X d.R.m).frame ((levelExponentAtT a hS hH hP u).tilG c).1) :=
  (hqG_re d.R.m le_rfl ((tildeLatticeAgreement a hS hH hP u).ga c)).symm

end Formalism.L2.Col
