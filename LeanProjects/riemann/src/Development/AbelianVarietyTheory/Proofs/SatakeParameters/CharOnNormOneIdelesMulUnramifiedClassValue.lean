import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterLawsNormOneIdelesOfKernelChain
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc.ChiHom

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} {t : KerEntTied ex}

theorem chiI_det (J : Joint t H X) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) :
    chiI J (Matrix.GeneralLinearGroup.det y.1) = ((D.chiD (J.dtU y) : ℂˣ) : ℂ) := by
  have h : ∃ y' : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y'.1 = Matrix.GeneralLinearGroup.det y.1 := ⟨y, rfl⟩
  unfold chiI
  rw [dif_pos h]
  have e : h.choose = y := Subtype.ext (GlobalTheory.TwV.MuLawPf.generalLinearGroupOne_eq_of_det_eq h.choose_spec)
  rw [e]

set_option maxHeartbeats 2000000 in

theorem carries_std_of_int (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) (hy : Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E) :
    Formalism.L2.Herm.Carries y.1 (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) := by
  have hu := (Submonoid.mem_units_iff _ _).1 hy
  intro v
  show v ∈ latS (Formalism.L2.Herm.Af D.host.F) (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.Col.stdLat D.host.E 1) ↔
    _ ∈ latS (Formalism.L2.Herm.Af D.host.F) (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.Col.stdLat D.host.E 1)
  rw [Formalism.L2.Col.mem_latS_std, Formalism.L2.Col.mem_latS_std]
  have e1 : Units.val ((y.1)⁻¹) 0 0 = Units.val ((Matrix.GeneralLinearGroup.det y.1)⁻¹) := by
    rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  have e2 : ∀ i : Fin 1, (Matrix.mulVec (Units.val ((y.1)⁻¹)) v) i = Units.val ((Matrix.GeneralLinearGroup.det y.1)⁻¹) * v 0 := by
    intro i
    fin_cases i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one]
    rw [← e1]; rfl
  simp only [e2]
  constructor
  · intro h i
    exact mul_mem hu.2 (h 0)
  · intro h i
    fin_cases i
    have := mul_mem hu.1 (h 0)
    rwa [← mul_assoc, Units.mul_inv, one_mul] at this

set_option maxHeartbeats 2000000 in

theorem dtU_mem_UO (J : Joint t H X) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm)
    (hy : Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E) : J.dtU y ∈ D.UO := by
  have h := J.rel 1 ⟨_, Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D 1⟩ ⟨_, Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D 1⟩ y.1 y.2
    (carries_std_of_int y hy) y rfl
  exact (QuotientGroup.eq_one_iff _).1 (h.symm.trans (D.relDet_self _ _))

end GlobalTheory.TwV.Xc.ChiHom

namespace GlobalTheory.TwV.Xc

open GlobalTheory.TwV.Xc.ChiHom in
set_option maxHeartbeats 4000000 in

theorem chiI_hom : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => (∀ x ∈ U1 (sigD D), ∀ y ∈ U1 (sigD D), chiI J (x * y) = chiI J x * chiI J y) ∧ (∀ x ∈ U1 (sigD D), x ∈ intU D.host.F D.host.E → chiI J x = 1) ∧ (∀ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, chiI J (Matrix.GeneralLinearGroup.det y.1) = ((D.chiD (J.dtU y) : ℂˣ) : ℂ)) ∧ ∀ x ∈ U1 (sigD D), ∃ 𝔞, TaylorLogMetric.N1 D 𝔞 ∧ chiI J x = t.χ 𝔞) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _ _
  refine ⟨?_, ?_, fun y => chiI_det J y, ?_⟩
  · intro x hx y hy
    obtain ⟨x', rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hx
    obtain ⟨y', rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hy
    have e : Matrix.GeneralLinearGroup.det x'.1 * Matrix.GeneralLinearGroup.det y'.1 =
        Matrix.GeneralLinearGroup.det (x' * y').1 := by
      rw [Subgroup.coe_mul, map_mul]
    rw [e, chiI_det, chiI_det, chiI_det, map_mul, map_mul, Units.val_mul]
  · intro x hx hint
    obtain ⟨y, rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hx
    rw [chiI_det, D.chiD_UO _ (dtU_mem_UO J y hint), Units.val_one]
  · intro x hx
    obtain ⟨y, rfl⟩ := GlobalTheory.TwV.MuLawPf.exists_unitaryOne_det_eq_normOneIdele hx
    refine ⟨t.idl (QuotientGroup.mk (J.dtU y)), (t.idl_ok.2.1 _).2 ⟨_, rfl⟩, ?_⟩
    rw [chiI_det, t.χ_rec, TaylorLogMetric.chiRec_idl D t.idl t.idl_ok.1]
    rfl

end GlobalTheory.TwV.Xc

end
