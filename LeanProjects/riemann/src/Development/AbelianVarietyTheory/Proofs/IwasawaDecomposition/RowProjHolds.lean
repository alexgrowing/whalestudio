import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorLevelMultiplicitySpaceMemGoodRows
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLiftFlagGroupInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsVecOfNe
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DTheta

theorem rowProj_holds : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → GlobalTheory.Mem.R3.DTheta.RowProj R.toRealDat F.lv2 := by
  intro hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hPins hHolds
  have hb := hPins.char.base
  intro b t w hw
  have h1 := GlobalTheory.KeepLevel.goodProjector_levelMultiplicitySpace_mem_goodRows hb.lev hb.models.inf hb.grp.record (R.toRealDat.levR F.lv2 b) t hw
  refine ⟨h1, fun c hc => ?_⟩
  have hcfix : postOn (R.MY 0) R.e0 c = c := sub_eq_zero.1 (LinearMap.mem_ker.1 hc.2)
  have hc0 : c ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
    have := GlobalTheory.Mem.Th.multAt_le R.toRealDat (R.toRealDat.levR F.lv2 b) t 0 ((GlobalTheory.Mem.Th.multAt_zero R.toRealDat _ t).symm ▸ hc.1)
    rwa [GlobalTheory.Mem.Th.multAt_zero] at this
  have hw0 : w ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) := by
    have := GlobalTheory.Mem.Th.multAt_le R.toRealDat (R.toRealDat.levR F.lv2 b) t 0 hw
    rwa [GlobalTheory.Mem.Th.multAt_zero] at this
  obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec (R.MY 0) (GlobalTheory.GardingVec.sm_ne_bot D _ _ (R.MY 0))
  have ha : 0 < (RealDat.nP F.lv2 b)⁻¹ := inv_pos.2 (GlobalTheory.KapRedII.nP_pos' F.lv2 b)
  rw [GlobalTheory.KapRedII.ipM_smul_of_vec _ _ _ _ _ ha v hv, GlobalTheory.KapRedII.ipM_smul_of_vec _ _ _ _ _ ha v hv]
  congr 1
  conv_lhs => rw [← hcfix]
  exact GlobalTheory.ProjectorAdjoint.ipM_gaL (L := R.dat0 R.triv) hP hb.models.inf hb.models.ν0.1.1 hb.models.ν0.2 R.eG _
    (GlobalTheory.ProjectorAdjoint.eC_inv R.toRealDat hb.grp.record) hc0 hw0

end GlobalTheory.Mem.R3.DTheta
