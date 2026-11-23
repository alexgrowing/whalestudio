import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopMultAndExtVInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.HdExist

theorem hd_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → D.host.F = maximalRealSubfield D.host.E → Seed.FrmC.StdLat (Yc D 0) → (∀ i, Seed.FrmC.StdLat (Wc D i)) → ∀ (tup : T → D.what₂.Tup) (tupT : D.what₂.Tup → T), (∀ t, tupT (tup t) = t) → tup A3.A.μ0 = D.what₂.mu0 → ∃ y : Hd R.toRealDat, y.tup = tup ∧ y.tupT = tupT := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hF hY hW tup tupT htt ht0
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  obtain ⟨hTop, hinj⟩ := GlobalTheory.DefiniteMult.topMult_and_extV_injective D G Pl0 T A3.A Ks R.toRealDat F.lv2 hB
  obtain ⟨PY, PW, ιW, hPY, hPW, hiso, hmatch⟩ := GlobalTheory.StdFrameExist.frames_std_matched D hF hY hW
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  exact ⟨⟨tup, tupT, htt, ht0, hm, hTop, hinj, PY, PW, ιW, hiso, hmatch, hF, hPY, hPW⟩, rfl, rfl⟩

end GlobalTheory.Mem.R3.Rw.HdExist
