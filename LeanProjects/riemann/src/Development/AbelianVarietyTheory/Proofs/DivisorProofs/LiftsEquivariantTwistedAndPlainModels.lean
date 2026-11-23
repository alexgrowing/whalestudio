import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.GEqBr

set_option maxHeartbeats 2000000 in

theorem geq_br : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.phase → R.PGEquiv F → (∀ t g (v : (A3.A.MtildeCSD t).Forms), R.Th t (R.jX t (A3.A.leftGroupActionRight t g v)) = R.gE g (R.Th t (R.jX t v))) ∧ ∀ i t g (v : (A3.A.MtCSD i t).Forms), R.thG i t (R.jV i t (A3.A.leftGroupActionLift i t g v)) = R.gW i (sg0 D A3.A) g (R.thG i t (R.jV i t v)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hph hG
  refine ⟨fun t g v => hG.1 t g v, fun i t g v => ?_⟩
  have h : cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (R.jV i t (A3.A.leftGroupActionLift i t g v)) =
      R.gW i (sg0 D A3.A) g (cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) • R.thG i t (R.jV i t v)) := hG.2 i t g v
  rw [map_smul] at h
  have hne : cj (twAt D.what₂.embLL A3.A.v0) (R.phs i) ≠ 0 := by
    intro h0
    have := congrArg norm h0
    rw [norm_cj, (hph i).1, norm_zero] at this
    exact one_ne_zero this
  exact smul_right_injective _ hne h

end GlobalTheory.GEqBr
