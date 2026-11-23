import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseLevelRowSideTransport
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReplacementValuesBaseLevelTypePartsEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CopyLIntegral
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdxDefsUp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Mv

section
variable {B : Base} {C : Cols B} {a : Late B C} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m}
  {R : RealDat3 a.D A Ks} {F : Face3 a.D A} {X0 : BaseLevelRowSide a.D} {Y : Read (A3 := A) R.toRealDat F.lv2 X0} (Z : ReadL R F X0 Y)
  (u : Parts R)

theorem jWu_heq : HEq (jWu Z u) Z.jW := (by with_unfolding_all exact ((HEq.refl Z.jW) :))

theorem eRRu_heq : HEq (eRRu Z u) Z.eRR := (by with_unfolding_all exact ((HEq.refl Z.eRR) :))

theorem eRR0u_heq : HEq (riemannRochSpaceCoordinateEquiv Z u) Z.eRR0 := (by with_unfolding_all exact ((HEq.refl Z.eRR0) :))

variable (c : Refill a)

theorem readL_jW : HEq (letI := alg c.to iK; (readL c Z).jW) Z.jW := (by with_unfolding_all exact ((jWu_heq Z (partsB c R)) :))

theorem readL_eRR : HEq (letI := alg c.to iK; (readL c Z).eRR) Z.eRR := (by with_unfolding_all exact ((eRRu_heq Z (partsB c R)) :))

theorem transportedReading_baseRowLatticeCoordinates : HEq (letI := alg c.to iK; (readL c Z).eRR0) Z.eRR0 := (by with_unfolding_all exact ((eRR0u_heq Z (partsB c R)) :))

end

set_option maxHeartbeats 4000000 in

theorem rowsAre_refill : ∀ (B : Base) (C : Cols B) (a : Late B C) (c : Refill a) (px : PreX B.toPre) (I : ColIn B px) (hX : B.fields.Ok) (T : TwDat B) (Wt : Set B.places.Pl) (ix : C.Tup ≃ I.ι) (p0 : BaseLevelRowSide a.D) (r : RowsAre a.st I hX T Wt ix p0), ∃ r' : RowsAre c.to.st I hX T Wt ix (Tr.baseLevelRowSideTransport c p0), r'.z = Mv.cpDat c.to c.same r.z ∧ HEq r'.Y.tup r.Y.tup ∧ HEq r'.Y.tupT r.Y.tupT ∧ HEq r'.Y.PY.ψ r.Y.PY.ψ ∧ HEq (fun i => (r'.Y.PW i).ψ) (fun i => (r.Y.PW i).ψ) ∧ HEq (fun π => principalLevelFrame.rowRepR r'.z.R.θ (r'.Y.eFT π)) (fun π => principalLevelFrame.rowRepR r.z.R.θ (r.Y.eFT π)) ∧ HEq (fun x => (r'.Y.Ish.jE x).1) (fun x => (r.Y.Ish.jE x).1) ∧ HEq (fun x => (r'.Y.Iz.jE x).1) (fun x => (r.Y.Iz.jE x).1) ∧ HEq r'.Y.eE r.Y.eE ∧ HEq r'.Y.jA r.Y.jA ∧ HEq r'.Y.jA0 r.Y.jA0 ∧ HEq r'.Y.eMt r.Y.eMt ∧ HEq r'.Y.mj.eW r.Y.mj.eW ∧ HEq r'.Z.jW r.Z.jW ∧ HEq r'.Z.eRR r.Z.eRR ∧ HEq r'.Z.eRR0 r.Z.eRR0 := by
  intro B C a c px I hX T Wt ix p0 r
  letI := r.z.alg
  refine ⟨⟨Mv.cpDat c.to c.same r.z, (by with_unfolding_all exact ((holds_tr c.to r.intersectionNumber_baseChange) :)), (by with_unfolding_all exact ((read c r.Y) :)), (by with_unfolding_all exact ((readL c r.Z) :)),
    (by with_unfolding_all exact (r.tup_ix :))⟩, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kexactB (HEq.refl r.Y.tup)
  · exact (by with_unfolding_all exact ((HEq.refl r.Y.tupT) :))
  · exact (by with_unfolding_all exact ((HEq.refl r.Y.PY.ψ) :))
  · exact (by with_unfolding_all exact ((HEq.refl (fun i => (r.Y.PW i).ψ)) :))
  · exact (by with_unfolding_all exact ((heq_of_eq (funext fun π => (rep_eq c r.Y π).symm)) :))
  · kexactB (HEq.refl (fun x => (r.Y.Ish.jE x).1))
  · kexactB (HEq.refl (fun x => (r.Y.Iz.jE x).1))
  · exact (by with_unfolding_all exact ((HEq.refl r.Y.eE) :))
  · exact (by with_unfolding_all exact ((HEq.refl r.Y.jA) :))
  · exact (by with_unfolding_all exact ((HEq.refl r.Y.jA0) :))
  · exact (by with_unfolding_all exact ((HEq.refl r.Y.eMt) :))
  · exact (by with_unfolding_all exact ((HEq.refl r.Y.mj.eW) :))
  · exact (by with_unfolding_all exact ((readL_jW r.Z c) :))
  · exact (by with_unfolding_all exact ((readL_eRR r.Z c) :))
  · exact (by with_unfolding_all exact ((transportedReading_baseRowLatticeCoordinates r.Z c) :))

end GlobalTheory.Mem.R3.Rw.Mv

end
