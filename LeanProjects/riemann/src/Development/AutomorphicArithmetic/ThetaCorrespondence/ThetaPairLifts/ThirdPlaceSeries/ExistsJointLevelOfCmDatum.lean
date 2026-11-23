import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JointEtaOfAdmissibleTwistStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
namespace GlobalTheory.JointLevel
open scoped TensorProduct
open Formalism.IndefR Formalism.BasicNotions.TH GlobalTheory.MtRead GlobalTheory.MtLev
open Formalism.L2.DIV (redFn rTup levFn kP blockTri blk2 blkOf dBlk upperLeftBlock ext1 G0 Pl)
section Loc
variable {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}
end Loc
variable {D : D7}
section Dat
variable {iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {f : Formalism.IndefR.NX.U D.nd → ℂ}
end Dat
section Shape
variable {iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {f : Formalism.IndefR.NX.U D.nd → ℂ}
  {V : HSp D} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V D.R.nV}
end Shape
section Rows
open Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.L2.DIV
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
end Rows
theorem joint_level_of_twOK_at_twisted : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → Joint (D := Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) (mtAt (D := Dof x) l.mt.M v j) l.b.Bs.exp b hA j := by
  intro _ hL
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j hv _ hT
  have hon : (Dof x).what₂.muTw v = (Dof x).what₂.muAt v := (P.q.mu.on v (GlobalTheory.HeightCounting.Up.Model.mem_of_twisted x v hv)).symm
  have hμ : Formalism.IndefR.RecTie.Used0 (Dof x) ((Dof x).what₂.muTw v) := Or.inr ⟨v, hon⟩
  refine joint_of (D := Dof x) l.mt.ad l.rat.rat l.b.Bs l.b.ser x.m.z.lev.is x.m.z.pins.keep l.Pq_over l.a.elem (fun t PP hPP => ?_)
    hμ j ?_ b hA hT
  · rw [x.m.z.lev.Q] at hPP
    rw [l.sel]
    obtain ⟨u, -, e⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hPP
    exact ⟨u, e⟩
  · have e1 := x.m.z.lev.xiH (x.r.Y.tupT ((Dof x).what₂.muTw v))
    have e2 := x.m.tup (x.r.Y.tupT ((Dof x).what₂.muTw v))
    rw [← x.r.tup, x.r.Y.tupTie _ hμ] at e2
    rw [e1, ← e2, x.m.z.lev.C]
    rfl
end GlobalTheory.JointLevel
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joint_level_of_cm_datum_twOK : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → Joint (D := Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) (mtAt (D := Dof x) l.mt.M v j) l.b.Bs.exp b hA j := by
  first | exact @_root_.GlobalTheory.JointLevel.joint_level_of_twOK_at_twisted | exact _root_.GlobalTheory.JointLevel.joint_level_of_twOK_at_twisted | (intros; apply _root_.GlobalTheory.JointLevel.joint_level_of_twOK_at_twisted <;> assumption)
end
end
