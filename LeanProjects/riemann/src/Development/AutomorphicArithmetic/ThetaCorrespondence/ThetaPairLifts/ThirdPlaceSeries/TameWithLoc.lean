import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesLocalOfHypothesis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CenFrame
section Mat
variable {k : Type} [CommRing k] {n n' r t : ℕ}
end Mat
section Loc
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
end Loc
section Lev
variable {D : D7}
end Lev
section Core
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
end Core
section Main
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
end Main
end GlobalTheory.CenFrame
namespace GlobalTheory.SerThird
open Formalism.MainNotions.N Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting.Up GlobalTheory.CenFrame
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 4000000 in
theorem cenLoc_third_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (Lc : LocAll (lay0 (Dof x))) : CenLoc (withLoc Lc) (mtL Lc l.mt.M) := by
  intro i
  have h := cen_twisted x.r.Y x.m.z.cG x.m.z.pins.char.base x.m.z.pins.keep x.m.intersectionNumber_baseChange.ok.ok2 (cenRead_state x) l.mt.M l.mt.ad l.mt.mt
    ((withLoc Lc).nd.w i) ((withLoc Lc).nd.w_tw i) ((withLoc Lc).nd.mu i) ((withLoc Lc).nd.mu_w i) ((withLoc Lc).nd.j i)
    ((withLoc Lc).nd.j_range i).1 ((withLoc Lc).nd.j_range i).2
  exact (by with_unfolding_all exact (h :))
set_option maxHeartbeats 2000000 in
theorem tame_coupled_with_loc {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (Lc : LocAll (lay0 (Dof x))) :
    ∀ k v, ∃ κ : IsLocalRing.ResidueField ((withLoc Lc).nd.plOm.1 ((withLoc Lc).naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar ((withLoc Lc).host.g k),
      Formalism.L2.NT.TameCoupled ((withLoc Lc).nd.plOm.1 ((withLoc Lc).naut.plGw k v)) κ ((withLoc Lc).ntypes.tg k v)
        (GlobalTheory.Mem.TypePl.labDat ((withLoc Lc).host.g k)).gen :=
  fun k v => ⟨l.a.A.grp.kv k v, by
    have h := l.a.A.grp.tg_tame k v
    rw [l.a.zeta k] at h
    exact h⟩
end GlobalTheory.SerThird
end
end
