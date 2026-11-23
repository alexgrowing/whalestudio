import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseLevelRowSideTransport
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

namespace GlobalTheory.Mem.R3.Rw.Up

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T₀ D.R.m}

theorem exists_mjHTie_of_eq (F : Face3 D A3) (Xd : DivX D) {X X' : Cx.CxData A3.fam3.amb3} (e : X' = X)
    (jW : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X'.data F.cr false)).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (jW0 : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X.data F.cr false)).dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (hj : HEq jW jW0)
    (eW : ∀ i : Fin D.R.m, (Fin ((A3.indefDown (X'.data F.cr false)).dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V)
    (h1 : ∀ (i : Fin D.R.m) x, Xd.jM ((i : ℕ) + 1) (eW i x) = jW i x)
    (h2 : ∀ i : Fin D.R.m, HLatTie (Xd.MjH ((i : ℕ) + 1)) ((A3.indefDown (X'.data F.cr false)).M i)
      ((A3.indefDown (X'.data F.cr false)).XW i) (eW i)) :
    ∃ J, MjHTie D A3.A Xd (A3.indefDown (X.data F.cr false)) jW0 J := by
  subst e
  cases hj
  exact ⟨⟨eW⟩, ⟨h1, h2⟩⟩

end GlobalTheory.Mem.R3.Rw.Up

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.R3.Rw.Up.mjAre_back : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (r : RowsAre (w.st Z) w.I hX T Wt (Equiv.refl _) p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (r' : RowsAre (w.st (SRe.upL Z S' N h)) w.I hX T Wt (Equiv.refl _) (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), r'.z = Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z → HEq r'.Z.jW r.Z.jW → ∀ Y : DivX (w.D (SRe.upL Z S' N h)), MjAre r'.Z Y → MjAre r.Z (Up.divBack Y) := by
  intro K B f T w Z hX Wt p0 r S' N h r' hz hj Y hY
  obtain ⟨z', hold', Y', Z', tix⟩ := r'
  dsimp only at hz hj
  subst hz
  obtain ⟨J', t'⟩ := hY
  letI : Algebra (Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z).core.Q.c.F (w.st (SRe.upL Z S' N h)).toD7.what₂.LL :=
    (Mv.cpDat (Up.refUp Z S' N h).to (Up.refUp Z S' N h).same r.z).alg
  have e := toCx3_eq (Up.refUp Z S' N h).to (iK := r.z.alg) r.z.R r.z.F
  exact (by with_unfolding_all exact ((exists_mjHTie_of_eq r.z.F (divBack Y) e.symm ((Z'.jW)) ((r.Z.jW)) ((hj)) ((J'.eW)) ((t'.j_eq)) ((t'.hlat))) : _))

end
