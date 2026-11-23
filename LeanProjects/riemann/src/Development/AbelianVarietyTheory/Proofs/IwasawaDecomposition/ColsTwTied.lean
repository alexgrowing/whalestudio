import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DsigEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChoiceExistsStandardChainDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EMtTied
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

theorem WPt.colsTwTied : ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), q.O.ex.tw = q.w.tw q.Z ∧ ∃ tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes q.x.n.tp q.x.col.C (q.w.tw q.Z), TC.StdTw q.w.I q.w.l q.Z q.w.l0 tw ∧ Formalism.L2.Rows.EMtTied (q.w.D q.Z) q.x.col.C tw := by
  intro 𝒮 K q
  refine ⟨?_, ?_⟩
  · exact congrArg (fun s : Σ (Gt : GatTies (q.w.D q.Z)) (cmp : LatCmp (q.w.D q.Z)) (tw : TwForms (q.w.D q.Z)),
      KerFam (q.w.D q.Z) Gt cmp tw (ofObj q.O).Gy => s.2.2.1) q.x.ker_eq
  · obtain ⟨tw, htw⟩ := GlobalTheory.T.trueColumnChoice_exists_standardChainData q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ q.x.n.tp q.x.col.C q.x.n.xi q.x.col.std q.x.col.stdLv
    exact ⟨tw, htw, GlobalTheory.Mem.Col2.EMt.eMtTied q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ q.x.n.tp q.x.col.C tw q.x.what₂.emt0 q.x.what₂.emt⟩

end GlobalTheory.Mem.Top.Bl

end
