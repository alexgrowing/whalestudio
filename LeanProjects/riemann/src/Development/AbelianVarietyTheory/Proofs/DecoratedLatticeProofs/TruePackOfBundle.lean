import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharactersMatchBundleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColsStdOfBWit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopReadingBundleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemOfCoprime
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem truePack_of_bWit : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → Nonempty (Bl.RXs q.x.what₂) → PtRows b → TruePack (packB b) := by
  intro hL p K q c b hW hX hR
  obtain ⟨hOk, hPins, hTw, hStdC, hTS⟩ := GlobalTheory.Fam.colsStd_of_bWit q b hW
  obtain ⟨hChr, hXi, hQ, hLev, hRec, hRP, hOk3, hIdE, hLM⟩ := GlobalTheory.T.characters_match_bundle q b hW
  have hTop := GlobalTheory.T.exists_top_reading_bundle q b hW hX
  have hTW : TrueW (packB b) := ⟨hOk, hPins, hTw, hStdC, hChr, ⟨1, hTop⟩⟩
  have hTQ : TrueQ (packB b) := ⟨hXi, hQ, hTop⟩
  obtain ⟨hRec'⟩ := hRec
  have hPk : PkHyp (packB b) := pkHyp_of_real (packB b) hR.join hLM hR.dc hR.frames hRP hR.see hRec' hR.ex hR.prim.1 hR.prim.2
    hOk3 hIdE hR.gapS hR.fin hR.gap hTW hTQ
  exact TruePack.mk _ ⟨hPk, hTW, hTQ, hTS, hLev, ⟨hRec'⟩⟩

end GlobalTheory.Fam
