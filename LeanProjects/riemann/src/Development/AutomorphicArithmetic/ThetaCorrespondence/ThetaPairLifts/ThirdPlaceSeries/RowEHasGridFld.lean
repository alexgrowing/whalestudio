import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridFieldHasLattices
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithAtProperty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistsAtLinked
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvPSizeRowsDlog
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.ChiGrid
namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow
section Transfer
variable {D : Formalism.BasicNotions.D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
end Transfer
variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
  {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
theorem hasGrid_of_full_field_lamTie (p : PtAt ex Csz) (CF : ℝ) (hp : p.CompatibilityConditions)
    (hs : TwistedPlaceChoiceLiesOverPair D ex.nch)
    (hc : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (ex.nch.twI w) (ex.nch.Q w))
    (hpw : ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (ex.nch.twI w) (ex.nch.Q w) (ex.nch.k' w) (ex.nch.psi' w ^ a) (twEps D (ex.nch.twI w)))
    (G : Grid p CF) (h2 : FieldHas G (Formalism.L2.Host.embLL0 D)) (h4 : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G))
    (hF : Full p.R.toRealDat G) : HasGrid (@Fld) p CF := by
  have hfit := gridFit_of_parts hs hc hpw hp.real.valLL0 h2 hp.real.psiChoice h4
  obtain ⟨W, M, ρ, ξ, cv, rm, S, rp, n, e, c, hIs, hOK, hSq⟩ := hF
  exact ⟨G, W, hIs.weil, hfit, n, ⟨M, ρ, ξ, cv, rm, S, rp, e, c⟩, ⟨hIs, hp.eSer, hOK, hSq⟩⟩
end GlobalTheory.Mem.LiteralAutomorphy.GridRow
namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow
theorem rowE_hasGrid_fld_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (CF : ℝ) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithList hL CF K B f T w Z Wt p0 t nch n xd c)) → RowE (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ)) fun _ D O c b => ∀ t : b.Comparison₂, (b.part t).pt.CompatibilityConditions → GlobalTheory.BigTop.Fun.HasGrid @GlobalTheory.BigTop.Fun.Fld (b.part t).pt CF := by
  intro hL CF N S Γ hN
  refine ((_root_.GlobalTheory.Mem.LiteralAutomorphy.TwAtLink.twists_at_linked_alt hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N (GridA CF)) S Γ).s)).and
    ((_root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.rowE_pinned_grid_alt hL CF N S Γ hN).and (_root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.rowE_full_grid_alt hL CF N S Γ))).imp fun κ K β c b _ _ _ H t ht => ?_
  obtain ⟨hw1, hw2, hcond, hpow⟩ := H.1
  obtain ⟨G₀, hF₀, hT₀⟩ := H.2.1 t ht
  obtain ⟨G, hv, hw, hch, hFull⟩ := H.2.2 t ht G₀
  exact _root_.GlobalTheory.Mem.LiteralAutomorphy.GridRow.hasGrid_of_full_field_lamTie _ CF ht ⟨hw1, fun w w' a b c => (hw2 w w' a b c).2.2⟩ hcond hpow G (fieldHas_of_same hv hch hF₀)
    (lamOf_of_same hw hch ▸ hT₀) hFull
end GlobalTheory.Mem.LiteralAutomorphy.GridRow
end
