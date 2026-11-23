import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AdmissibleOfTransported

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Top4 Formalism.L2.SG.JoinSI Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.JoinSISel

section At

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

def MIAt2 {R : Formalism.L2.RecT ex} {P : Formalism.L2.Rows.RowSideFamily ex}
    {Dcf : ∀ Zs : Formalism.L2.Indef.DefSub P.A3.fam3.amb3, Formalism.L2.Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs, Formalism.L2.Indef.SPer (Dcf Zs)} {Zscf : Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3}
    {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : Formalism.IndefR.RealT R P Dcf Spf Zscf S Ks) : Prop :=
  (cx Q).MIstar2 (Q.F.eV (cx Q).zs) Q.sEE

end At

variable {𝒜 : FamClass} {sel : Formalism.L2.TSel 𝒜} {selS : SelS 𝒜 sel} {selP : BaseLevelCompatibleSelection 𝒜 sel} {selDH : Formalism.L2.Top3.SelDH 𝒜 sel}
  {selC : ColumnCompatibleSelection 𝒜 sel selP} {selK : SelK 𝒜 sel} {selI : IndefiniteRealisationChoice 𝒜 sel selS selP selDH selC selK}

theorem closed_complementFiveFamily_of_evSel_imageFull (selJ : SelJ 𝒜 sel selS selP selDH selC selK selI)
    (hM : Closed 𝒜 fun Fm _ => ∀ hc : 𝒜 Fm, EvSel sel Fm hc fun x hx h i => MIAt2 (selI Fm hc x hx h i))
    (hFX : Closed 𝒜 fun Fm _ => ∀ hc : 𝒜 Fm, EvSel sel Fm hc fun x hx h i => FinX (selS Fm hc x hx h i).Y)
    (hon : Closed 𝒜 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, BaseVectorImageFull (Fm.D x i)) :
    Closed 𝒜 fun Fm _ => Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm := by
  obtain ⟨ε1, hε1, H⟩ := (hM.and hFX).and hon
  refine ⟨ε1, hε1, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := H eps he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨hM', hF'⟩, ⟨y0, hY⟩⟩ := hK Fm CH hc hL
  obtain ⟨a0, hA⟩ := hM' hc
  obtain ⟨b0, hB⟩ := hF' hc
  refine ⟨max (max a0 b0) (max y0 (max (sel Fm hc).1 (Fm.x1 + 1))), fun x hxge i => ?_⟩
  have h1 : max a0 b0 ≤ x := le_trans (le_max_left _ _) hxge
  have h2 : max y0 (max (sel Fm hc).1 (Fm.x1 + 1)) ≤ x := le_trans (le_max_right _ _) hxge
  have hx : Fm.x1 < x := by
    have := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)
    linarith
  have h : (sel Fm hc).1 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h2)
  exact adm13_of_joinSI (hA x hx h (le_trans (le_max_left _ _) h1) i) (selJ Fm hc x hx h i)
    (hB x hx h (le_trans (le_max_right _ _) h1) i) (hY x (le_trans (le_max_left _ _) h2) i)

end Formalism.L2.SG.JoinSISel
