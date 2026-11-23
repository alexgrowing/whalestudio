import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingYAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockRowSubstitutionPreservesComplexSpan
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChartTies3Site
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HP

set_option maxHeartbeats 4000000 in

theorem cmpJHyp_inTw_site : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) (T : ∀ u : D.what₂.Word, Forms0 D u) (c : LatCmp D), CmpTied D X0 T Gt c → FillTie Gt u w hg Fl → SiteGood Z → SiteRest Z c → CmpJHyp c (Z.inTw Fl ht Gt) := by
  intro D X0 u w hg Tw μ Z Fl ht Gt T c K hF G A
  refine HypTiesI.hyp (X0 := X0) ⟨ht, hF, fun j hj => ⟨Z.Fo j hj, Z.loc Fl ht j hj, rfl, ?_⟩⟩ K
  exact
    { frRat := Z.frRat Fl ht j hj
      sameU := Z.sameU Fl ht j hj
      hypT := hypTJ_site Z Fl ht G.siteGood_prime_torsion G.bad_p j hj
      bad_p := G.bad_p j hj
      std := A.std j hj
      psi := A.psi j hj
      chRat := A.chRat j hj
      hypC := hypTJC_site Z Fl ht G.siteGood_prime_torsion j hj
      ok := G.ok j hj
      siteGood_prime_torsion := G.siteGood_prime_torsion j hj
      Lb_eq := fun _ => (reL_symm (rankN D (j + 1) hj) _).symm }

end GlobalTheory.HP
