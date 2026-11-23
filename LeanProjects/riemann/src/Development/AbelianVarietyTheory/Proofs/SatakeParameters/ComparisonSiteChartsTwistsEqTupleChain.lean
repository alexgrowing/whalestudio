import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingYAlt
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Port

theorem gl_one_eq_of_det_eq {R : Type*} [CommRing R] (g h : GL (Fin 1) R)
    (e : Matrix.GeneralLinearGroup.det g = Matrix.GeneralLinearGroup.det h) : g = h := by
  have e' : (g : Matrix (Fin 1) (Fin 1) R).det = (h : Matrix (Fin 1) (Fin 1) R).det := by
    have := congrArg Units.val e
    simpa using this
  ext i k
  rw [Subsingleton.elim i 0, Subsingleton.elim k 0]
  simpa [Matrix.det_unique] using e'

theorem siteD_inTw_charts_tw : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) (Hh : Formalism.L2.Herm.SymmetricHermitianColumns D) (St : GlobalTheory.TwU.ChainCharts D u μ) (hv : ValAll Tw St), Z.Fo = foOf Hh St hv → (∀ j hj, St (j + 1) hj = GlobalTheory.TwU.StepCharts.ofStepIn ((Z.inTw Fl ht Gt).at' j hj).st) ∧ ∀ j hj β (x : UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Formalism.L2.Herm.IsDetOf D.sp.cm y x.1 → (((Z.inTw Fl ht Gt).at' j hj).st.tw β).ch x = D.chiD (Hh.dt y) ^ cTw D (j + 1) := by
  intro D X0 u w hg Tw μ Z Fl ht Gt Hh St hv hZ
  obtain ⟨Fo, fin, S⟩ := Z
  dsimp only at hZ
  subst hZ
  refine ⟨fun j hj => rfl, ?_⟩
  intro j hj β x y hy
  have hyx : y = detU D (j + 1) hj x := by
    apply Subtype.ext
    apply gl_one_eq_of_det_eq
    rw [det_detU]
    exact hy
  subst hyx
  rfl

end GlobalTheory.Port
