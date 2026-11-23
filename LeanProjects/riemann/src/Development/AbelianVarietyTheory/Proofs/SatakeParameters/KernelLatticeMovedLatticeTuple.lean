import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatKRatMulLev
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartEqOfSameComponentStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000

theorem smulLat_of_heq {E : Type} [Field E] [NumberField E] [StarRing E] {a N : ℕ} (hr : a = N) (σ : E →+* E) (Jm : Matrix (Fin N) (Fin N) E)
    (g : GL (Fin N) E) (A A' : Submodule (𝓞 E) (Fin a → E)) (B B' : Submodule (𝓞 E) (Fin N → E)) (hA : HEq A B) (hA' : HEq A' B')
    (hB : B' = SDLat.smulLat (eMat rfl σ Jm g) B) : A' = SDLat.smulLat (eMat hr σ Jm g) A := by
  subst hr
  cases eq_of_heq hA
  cases eq_of_heq hA'
  exact hB

theorem kerN_smul : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → (J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La)) = SDLat.smulLat (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g) ((J.fd std).kerN j (c, La))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj c La γ g κ hr hLat hMove
  have hLat' : ((sysS H X std).Pj j).IsLatTup (((sysS H X std).Lv.lev j c).smul γ La) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ La).2 hLat
  have hch : J.chart std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La) = J.chart std j hj.le (c, La) :=
    GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hS j hj.le c _ _ hLat' hLat
  have h1 := (hD j hj.le (c, La) hLat).2.2.1
  have h2 := (hD j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La) hLat').2.2.1
  obtain ⟨hg, hpt, -, -⟩ := hMove
  rw [hch, hpt] at h2
  exact smulLat_of_heq hr _ _ g _ _ _ _ h1 h2 (latK_rat_mul_lev D _ _ _ _ _ _ _ _ κ g hg)

end GlobalTheory.TwV.Xc
end
