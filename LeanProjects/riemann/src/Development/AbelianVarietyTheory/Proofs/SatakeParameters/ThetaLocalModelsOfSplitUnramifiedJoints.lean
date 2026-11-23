import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointSiteChainComparedCarriesAdmittedSystemStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem modelsOK_of_joints : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), (∀ μ, DV.Used D μ → JointsAt t μ) → (∀ u, ex.tw.e0 u D.what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _)) → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.ModelsOK D Gl ex.cmp Dx ex.tw := by
  intro hA hC D L hT Gi Gl Kc Dx cX ex t hJ h0 hS hk
  classical
  refine ⟨h0, fun μ u w hg => if h : DV.Used D μ ∧ D.what₂.places.resChar w ∉ Dx.Qp μ then
      ⟨Classical.choose (hJ μ h.1 u w hg h.2),
        chainAt (Classical.choose (Classical.choose_spec (Classical.choose_spec (hJ μ h.1 u w hg h.2)))) hT⟩
    else ⟨Gl.Lv u w hg, Gl.Ch u w hg⟩, ?_⟩
  intro μ hU u w hg hq
  have hP : DV.Used D μ ∧ D.what₂.places.resChar w ∉ Dx.Qp μ := ⟨hU, hq⟩
  dsimp only
  have key : ∀ x : (Σ Lv : Levels (Gl.Fl u w hg), Chain Lv),
      x = ⟨_, chainAt (Classical.choose (Classical.choose_spec (Classical.choose_spec (hJ μ hP.1 u w hg hP.2)))) hT⟩ →
      GlobalTheory.TwU.CmpLite D ex.cmp ex.tw u μ w hg x.2 ∧ GlobalTheory.TwU.SiteAdm D u w hg (Gl.Fl u w hg) x.1 x.2 := by
    rintro x rfl
    exact GlobalTheory.T.jointSite_chain_compared_carries_admittedSystem hA hC t
      (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hJ μ hP.1 u w hg hP.2))))).some
      hU hS hk
  exact key _ (dif_pos hP)

end GlobalTheory.TwV
