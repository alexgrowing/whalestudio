import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryPt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReindexRenamePointDetLatK
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.TwV.Joint.isPt_pt_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), J.IsPt std 0 (Nat.zero_le _) La (J.pt std 0 (Nat.zero_le _) La) ∧ (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) (J.pt std 0 (Nat.zero_le _) La).1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J La
  have hr := (lev0At J.Gd u w hg).A.rk
  obtain ⟨x0, hx0⟩ := GlobalTheory.TwU.exists_unitary_pt J.one.good La.1
    (basesAt (chainAt H hT) std (sysS H X std).vp (sysS H X std).unif (sysS H X std).eO (sysS H X std).eO_spec (sysS H X std).dG
      (sysS H X std).dG_spec (sysS H X std).om 0 La.2)
  have hs := Classical.epsilon_spec (p := fun x => (lev0At J.Gd u w hg).A.IsPt La.1
      (basesAt (chainAt H hT) std (sysS H X std).vp (sysS H X std).unif (sysS H X std).eO (sysS H X std).eO_spec (sysS H X std).dG
        (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧ x ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ⟨x0, hx0⟩
  have hex : ∃ x, J.IsPt std 0 (Nat.zero_le _) La x := by
    refine ⟨⟨_, hs.2⟩, hr, ?_⟩
    ext i j
    rfl
  have hp := Classical.epsilon_spec hex
  obtain ⟨hr', he⟩ := hp
  refine ⟨⟨hr', he⟩, ?_⟩
  have h1 : (J.pt std 0 (Nat.zero_le _) La).1 = Classical.epsilon (fun x => (lev0At J.Gd u w hg).A.IsPt La.1
      (basesAt (chainAt H hT) std (sysS H X std).vp (sysS H X std).unif (sysS H X std).eO (sysS H X std).eO_spec (sysS H X std).dG
        (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧ x ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [show (J.pt std 0 (Nat.zero_le _) La).1 = _ from he]
    ext i j
    rfl
  rw [h1]
  exact hs.1
