import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryPt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReindexRenamePointDetLatK
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

set_option maxHeartbeats 2000000 in

theorem Joint.pt_succ_isPt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), J.IsPt std (j + 1) hj La (J.pt std (j + 1) hj La) ∧ ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2) (J.pt std (j + 1) hj La).1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La
  have hG := (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).good
  obtain ⟨x0, hx0⟩ := exists_unitary_pt hG ((I.at' j hj).st.eC.symm La.1).2
    (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2)
  have hspec := Classical.epsilon_spec (p := fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
    (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2) x ∧
    x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ⟨x0, hx0⟩
  have hy : (J.cp std).y (j + 1) La = Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk.symm)
      (Classical.epsilon fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
        (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2) x ∧
        x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    show (chAt _ _ _ _ _ _ _ _ _ I _ _ _ _ (j + 1) La).y = _
    simp only [chAt, dif_pos hj]
  have hre : ∀ {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (y : GL (Fin m) R), Formalism.L2.PairingIndexBounds.F.reGL (finCongr h.symm) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) = y := by
    intro R _ m n h y
    subst h
    ext a b
    simp [Formalism.L2.PairingIndexBounds.F.reGL]
  have key : ∃ x, J.IsPt std (j + 1) hj La x :=
    ⟨⟨_, hspec.2⟩, ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk, by
      rw [hy]
      exact (hre ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk.symm _).symm⟩
  have hpt : J.IsPt std (j + 1) hj La (J.pt std (j + 1) hj La) := Classical.epsilon_spec key
  refine ⟨hpt, ?_⟩
  obtain ⟨hr, hx⟩ := hpt
  rw [hx, hy, hre]
  exact hspec.1

end GlobalTheory.TwV
