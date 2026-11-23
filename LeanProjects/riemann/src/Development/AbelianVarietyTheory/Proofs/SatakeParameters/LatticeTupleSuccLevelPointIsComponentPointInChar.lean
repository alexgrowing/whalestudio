import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

theorem reGL_finCongr_twice {R : Type} [CommRing R] {a b : ℕ} (h1 : a = b) (h2 : b = a) (x : GL (Fin a) R) :
    Formalism.L2.PairingIndexBounds.F.reGL (finCongr h2) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h1) x) = x := by
  subst h1
  apply Units.ext
  ext r s
  rfl

set_option maxHeartbeats 1000000 in

theorem ptS_isPt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ g : ∀ v, GL (Fin ((gatJ Lv (j + 1)).P.m + 1)) ((gatJ Lv (j + 1)).P.Qq v), (∀ v, La.2 v = colSpan ((gatJ Lv (j + 1)).P.W v) (g v).1) ∧ ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 g (J.pt std (j + 1) hj La).1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD j hj La hLa
  obtain ⟨⟨hr, hx⟩, -⟩ := hD (j + 1) hj La hLa
  have hG := (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).good
  refine ⟨Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2, fun v => ?_, ?_⟩
  · obtain ⟨g, hg'⟩ := (Formalism.L2.G.Cmp.isLattice_iff _ (La.2 v)).1 (hLa v)
    exact Classical.epsilon_spec (p := fun g0 : GL (Fin ((gatJ Lv (j + 1)).P.m + 1)) ((gatJ Lv (j + 1)).P.Qq v) =>
      La.2 v = colSpan ((gatJ Lv (j + 1)).P.W v) (g0 : Matrix _ _ _)) ⟨g, by rw [hg', Formalism.L2.G.Cmp.colSpan_eq]⟩
  · have hy : (J.cp std).y (j + 1) La = Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk.symm)
        (Classical.epsilon fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
          (Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2) x ∧
          x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
      show (dite (j + 1 ≤ D.R.m) _ _ : PtCh _ _).y = _
      rw [dif_pos hj]
    rw [hx, hy, reGL_finCongr_twice]
    exact (Classical.epsilon_spec (p := fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
          (Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2) x ∧
          x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ⟨_, hG.isPt_sec _ _, Subgroup.mul_mem _ (hG.yG_mem _) (hG.sec _).2⟩).1

end GlobalTheory.TwV.DelA
