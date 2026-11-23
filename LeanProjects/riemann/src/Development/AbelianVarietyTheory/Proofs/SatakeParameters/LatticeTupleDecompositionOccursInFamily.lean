import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicLatticeTupleDecompositionStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem dec_update : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ (γ : GL (Fin (D.R.N (j + 1))) D.host.E), γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj) → ∀ κ : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U, (J.pt std (j + 1) hj La).1 = GlobalTheory.TwU.ratA D.host.F γ * ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 * κ.1 → ∃ d : Dec J std, d.gam (j + 1) hj La = γ ∧ d.kap (j + 1) hj La = κ) := by
  unfold GlobalTheory.TwV.AllSites
  intro D _ hT _ _ _ _ _ ex u μ w hg Lv I H X _ std t J S hD j hj La hLa γ hγ κ hκ
  obtain ⟨d0⟩ := GlobalTheory.T.exists_adelic_latticeTuple_decomposition S hD
  have key : ∀ k (hk : k ≤ D.R.m) (Lb : (sysS H X std).Lt k), ∃ (g : GL (Fin (D.R.N k)) D.host.E)
      (c : ((J.St k hk).K (J.chart std k hk Lb)).lev.U),
      g ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk) ∧
      (((sysS H X std).Pj k).IsLatTup Lb.2 →
        (J.pt std k hk Lb).1 = GlobalTheory.TwU.ratA D.host.F g * ((J.St k hk).y (clsAt X H k Lb.1 Lb.2)).1 * c.1) ∧
      (∀ _ : k = j + 1, HEq Lb La → HEq g γ ∧ HEq c κ) := by
    intro k hk Lb
    by_cases h : k = j + 1 ∧ HEq Lb La
    · obtain ⟨rfl, h2⟩ := h
      obtain rfl := eq_of_heq h2
      exact ⟨γ, κ, hγ, fun _ => hκ, fun _ _ => ⟨HEq.rfl, HEq.rfl⟩⟩
    · exact ⟨d0.gam k hk Lb, d0.kap k hk Lb, d0.mem k hk Lb, d0.eq k hk Lb, fun e hL => absurd ⟨e, hL⟩ h⟩
  choose g c hm he hh using key
  exact ⟨⟨g, c, hm, he⟩, eq_of_heq (hh (j + 1) hj La rfl HEq.rfl).1, eq_of_heq (hh (j + 1) hj La rfl HEq.rfl).2⟩

end GlobalTheory.TwV.DelA
