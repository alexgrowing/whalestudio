import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem fills_Pj_m_add_one {p : ℕ} {G : GAtP p} (Fl : Fills G) (j : ℕ) :
    (Fl.Pj j).m + 1 = Formalism.MainNotions.FormalGroupSystem.NN G.P.m Fl.t j := by
  cases j with
  | zero => simp [Fills.Pj, Formalism.MainNotions.FormalGroupSystem.NN]
  | succ j => simp only [Fills.Pj, Places.withWt, Formalism.MainNotions.FormalGroupSystem.NN]; ring

theorem sysS_ranks : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => (sysS H X std).mm = D.R.m ∧ (sysS H X std).t = D.R.t ∧ (∀ j, ((sysS H X std).Pj j).m + 1 = D.R.N j) ∧ ∀ j, RankTie (sysS H X std) D j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  have hk : (D.gat u w hg).P.m + 1 = D.R.N 0 := (lev0At J.Gd u w hg).A.rk
  have ht : (Gl.Fl u w hg).t = D.R.t := X.fl_t
  have hN : ∀ j, D.R.N j = Formalism.MainNotions.FormalGroupSystem.NN (D.gat u w hg).P.m (Gl.Fl u w hg).t j := by
    intro j
    simp only [Formalism.MainNotions.FormalGroupSystem.NN, ht]
    simp only [Formalism.BasicNotions.Ranks.N] at hk ⊢
    omega
  refine ⟨X.fl_m, X.fl_t, fun j => ?_, fun j => ⟨hN j, hN (j + 1)⟩⟩
  exact (fills_Pj_m_add_one (Gl.Fl u w hg) j).trans (hN j).symm

end GlobalTheory.TwV.DelB
