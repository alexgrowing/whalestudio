import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosBridge
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelA.posTie_at : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; PosTie (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) ∧ ∀ r : D.what₂.LL, ι (D.what₂.embLL r) = algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w] (ex.cmp.embW u w hg r)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hS ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  refine ⟨fun v s x => ?_, fun r => ?_⟩
  · have h := hS v s x
    have hz : (embT D (hT.gat_pos u w hg ⟨v, s⟩)) x ∈ TaylorLogMetric.Qbar := by
      rw [← tEL_emb]
      exact Formalism.L2.G.embLL_mem_alg D _
    have he : TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) x = embT D (hT.gat_pos u w hg ⟨v, s⟩) x := rfl
    have hL : TaylorLogMetric.lamC S.lam (TaylorLogMetric.embT D (hT.gat_pos u w hg ⟨v, s⟩) x) = ι ((embT D (hT.gat_pos u w hg ⟨v, s⟩)) x) := by
      unfold TaylorLogMetric.lamC
      rw [dif_pos (he ▸ hz)]
      rw [hι ⟨_, hz⟩]
      rfl
    rw [← hL, h, Formalism.L2.Herm.star_conj]
    rfl
  · have hz := Formalism.L2.G.embLL_mem_alg D r
    rw [hι ⟨_, hz⟩, ← S.hK r hz]
    rfl
