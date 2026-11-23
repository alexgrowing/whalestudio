import Mathlib
import Formalism.LocalToGlobal.TieTwRecOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel
import Formalism.LocalToGlobal.NormalizedHeckeFactors.EtaClosed

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

theorem GlobalTheory.Top.link_eta : ∀ (𝒜 : FamClass)
    (sel : Formalism.L2.TSel 𝒜)
    (hduty : ∀ {eps : ℝ} (Fm : FamP eps), 𝒜 Fm → Duty Fm), Closed (D3 3 𝒜) fun Fm _ => LinkEta Fm := by
  intro 𝒜 sel _
  refine Closed.of_class fun Fm _ hc => ?_
  obtain ⟨x0, hx0⟩ := tied_families_of_choice (sel Fm (d3_a hc))
  refine Formalism.L2.linkEta_closed Fm ⟨max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have h1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
  obtain ⟨T⟩ := hx0 x h1 ((le_max_left _ _).trans hx) i
  exact ⟨T.n.gal.mt, T.n.cover, T.n.gal.hecke⟩
