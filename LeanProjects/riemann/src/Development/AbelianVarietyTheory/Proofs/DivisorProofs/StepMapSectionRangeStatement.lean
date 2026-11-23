import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepMapSectionRange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecSecCol
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory.FlagZ.TautUniq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.step_map_section_range : ∀ (ι : Type) [Fintype ι] (N : ℕ)
    (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) N), Taut.IsTaut ι N fl →
    ∀ (A : Type) [CommRing A] (h : ι → GL (Fin N) A) (y : Sp A ⟶ Sp ℤ)
      (hy : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd h ≫ flStr ι N = y) (a : ι) (l : Fin (N + 1))
      (v : Fin N → A),
    vecSec y v ∈ Set.range ((stepMap ι N fl (flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd h) y hy a l).app ⊤) ↔
      v ∈ Submodule.span A (Set.range fun j : Fin l => fun i => (h a).1 i (Fin.castLE l.is_le j)) := by
  first | exact @GlobalTheory.FlagZ.TautUniq.vecSec_mem_range_stepMap_iff | exact GlobalTheory.FlagZ.TautUniq.vecSec_mem_range_stepMap_iff | (intros; apply GlobalTheory.FlagZ.TautUniq.vecSec_mem_range_stepMap_iff <;> assumption)
