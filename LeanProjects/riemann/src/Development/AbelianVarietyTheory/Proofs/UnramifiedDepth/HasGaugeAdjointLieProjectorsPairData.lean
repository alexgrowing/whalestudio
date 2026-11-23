import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsOrthogonalAdjointProjectorsPlacePairsStatement

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem hasProj_pairData : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), HasProj (Y.raw p) V := by
  intro C _ _ V O _ _ dd Y d _ I _ p
  obtain ⟨M, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_adjoint_projectors_placePairs C V O dd Y d Unit (fun _ => I) (fun _ => p) (by
    rintro ⟨⟨⟩, x⟩ ⟨⟨⟩, x'⟩ hne
    exact p.em_sep x x' (fun h => hne (by rw [h])))
  refine ⟨M (), (h1 ()).1, (h1 ()).2, fun g c => h2 () g c, fun g c => h3 () g () (1 - g) c ?_,
    fun g v => h4 () g v⟩
  intro h
  have h' : g = 1 - g := (Prod.ext_iff.mp h).2
  revert h'
  fin_cases g <;> decide

end GlobalTheory
