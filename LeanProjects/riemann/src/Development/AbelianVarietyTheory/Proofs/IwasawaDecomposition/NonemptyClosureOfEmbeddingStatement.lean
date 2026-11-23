import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyClosureOfEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_closure_of_embedding : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (Z : Scheme.{0}) (s : Z ⟶ Sp O), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → Flat s → ∀ (C : Coc Z) (N : ℕ), Nonempty (C.Emb N) → ∀ (ch : Charts Z) (r : ℕ) (D : C.Sub ch r), Nonempty (D.Closure s) := by
  first | exact @GlobalTheory.nonempty_subClosure | exact GlobalTheory.nonempty_subClosure | (intros; apply GlobalTheory.nonempty_subClosure <;> assumption)
