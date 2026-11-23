import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRefinedCocycleEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_refined_cocycle_embedding : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (Z : Scheme.{0}) (s : Z ⟶ Sp O), IsProjOver s → ∀ C : Coc Z, ∃ (Γ : Type) (a : Γ → C.A) (D : Γ → Z.Opens) (aff : ∀ g, IsAffineOpen (D g)) (cover : ∀ x : Z, ∃ g, x ∈ D g) (le : ∀ g, D g ≤ C.B (a g)) (N : ℕ), Nonempty ((C.refine a D aff cover le).Emb N) := by
  first | exact @GlobalTheory.DRFlag.Coc.exists_refine_emb | exact GlobalTheory.DRFlag.Coc.exists_refine_emb | (intros; apply GlobalTheory.DRFlag.Coc.exists_refine_emb <;> assumption)
