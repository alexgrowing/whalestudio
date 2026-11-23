import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsOfClosureInProjectiveSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_of_closure_in_projective_space : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (s : Z ⟶ Sp O) (f : Z' ⟶ Z) (C : Coc Z) (N : ℕ) (Em : C.Emb N) (q : Z' ⟶ PSpace O N) (Ω : Set Z'), q ≫ PSpace.str O N = f ≫ s → IsReduced Z' → Dense Ω → (∀ (K : Type) [Field K] (w : Sp K ⟶ Z'), Set.range w ⊆ Ω → ∀ (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α), ∃ (ξ : Fin (C.n α) → K) (g : O →+* K) (hv : _), w ≫ q = GlobalTheory.ProjSpace.pt g (((Em.A α).map (ev (w ≫ f) _ h)).mulVec ξ) hv) → ∃ L : C.Line f, ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin (C.n α) → K) (g : O →+* K), w ≫ f ≫ s = spMap g → (L.Carries w α h ξ ↔ ∃ hv, w ≫ q = GlobalTheory.ProjSpace.pt g (((Em.A α).map (ev (w ≫ f) _ h)).mulVec ξ) hv) := by
  first | exact @GlobalTheory.DRFlag.LineOfMap.exists_line | exact GlobalTheory.DRFlag.LineOfMap.exists_line | (intros; apply GlobalTheory.DRFlag.LineOfMap.exists_line <;> assumption)
