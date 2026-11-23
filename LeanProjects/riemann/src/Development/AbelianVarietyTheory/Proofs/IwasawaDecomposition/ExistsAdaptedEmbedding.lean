import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRefinedCocycleEmbeddingStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag

theorem basAt_basAt_tau {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} {t : SAB H X} {S : Type} [CommRing S] {Z : Scheme.{0}} {π : Z ⟶ X} {U U' : Z.Opens}
    {hU : IsAffineOpen U} (hU' : IsAffineOpen U') (le : U' ≤ U) {κ : Type} [Finite κ]
    (b : Module.Basis κ Γ(Z, U) (TanM (tau hU ≫ π) t.G)) (w : Sp S ⟶ Z) (hw : ⊤ ≤ w ⁻¹ᵁ U') :
    basAt (hU := hU') (basAt b (tau hU') (tau_le hU' le)) w hw =
      basAt b w (le_preimage_mono le hw) := by
  refine Module.Basis.eq_of_apply_eq fun i => ?_
  rw [basAt, basPull_apply]
  exact tanPull_basAt b _ _ _ (by rw [tau, spMap_ev]) _ _ i

theorem exists_adapted_emb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ) (k : ℕ), Geo M π → Nonempty (Adapted A σ k) → ∃ (D : Adapted A σ k) (N : ℕ), Nonempty (D.C.Emb N) := by
  intro E _ _ _ H Dw l Xo c V _ M X π ty A σ k hG ⟨D⟩
  obtain ⟨Γ, a, B, aff, cover, le, N, hN⟩ := GlobalTheory.T.exists_refined_cocycle_embedding V X (π ≫ M.s) hG.proj D.C
  refine ⟨{ C := D.C.refine a B aff cover le
            b := fun g => basAt (D.b (a g)) (tau (aff g)) (tau_le (aff g) (le g))
            int := fun g K _ w hw u hu j hj => ?_
            coord := fun g d S _ z hg hd v => ?_ }, N, hN⟩
  · have := D.int (a g) K w (le_preimage_mono (le g) hw) u hu j hj
    rw [← basAt_basAt_tau (aff g) (le g) (D.b (a g)) w hw] at this
    exact this
  · have := D.coord (a g) (a d) S z (le_preimage_mono (le g) hg) (le_preimage_mono (le d) hd) v
    rw [← D.C.refine_tr a B aff cover le g d z hg hd] at this
    unfold crd at this
    rw [← basAt_basAt_tau (aff g) (le g) (D.b (a g)) z hg, ← basAt_basAt_tau (aff d) (le d) (D.b (a d)) z hd] at this
    exact this

end GlobalTheory.DRFlag
