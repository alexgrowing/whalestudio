import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag

attribute [local instance] Over.cartesianMonoidalCategory in
open scoped CategoryTheory.Obj in

theorem exists_affine_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Y : Scheme.{0}} (t : SAB H Y) (y : Y) :
    ∃ (U : Y.Opens) (n : ℕ), y ∈ U ∧ ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Y), ⊤ ≤ z ⁻¹ᵁ U →
      Nonempty (Module.Basis (Fin n) S (TanM z t.G)) := by
  have := t.semi.smooth
  obtain ⟨U, hU, hy, -, n, v₀, hv⟩ := GlobalTheory.exists_affine_lieBasis_baseChange Y t.G y ⊤ trivial
  refine ⟨U, n, hy, fun S _ z hz => ?_⟩
  have key : ∀ (f : Γ(Y, U) →+* S) (z : Sp S ⟶ Y), spMap f ≫ hU.fromSpec = z →
      Nonempty (Module.Basis (Fin n) S (TanM z t.G)) := by
    rintro f _ rfl
    have h := isGrpPullback_pullback t.G (spMap f ≫ hU.fromSpec)
    obtain ⟨v', -, hb⟩ := hv S f _ _ h
    let u : Fin n → TanM (spMap f ≫ hU.fromSpec) t.G := fun j =>
      ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT (pushHom h (epsR S) (v' j)) ((ReciprocityTheory.ChartRestriction.G.PullbackSections.isTangent_iff h _).1 (hb.1 j))
    have h1 : FrameBC.Full u := (FrameBC.full_iff h (fun _ => rfl)).1 hb
    refine ⟨Module.Basis.mk (v := u) (Fintype.linearIndependent_iff.2 fun a ha => congrFun
      ((h1 0).unique ha.symm (by simp : (0 : TanM _ t.G) = ∑ i, (0 : Fin n → S) i • u i))) fun w _ => ?_⟩
    obtain ⟨a, rfl, -⟩ := h1 w
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact key _ z (spMap_ev z hU hz)

theorem initSpan_zero' {K N : Type} [CommRing K] [AddCommGroup N] [Module K N] {m : ℕ} (u : Fin m → N) :
    initSpan K u 0 = ⊥ := by
  simp [initSpan]

theorem intStep_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ), IntStep A σ 0 := by
  intro E _ _ _ H Dw l Xo c V _ M X π ty A σ x
  obtain ⟨U₀, n, hx, hb⟩ := exists_affine_basis M.t (π x)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ((π ⁻¹ᵁ U₀ : X.Opens) : Set X) from hx) (π ⁻¹ᵁ U₀).isOpen
  obtain ⟨b⟩ := hb _ (tau hU ≫ π) (le_preimage_map π hle (tau_le hU le_rfl))
  refine ⟨U, hU, n, b.reindex (Equiv.emptySum (Fin 0) (Fin n)).symm, hxU, fun K _ w hw u _ j hj => ?_⟩
  obtain rfl : j = 0 := Nat.le_zero.1 hj
  rw [initSpan_zero', initSpan_zero']

end GlobalTheory.DRFlag
