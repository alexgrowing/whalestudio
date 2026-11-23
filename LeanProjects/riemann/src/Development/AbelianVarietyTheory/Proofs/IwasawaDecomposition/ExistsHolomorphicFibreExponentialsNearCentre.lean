import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianExponentialAlongDisc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh

theorem isExpAt_homMk {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    {g : ℕ} (y₁ y₂ : Sp ℂ ⟶ X) (hy : y₁ = y₂) (e : (Fin g → ℂ) → (Over.mk y₁ ⟶ t.G))
    (hw : ∀ w, (e w).left ≫ t.G.hom = y₂)
    (hadd : ∀ z w, e (z + w) = e z * e w)
    (h1 : ∀ w, ∃! v : epsPt y₁ ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left)
    (h2 : ∀ v : epsPt y₁ ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) :
    IsExpAt t y₂ (fun w => (Over.homMk (e w).left (hw w) : Over.mk y₂ ⟶ t.G)) := by
  subst hy
  have he : (fun w => (Over.homMk (e w).left (hw w) : Over.mk y₁ ⟶ t.G)) = e :=
    funext fun w => Over.OverMorphism.ext rfl
  rw [he]
  have hzero : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  refine ⟨hadd, fun w => ?_, fun v hv => ?_⟩
  · obtain ⟨V, hV, hVu⟩ := h1 w
    refine ⟨V.left, ⟨⟨V.w, ?_⟩, hV⟩, fun v hv => ?_⟩
    · rw [hV.1]; exact congrArg Over.Hom.left hzero
    · have := hVu (Over.homMk v hv.1.1) hv.2
      exact congrArg CommaMorphism.left this
  · exact h2 (Over.homMk v hv.1) (by rw [hzero]; exact hv.2)

end GlobalTheory.ShFam.Hor.LogCh

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exists_expMaps_near_chart_centre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n : ℕ) (e0 : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)), (0 : Fin n → ℂ) ∈ e0.target → IsHolTo e0.target (fun z => (e0.symm z).1) → ∃ (g : ℕ) (ρ : ℝ) (ex : ExpMaps Z σ g), 0 < ρ ∧ Metric.ball 0 ρ ⊆ e0.target ∧ IsHolTo (Metric.ball 0 ρ ×ˢ Set.univ) (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e0.symm zw.1) zw.2).left) ∧ ∀ x ∈ e0.source, ‖e0 x‖ < ρ → Function.Surjective (ex x) ∧ IsExpAt Z.t (x.1 ≫ genι Z) (ex x) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n e0 h0 hsy
  let y : (Fin n → ℂ) → (Sp ℂ ⟶ Z.X) := fun z => (e0.symm z).1 ≫ genι Z
  have hy : IsHolTo e0.target y := GlobalTheory.RelExp.isHolTo_of_holAt e0.open_target fun z hz =>
    GlobalTheory.RelExp.HolAt.post ⟨e0.target, e0.open_target, hz, hsy⟩ (genι Z)
  obtain ⟨g, B', e, hB', hb', hfib, -⟩ := GlobalTheory.RelExp.exists_relative_exp_of_smooth _ Z.t.G n e0.target y 0
    Z.t.semi.smooth Z.t.semi.geomConnected e0.open_target h0 hy
  obtain ⟨ρ, hρ, hρB⟩ := Metric.isOpen_iff.1 (hB'.inter e0.open_target) 0 ⟨hb', h0⟩
  have hyx : ∀ x ∈ e0.source, y (e0 x) = x.1 ≫ genι Z := fun x hx => by simp only [y, e0.left_inv hx]
  have hw : ∀ x (hx : x ∈ e0.source) w, (e (e0 x) w).left ≫ Z.t.G.hom = x.1 ≫ genι Z := fun x hx w =>
    (e (e0 x) w).w.trans (hyx x hx)
  classical
  let ex : ExpMaps Z σ g := fun x w =>
    if hx : x ∈ e0.source then Over.homMk (e (e0 x) w).left (hw x hx w) else 1
  refine ⟨g, ρ, ex, hρ, fun z hz => (hρB hz).2, ?_, fun x hx hxρ => ?_⟩
  · refine GlobalTheory.RelExp.isHolTo_of_holAt (Metric.isOpen_ball.prod isOpen_univ) fun q hq => ?_
    refine ((hfib q.1 (hρB hq.1).1).1 q.2).congr ?_
    filter_upwards [(Metric.isOpen_ball.prod isOpen_univ).mem_nhds hq] with q' hq'
    have hs : e0.symm q'.1 ∈ e0.source := e0.map_target (hρB hq'.1).2
    have hr : e0 (e0.symm q'.1) = q'.1 := e0.right_inv (hρB hq'.1).2
    simp only [ex, dif_pos hs, Over.homMk_left]
    rw [hr]
  · have hb : e0 x ∈ B' := (hρB (mem_ball_zero_iff.2 hxρ)).1
    obtain ⟨-, hadd, hsurj, -, h1, h2⟩ := hfib _ hb
    have hex : ex x = fun w => (Over.homMk (e (e0 x) w).left (hw x hx w) : Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G) := funext fun w => dif_pos hx
    rw [hex]
    refine ⟨fun a => ?_, isExpAt_homMk Z.t _ _ (hyx x hx) _ (hw x hx) hadd h1 h2⟩
    obtain ⟨z, hz⟩ := hsurj (Over.homMk a.left (a.w.trans (hyx x hx).symm))
    have hzl := congrArg CommaMorphism.left hz
    exact ⟨z, Over.OverMorphism.ext hzl⟩

end GlobalTheory.ShFam.Hor.LogCh
