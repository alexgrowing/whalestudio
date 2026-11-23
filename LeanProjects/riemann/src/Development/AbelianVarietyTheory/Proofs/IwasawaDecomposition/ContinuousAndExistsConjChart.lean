import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjChart

open ReciprocityTheory.L2DbarEstimates (V)

noncomputable def conjCoord (d : ℕ) : V d ≃ₜ V d where
  toFun v := WithLp.toLp 2 (star v.ofLp)
  invFun v := WithLp.toLp 2 (star v.ofLp)
  left_inv v := by simp
  right_inv v := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem differentiableAt_conj_comp {d : ℕ} {F : V d → ℂ} {v : V d}
    (h : DifferentiableAt ℂ F (conjCoord d v)) :
    DifferentiableAt ℂ (fun w => starRingEnd ℂ (F (conjCoord d w))) v := by
  have h1 : DifferentiableAt ℂ (F ∘ (EuclideanSpace.equiv (Fin d) ℂ).symm) (star v.ofLp) :=
    h.comp (star v.ofLp) (EuclideanSpace.equiv (Fin d) ℂ).symm.differentiableAt
  have h2 := h1.star_star
  rw [star_star] at h2
  exact h2.comp v (EuclideanSpace.equiv (Fin d) ℂ).differentiableAt

section

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ}

noncomputable def conjPts (p : Y ⟶ Sp k) (h : σ = (starRingEnd ℂ).comp σ') : CxPts p σ' ≃ₜ CxPts p σ :=
  (Points.conjHomeomorph Y).subtype fun y => by
    have e : spMap σ = spMap (starRingEnd ℂ) ≫ spMap σ' := by
      rw [h, spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    change y ≫ p = _ ↔ (spMap (starRingEnd ℂ) ≫ y) ≫ p = _
    rw [e, Category.assoc]
    exact (Points.conjHomeomorph (Sp k)).injective.eq_iff.symm

theorem mem_ptsIn_of_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    {U : Y.Opens} (hy : y ∈ ptsIn p σ U) : y' ∈ ptsIn p σ' U := by
  change ⊤ ≤ y'.1 ⁻¹ᵁ U
  rw [h]
  exact fun x _ => hy (Set.mem_univ _)

noncomputable def conjChart (h : σ = (starRingEnd ℂ).comp σ') {d : ℕ} (c : AlgChart p σ' d) : AlgChart p σ d where
  e := ((conjPts p h).symm.transOpenPartialHomeomorph c.e).transHomeomorph (conjCoord d)
  U := c.U
  affine := c.affine
  x := c.x
  etale := c.etale
  source_subset y hy := by
    obtain ⟨z, rfl⟩ := (conjPts p h).surjective y
    have hz : (conjPts p h).symm (conjPts p h z) ∈ c.e.source := hy
    rw [Homeomorph.symm_apply_apply] at hz
    exact mem_ptsIn_of_conj rfl (c.source_subset hz)
  apply_eq y hy a := by
    obtain ⟨z, rfl⟩ := (conjPts p h).surjective y
    have hz : (conjPts p h).symm (conjPts p h z) ∈ c.e.source := hy
    change starRingEnd ℂ (c.e ((conjPts p h).symm (conjPts p h z)) a) = _
    rw [Homeomorph.symm_apply_apply] at hz ⊢
    rw [c.apply_eq z hz]
    exact (CxPts.ev_conj rfl (c.source_subset hz) _).symm
  holo W f v hv := by
    have h1 : conjCoord d v ∈ c.e.target := hv.1
    have h2 : conjPts p h (c.e.symm (conjCoord d v)) ∈ ptsIn p σ W := hv.2
    have h3 : c.e.symm (conjCoord d v) ∈ ptsIn p σ' W := by
      have := mem_ptsIn_of_conj (y' := (conjPts p h).symm (conjPts p h (c.e.symm (conjCoord d v)))) rfl h2
      rwa [Homeomorph.symm_apply_apply] at this
    have ho := GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn W)
    have hd := differentiableAt_conj_comp ((c.holo W f).differentiableAt (ho.mem_nhds ⟨h1, h3⟩))
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [(ho.preimage (conjCoord d).continuous).mem_nhds ⟨h1, h3⟩] with w hw
    exact CxPts.ev_conj (y' := conjPts p h (c.e.symm (conjCoord d w))) rfl hw.2 f

end

theorem continuous_and_exists_conj_chart :
    ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d p] (σ σ' : k →+* ℂ) (j : CxPts p σ' → CxPts p σ), σ = (starRingEnd ℂ).comp σ' → IsConjMap j → Continuous j ∧ ∀ c' : AlgChart p σ' d, ∃ c : AlgChart p σ d, (∀ z, j z ∈ c.e.source ↔ z ∈ c'.e.source) ∧ ∀ z ∈ c'.e.source, ∀ a, c.e (j z) a = starRingEnd ℂ (c'.e z a) := by
  intro k _ Y p d _ σ σ' j h hj
  obtain rfl : j = conjPts p h := funext fun z => Subtype.ext (hj z)
  refine ⟨(conjPts p h).continuous, fun c => ⟨conjChart h c, fun z => ?_, fun z _ a => ?_⟩⟩
  · change (conjPts p h).symm (conjPts p h z) ∈ c.e.source ↔ _
    rw [Homeomorph.symm_apply_apply]
  · change starRingEnd ℂ (c.e ((conjPts p h).symm (conjPts p h z)) a) = _
    rw [Homeomorph.symm_apply_apply]

end GlobalTheory.ConjChart
