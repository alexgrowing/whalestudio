import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.DomSurj

open CategoryTheory.Limits

theorem isProper_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsProper f := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  infer_instance

theorem surjective_cxPts_map : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (E : ℕ), IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ σ : k →+* ℂ, Function.Surjective (Points.PtsOver.map π hπ (spMap σ) : CxPts q σ → CxPts p σ) := by
  intro k _ X _ p D hX Y _ q E hY π hπ hgen σ x
  have := isProper_of_projOver hX.isProjOver
  have : IsProper (π ≫ p) := hπ ▸ isProper_of_projOver hY.isProjOver
  have : IsProper π := IsProper.of_comp π p

  have hsurj : Function.Surjective π := by
    have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
    have hall : Set.range π = Set.univ := by
      rw [← Set.univ_subset_iff, ← genericPoint_closure X, hcl.closure_subset_iff]
      exact Set.singleton_subset_iff.2 ⟨_, hgen⟩
    exact Set.range_eq_univ.1 hall
  obtain ⟨y, hy⟩ := hsurj (x.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x.1) y
    (IsLocalRing.closedPoint ℂ) hy
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x.1)
  obtain ⟨c, -, hc'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(Limits.pullback π x.1)))
    ⟨z, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨⟨pointOfClosedPoint (pullback.snd π x.1) c hc ≫ pullback.fst π x.1, ?_⟩, Subtype.ext ?_⟩
  · rw [← hπ, ← Category.assoc, Category.assoc _ _ π, pullback.condition,
      ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp, x.2]
  · show (pointOfClosedPoint (pullback.snd π x.1) c hc ≫ pullback.fst π x.1) ≫ π = x.1
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

end GlobalTheory.DomSurj
