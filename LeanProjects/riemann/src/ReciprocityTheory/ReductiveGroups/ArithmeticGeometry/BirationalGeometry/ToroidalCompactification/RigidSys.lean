import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi

def UniqWitSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (χ : Sp (PowerSeries k) ⟶ Y.X)
    (W W' : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (y : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = Out.jK (PowerSeries k) ≫ χ →
    y ≫ pullback.snd _ _ = Out.jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF →
    ∃ ψ : W.t.G ≅ W'.t.G, W.Agree W' ψ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

theorem mem_range_jK {k : Type} [Field k] (x : Sp (PowerSeries k)) (hx : PowerSeries.X ∉ x.asIdeal) :
    x ∈ Set.range (Out.jK (PowerSeries k)) := by
  have hXu : ¬ IsUnit (PowerSeries.X : PowerSeries k) := by
    intro hu
    first
      | (have h1 := hu.map (PowerSeries.constantCoeff k); simp at h1)
      | (have h1 := hu.map (PowerSeries.constantCoeff (R := k)); simp at h1)
  have hbot : x.asIdeal = ⊥ := by
    by_contra hne
    have hmax : x.asIdeal.IsMaximal := x.isPrime.isMaximal hne
    apply hx
    rw [IsLocalRing.eq_maximalIdeal hmax, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hXu
  have hx' : x ∈ Set.range (PrimeSpectrum.comap
      (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))) := by
    rw [PrimeSpectrum.localization_comap_range (FractionRing (PowerSeries k))
      (nonZeroDivisors (PowerSeries k))]
    show Disjoint _ _
    rw [hbot, Set.disjoint_left]
    intro a ha ha'
    exact nonZeroDivisors.ne_zero ha ((Submodule.mem_bot _).1 ha')
  obtain ⟨y, hy⟩ := hx'
  exact ⟨y, hy⟩

theorem mono_spMap_subtype {F : Type} [Field F] (V : ValuationSubring F) : Mono (spMap V.subtype) := by
  have h : Epi (CommRingCat.ofHom (algebraMap V F)) := IsLocalization.epi (nonZeroDivisors V) F
  show Mono (Spec.map (CommRingCat.ofHom (algebraMap V F)))
  exact Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap V F)).op

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
