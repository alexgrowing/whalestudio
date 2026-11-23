import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.DivDescent

theorem exists_mem_associated_of_map_eq {A R : Type} [CommRing A] [CommRing R] [IsDomain R] [IsLocalRing R]
    (φ : A →+* R) (I : Ideal A) {h : R} (hh : h ≠ 0) (hI : I.map φ = Ideal.span {h}) :
    ∃ a ∈ I, Associated (φ a) h := by
  by_contra hne
  push_neg at hne
  have hle : I.map φ ≤ Ideal.span {h} * maximalIdeal R := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have hm : φ a ∈ Ideal.span {h} := hI ▸ Ideal.mem_map_of_mem φ ha
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hm
    rw [Ideal.mem_comap, Ideal.mem_span_singleton_mul]
    refine ⟨r, ?_, by rw [mul_comm]; exact hr⟩
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hne a ha (Associated.symm ⟨hu.unit, by rw [IsUnit.unit_spec, mul_comm]; exact hr⟩)
  have hmem : h ∈ Ideal.span {h} * maximalIdeal R := hle (hI ▸ Ideal.mem_span_singleton_self h)
  obtain ⟨x, hx, hxe⟩ := Ideal.mem_span_singleton_mul.mp hmem
  have : x = 1 := mul_left_cancel₀ hh (by rw [hxe, mul_one])
  exact (mem_maximalIdeal x).mp hx (this ▸ isUnit_one)

theorem isNoetherianRing_stalk {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (x : Z.X) :
    IsNoetherianRing (Z.X.presheaf.stalk x) := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI := GlobalTheory.SchemeWords.isProper_of_isProjOver Z.proj
  haveI : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  infer_instance

end GlobalTheory.DivDescent
