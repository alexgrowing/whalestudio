import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitMemRangeJKOfMemRangeJ
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ChartNotAb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem subsingleton_of_closed_mem_abLocus {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {t : SAB H (Sp R)}
    (P : PELUnif (maximalIdeal R) t) (hc : (closedPoint R : Sp R) ∈ abLocus t.G) : Subsingleton P.D.toPre.X := by
  have hmax : (maximalIdeal R ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (R ⧸ maximalIdeal R ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have hle : maximalIdeal R ^ (0 + 1) ≤ (closedPoint R).asIdeal := by
    rw [zero_add, pow_one]; exact le_rfl
  obtain ⟨q, hq⟩ : closedPoint R ∈ Set.range (PrimeSpectrum.comap
      (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    exact hle
  let g := P.U.gt 0
  have m : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hq' : thick R (maximalIdeal R) 0 q ∈ abLocus t.G := by
    rw [← hq] at hc; exact hc
  exact ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF _ q hq' P.D.toPre.X g.i g.i_hom

end GlobalTheory.ChartNotAb

open GlobalTheory.ChartNotAb in

theorem GlobalTheory.UChart.closedPoint_not_mem_abLocus_of_isTaut : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)), IsTaut C → 1 ≤ C.m → closedPoint (ChartRing k m e) ∉ abLocus C.t.G := by
  intro E _ _ _ H Dw l Xo c φ k _ m e C hT hm hc
  obtain ⟨-, -, -, -, -, ⟨N, s, ε, τ₀, -, hε, -, -⟩, -⟩ := hT
  have hs := subsingleton_of_closed_mem_abLocus C.P hc
  let i : Fin C.m := ⟨0, hm⟩
  apply ε.ne_zero (Sum.inl i)
  apply Subtype.ext
  rw [Submodule.coe_zero, hε i]
  ext x y
  rw [Subsingleton.elim x 0]
  simp
