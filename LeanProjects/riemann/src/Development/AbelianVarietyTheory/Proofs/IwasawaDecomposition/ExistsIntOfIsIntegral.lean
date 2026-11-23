import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PolArc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {W : ValuationSubring ℂ}

theorem exists_int_of_isIntegral (bV : 𝓞 c.F →+* c.V W) (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F))
    (r₁ : c.V W) (h : IsIntegral ℤ ((r₁ : c.V W) : c.F)) : ∃ r : 𝓞 c.F, bV r = r₁ ∧ (r : c.F) = (r₁ : c.F) :=
  ⟨⟨(r₁ : c.F), h⟩, Subtype.ext ((hbV _).trans rfl), rfl⟩

theorem isIntegral_of_eq_rt0 {x : c.F} (hx : (x : ℂ) = H.rt0) : IsIntegral ℤ x := by
  refine IsIntegral.of_pow two_pos ?_
  have e : x ^ 2 = algebraMap ℤ c.F (-(H.d : ℤ)) := by
    apply Subtype.ext
    change ((x ^ 2 : c.F) : ℂ) = ((algebraMap ℤ c.F (-(H.d : ℤ)) : c.F) : ℂ)
    rw [IntermediateField.coe_pow, hx, H.sqrt_neg_disc_sq]
    simp
  rw [e]
  exact isIntegral_algebraMap

theorem isIntegral_of_eq_zeta {x : c.F} (hx : (x : ℂ) = zeta l.A) : IsIntegral ℤ x := by
  refine IsIntegral.of_pow l.A_pos ?_
  have e : x ^ l.A = 1 := by
    apply Subtype.ext
    change ((x ^ l.A : c.F) : ℂ) = ((1 : c.F) : ℂ)
    rw [IntermediateField.coe_pow, hx]
    exact (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one
  rw [e]
  exact isIntegral_one

def moveV (bV : 𝓞 c.F →+* c.V W) (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) {O' : Type} [CommRing O']
    [IsDomain O'] (b' : c.V W →+* O') (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) :
    ArcIn D l (c.V W).subtype O' b' :=
  { a with
    geom := by
      intro F _ _ _ r₁ z₁ hr₁ hz₁ f hf
      obtain ⟨r, rfl, hr⟩ := exists_int_of_isIntegral bV hbV r₁ (isIntegral_of_eq_rt0 hr₁)
      obtain ⟨z, rfl, hz⟩ := exists_int_of_isIntegral bV hbV z₁ (isIntegral_of_eq_zeta hz₁)
      exact a.geom F r z ((congrArg (fun y : c.F => (y : ℂ)) (hbV r)).symm.trans hr₁)
        ((congrArg (fun y : c.F => (y : ℂ)) (hbV z)).symm.trans hz₁) f hf }

theorem moveV_D₀ (bV : 𝓞 c.F →+* c.V W) (hbV : ∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) {O' : Type} [CommRing O']
    [IsDomain O'] (b' : c.V W →+* O') (a : ArcIn D l (algebraMap (𝓞 c.F) c.F) O' (b'.comp bV)) :
    (moveV bV hbV b' a).D₀ = a.D₀ := rfl

end GlobalTheory.PolArc
