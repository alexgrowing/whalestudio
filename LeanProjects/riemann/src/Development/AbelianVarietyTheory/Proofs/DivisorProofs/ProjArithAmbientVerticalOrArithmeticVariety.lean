import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarietyRelativeDimDrop
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixHt

theorem isEmpty_cxPts_of_algebra_zmod {k : Type} [CommRing k] {Y : Scheme.{0}} (q : Y ⟶ Sp k)
    (l : ℕ) [Fact l.Prime] (_ : Algebra (ZMod l) Γ(Y, ⊤)) (σ : k →+* ℂ) : IsEmpty (CxPts q σ) := by
  refine ⟨fun y => ?_⟩
  let f : ZMod l →+* ℂ := (Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp
    (y.1.appTop.hom.comp (algebraMap (ZMod l) Γ(Y, ⊤)))
  have h := map_natCast f l
  rw [ZMod.natCast_self, map_zero] at h
  exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h.symm

theorem amb_vertical_or_arithVar : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ d : ℕ, topologicalKrullDim Y = d → (∃ (l : ℕ) (_ : Fact l.Prime), Nonempty (Algebra (ZMod l) Γ(Y, ⊤)) ∧ ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) ∨ ∃ e : ℕ, d = e + 1 ∧ IsArithVar q e := by
  intro k _ Y _ q hq d hd
  obtain ⟨ℓ, _⟩ := CharP.exists Γ(Y, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Y, ⊤) ℓ with hℓ | rfl
  · have : Fact ℓ.Prime := ⟨hℓ⟩
    exact .inl ⟨ℓ, this, ⟨ZMod.algebra _ ℓ⟩, fun σ => isEmpty_cxPts_of_algebra_zmod q ℓ (ZMod.algebra _ ℓ) σ⟩
  · have hc := CharP.charP_to_charZero Γ(Y, ⊤)
    obtain _ | e := d
    · exact absurd (by simpa using hd) (dim_ne_zero_of_isProjOver q hq.isProjOver hq.finite hc)
    · exact .inr ⟨e, rfl, hq.isDomain, hq.finite, ‹_›, hq.isProjOver,
        (flat_int_iff_charZero _).2 hc, hd⟩

end GlobalTheory.MixHt
