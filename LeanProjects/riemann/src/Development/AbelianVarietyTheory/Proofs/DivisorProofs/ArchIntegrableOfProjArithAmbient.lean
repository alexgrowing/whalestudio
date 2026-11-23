import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem archIntegrable_of_isAmb : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k),
    IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) →
    ∀ (M N : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), N.ArchIntegrable M e hr := by
  intro H k _ Y _ q hq e he M N r hr σ
  rcases isEmpty_or_nonempty (CxPts q σ) with h0 | ⟨⟨y⟩⟩
  · exact ⟨MeasureTheory.Integrable.of_isEmpty, MeasureTheory.Integrable.of_isEmpty⟩
  · have hc : CharZero Γ(Y, ⊤) :=
      RingHom.charZero (S := ℂ) ((Scheme.ΓSpecIso (.of ℂ)).hom.hom.comp y.1.appTop.hom)
    exact H k Y q e ⟨hq.1, hq.2, ‹_›, hq.3, (flat_int_iff_charZero _).2 hc, he⟩ M N r hr σ

end GlobalTheory.MixHt
