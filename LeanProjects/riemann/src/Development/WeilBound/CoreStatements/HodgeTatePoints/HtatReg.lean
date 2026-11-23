import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenRing
import Development.WeilBound.CoreStatements.HodgeTatePoints.HcptgenChart

noncomputable section

namespace PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

theorem chart_le_regAt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
    {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
    (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω]
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    (s : ∀ k, J k) (q : Cpt 𝔐.ξ) (hs : InChart 𝔐.ξ (mseg y) s q) (hq : OverZp 𝔐 p q)
    (a : chartRing o (mseg y) s) : (a : Ω) ∈ regAt 𝔐.ξ q := by
  have ha : (a : Ω) ∈ Algebra.adjoin o (Set.range fun j => mseg y j / mseg y s) :=
    (Hcptgen.chartRing_mseg (o := o) y s hs.1).le a.2
  obtain ⟨b, hb, h⟩ := Hcptgen.mem_adjoin_loc Fact.out ho _ ha
  have h3 := (𝔐.tie.ring s hs.1 _).1 h q hs
  have h4 := (Hcptgen.overZp_iff Fact.out q).1 hq b hb
  have := mul_mem h3 h4.2.2
  rwa [mul_assoc, mul_inv_cancel₀ h4.1, mul_one] at this

end PositivityTheory.HtPt.Htat
