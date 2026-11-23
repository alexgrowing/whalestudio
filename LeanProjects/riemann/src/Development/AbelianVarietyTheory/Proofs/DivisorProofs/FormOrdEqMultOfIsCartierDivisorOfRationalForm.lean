import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem DivOver.formOrd_eq_mult_of_isDivOfForm : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ K : CartierDiv Y, IsDivOfForm K η → ∀ (E : DivOver q) (w : Y), E.IsAt w → E.formOrd η = K.mult w := by
  intro k _ _ Y _ _ q n _ η hη K hK E w hE
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q n ‹_›
  obtain ⟨U, ω, hU, hω⟩ := exists_isFrame q n w
  have hgen := isFreeGen_formOf (gen_mem hU) hω
  have h0 : formOf U (gen_mem hU) ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨c, hc⟩ := hgen.2 η
  have hc0 : c ≠ 0 := fun e => hη (by rw [← hc, e]; exact zero_smul _ _)
  have h1 := hK U ω hω w hU (Units.mk0 c hc0) hc.symm
  have h2 := E.formOrd_smul hn h0 (Units.mk0 c hc0)
  rw [DivOver.formOrd_formOf_eq_zero hU hE hω, add_zero] at h2
  replace h2 : E.formOrd η = E.ord (Units.mk0 c hc0) := hc ▸ h2
  rw [h2, h1.mult_eq, hE.ord_eq]

end GlobalTheory.Discrepancy
