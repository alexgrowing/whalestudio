import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem exists_isDivOfForm_and_toPic : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → (∃ K : CartierDiv Y, IsDivOfForm K η) ∧ ∀ K : CartierDiv Y, IsDivOfForm K η → ∀ Kc : CanonLB q n, toPic K = cls Kc.bundle Kc.isLB := by
  intro k _ _ Y _ _ q n _ η hη
  obtain ⟨c, hc⟩ := (isFreeGen_baseForm q n).2 η
  replace hc : c • baseForm q n = η := hc
  have h0 : c ≠ 0 := fun e => hη (by rw [← hc, e, zero_smul])
  have h := (isDivOfForm_canonical q n).smul (Units.mk0 c h0)
  rw [Units.val_mk0, hc] at h
  refine ⟨⟨_, h⟩, fun K hK Kc => ?_⟩
  rw [hK.unique hη h, map_add, toPic_principal]
  simpa using (presents_canonical q n).toPic_eq.trans ((cls_eq_iff _ _).2 (CanonLB.lbIso _ Kc))

end GlobalTheory.Discrepancy
