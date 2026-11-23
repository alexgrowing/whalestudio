import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointEigenspaceAddConjEqMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEigSp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_jointEigenspace_add_conj_eq_mul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (D' : PLat D.O D.inv) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : D'.La →+ (Fin D.g → ℂ)), IsPeriod D' ρ Q → ∀ τ : D.F →+* ℂ, Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ) + Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) ((starRingEnd ℂ).comp τ)) = D.m * D.n := by
  first | exact @GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq | exact GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq | (intros; apply GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq <;> assumption)
