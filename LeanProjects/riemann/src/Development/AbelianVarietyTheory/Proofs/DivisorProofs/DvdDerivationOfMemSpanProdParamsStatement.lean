import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdDerivationOfMemSpanProdParams
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_derivation_of_mem_span_prod_params' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] (m : ℕ) (r : Fin m → R), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m r → ∀ (J : Finset (Fin m)) (D : Derivation ℤ R R), D (∏ j ∈ J, r j) ∈ Ideal.span {∏ j ∈ J, r j} → ∀ j ∈ J, r j ∣ D (r j) := by
  first | exact @GlobalTheory.dvd_derivation_of_mem_span_prod_params | exact GlobalTheory.dvd_derivation_of_mem_span_prod_params | (intros; apply GlobalTheory.dvd_derivation_of_mem_span_prod_params <;> assumption)
