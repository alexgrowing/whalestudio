import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory

theorem dvd_derivation_of_mem_span_prod_params :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] (m : ℕ)
      (r : Fin m → R), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m r → ∀ (J : Finset (Fin m))
      (D : Derivation ℤ R R), D (∏ j ∈ J, r j) ∈ Ideal.span {∏ j ∈ J, r j} →
      ∀ j ∈ J, r j ∣ D (r j) := by
  intro R _ _ _ _ m r hrsp J D hD j hj
  have hprime : ∀ i, Prime (r i) :=
    ReciprocityTheory.AnForm.R.prime_of_regular_params r hrsp.1 hrsp.2
  have hnass : ∀ i k, i ≠ k → ¬ Associated (r i) (r k) :=
    (ReciprocityTheory.AnForm.R.regular_params_spec r hrsp.1 hrsp.2).2
  have hsplit : ∏ i ∈ J, r i = r j * ∏ i ∈ J.erase j, r i :=
    (Finset.mul_prod_erase J r hj).symm
  have hdvdD : r j ∣ D (∏ i ∈ J, r i) := by
    have h1 : (∏ i ∈ J, r i) ∣ D (∏ i ∈ J, r i) := Ideal.mem_span_singleton.mp hD
    exact (hsplit ▸ dvd_mul_right (r j) _ : r j ∣ ∏ i ∈ J, r i).trans h1
  rw [hsplit, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hdvdD
  have h2 : r j ∣ (∏ i ∈ J.erase j, r i) * D (r j) :=
    (dvd_add_right (dvd_mul_right (r j) _)).mp hdvdD
  rcases (hprime j).dvd_or_dvd h2 with h3 | h3
  · exfalso
    obtain ⟨k, hk, hdk⟩ := (hprime j).exists_mem_finset_dvd h3
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    exact hnass j k (Ne.symm hkj) ((hprime j).associated_of_dvd (hprime k) hdk)
  · exact h3

end GlobalTheory
