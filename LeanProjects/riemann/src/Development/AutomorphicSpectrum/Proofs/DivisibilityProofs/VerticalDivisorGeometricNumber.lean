import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabDivCycle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.GeoNumFp

theorem charOf_eq_of_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {W : Ideal (MRing ι ℤ)} (hW : W.IsPrime) {p : ℕ} (hp : p.Prime)
    (hpW : (C (p : ℤ) : MRing ι ℤ) ∈ W) : ¬ IsHorizontal W ∧ charOf W = p := by
  have hv : ¬ IsHorizontal W := by
    intro h
    have hm : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing ι ℤ) := Ideal.mem_comap.mpr hpW
    rw [show W.comap (C : ℤ →+* MRing ι ℤ) = ⊥ from h, Ideal.mem_bot] at hm
    exact hp.ne_zero (by exact_mod_cast hm)
  refine ⟨hv, ?_⟩
  have hq : (charOf W).Prime := ReciprocityTheory.ChartRestriction.G.Geo.charOf_prime hW hv
  have hm : (p : ℤ) ∈ W.comap (C : ℤ →+* MRing ι ℤ) := Ideal.mem_comap.mpr hpW
  have hd : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι ℤ)) ∣ (p : ℤ) :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp hm
  have hd' : charOf W ∣ p := by
    have := Int.natAbs_dvd_natAbs.mpr hd
    simpa [charOf] using this
  exact (Nat.prime_dvd_prime_iff_eq hq hp).mp hd'

theorem geoNum_eq_intNum : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (a : K → ℕ) (f : MRing ι ℤ), IsMultiHomog f a → f ∉ P → ∀ W, divCycle P f W ≠ 0 → ∀ (p : ℕ) [Fact p.Prime], (C (p : ℤ) : MRing ι ℤ) ∈ W → charOf W = p ∧ ¬ IsHorizontal W ∧ ∀ L : Fin D → K → ℤ, geoNum D W L = intNum (ZMod p) (extTo (ZMod p) W) L := by
  intro K _ _ ι _ P D hP a f hf hfP W hW p _ hpW
  have hmem : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W := by
    by_contra h
    exact hW (by simp only [divCycle]; exact dif_neg h)
  obtain ⟨hWmin, hWrel⟩ := hmem
  obtain ⟨-, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  have hWp : W.IsPrime := hWmin.1.1
  have hfa : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a := (VocabMultiHomog.proof ℤ K ι f a).2 hf
  have hWmh : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal W :=
    ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_of_mem_minimalPrimes hPh hfa hWmin
  have := hPp
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.dim_quot_minimal_add_one P W f hfP hWmin
  rw [hPdim] at h1
  have hdim : ringKrullDim (MRing ι ℤ ⧸ W) = ((D + Fintype.card K : ℕ) : WithBot ℕ∞) :=
    ReciprocityTheory.ChartRestriction.G.Geo.withBot_eq_of_add_one
      (by rw [h1, show D + 1 + Fintype.card K = D + Fintype.card K + 1 by omega])
  obtain ⟨hv, hc⟩ := charOf_eq_of_mem hWp (Fact.out : p.Prime) hpW
  exact ⟨hc, hv, fun L =>
    (GroundTheory.Heights₂.Heights.Bridge.intNum_map_eq_geoNum p D W ⟨hWp, hWmh, hWrel⟩ hpW hdim L).symm⟩

end GlobalTheory.CompanionTheory.Ar.Num.GeoNumFp
