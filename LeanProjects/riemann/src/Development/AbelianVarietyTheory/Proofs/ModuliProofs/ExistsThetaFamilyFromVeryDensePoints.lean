import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaSchemeSectionsGoodFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyAdditionMorphismThetaLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsInversionEndomorphismsThetaLevelFamilyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarisedOfVeryDenseFibresStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSquareLevelWithGivenThetaPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem exists_tObj_of_veryDense : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → TMap t' t (spMap x) := by
  intro h1 h2 g J _ Mat κ n hn hodd
  obtain ⟨j1, H1⟩ := GlobalTheory.T.exists_theta_scheme_sections_good_fibres h1 h2 g J Mat κ n hn hodd
  obtain ⟨j2, H2⟩ := GlobalTheory.T.exists_family_addition_morphism_thetaLevel h1 h2 g J Mat κ n hn hodd
  obtain ⟨j3, H3⟩ := GlobalTheory.T.exists_inversion_endomorphisms_thetaLevelFamily h1 h2 g J Mat κ n hn hodd
  obtain ⟨j4, H4⟩ := GlobalTheory.T.exists_principallyPolarised_of_veryDense_fibres h1 h2 g J Mat κ n hn hodd
  refine ⟨j1 + j2 + j3 + j4 + 4, ?_⟩
  intro j hj o _ b R _ _ _ β v hv
  obtain ⟨Z, I, M, th, sc, p, hZ, hfib⟩ := H1 j (by omega) o b R β v hv
  obtain ⟨m, hm⟩ := H2 j (by omega) o b R β v Z I M th sc p hv hZ hfib
  obtain ⟨F, hF⟩ := H3 j (by omega) o b R β v Z I M th sc p hv hZ hfib
  obtain ⟨P, act, Q, hP, hgood⟩ := H4 j (by omega) o b R β v Z I M th sc p m F hv hZ hfib hm hF
  obtain ⟨t, ht, hlast⟩ := GlobalTheory.T.exists_square_level_with_given_thetaPoint h1 h2 g n j J hn hodd (by omega) o b R β v P act Q hP (by
    intro q f hq hf
    obtain ⟨p', ⟨K, iK, iK', x, t', hker, hsh, hth⟩, hp'⟩ := hv q f hq hf
    obtain ⟨ψ, hψ⟩ := hgood K x t' hsh hth
    exact ⟨p', ⟨K, iK, iK', x, t', ψ, hker, hth, hψ⟩, hp'⟩)
  refine ⟨t, ht, ?_⟩
  intro K _ _ x t' hsh hth
  obtain ⟨ψ, hψ⟩ := hgood K x t' hsh hth
  exact hlast K x t' ψ hth hψ

end GlobalTheory.ZM
