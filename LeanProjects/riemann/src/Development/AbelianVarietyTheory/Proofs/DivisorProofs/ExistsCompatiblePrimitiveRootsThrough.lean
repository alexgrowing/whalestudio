import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLevelPointsOfLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PelOKOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.SqrtNegDiscMemCoeffField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.RootSystem

theorem exists_compatible_roots_through (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : ℕ) (ω : K)
    (hA : 0 < A) (hω : IsPrimitiveRoot ω A) :
    ∃ ζ : ℕ → Kˣ, (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) ∧
      (ζ A : K) = ω := by
  have hz : IsPrimitiveRoot (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A) A := GlobalTheory.HostModel.isPrimitiveRoot_zeta hA
  have hint : IsIntegral ℚ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A) := (hz.isIntegral hA).tower_top
  let L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A}
  haveI : FiniteDimensional ℚ L := IntermediateField.adjoin.finiteDimensional hint
  let pb := IntermediateField.adjoin.powerBasis hint
  have hroot : Polynomial.aeval ω (minpoly ℚ pb.gen) = 0 := by
    have hm : minpoly ℚ pb.gen = minpoly ℚ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A) := by
      rw [IntermediateField.adjoin.powerBasis_gen]; exact IntermediateField.minpoly_gen ℚ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A)
    rw [hm, ← Polynomial.cyclotomic_eq_minpoly_rat hz hA, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic]
    exact (hω.isRoot_cyclotomic hA)
  let f : L →ₐ[ℚ] K := pb.lift ω hroot
  obtain ⟨ζ, h1, h2, h3⟩ := GlobalTheory.HostModel.exists_roots L K f.toRingHom
  refine ⟨ζ, h1, h2, ?_⟩
  have hg := h3 A hA (IntermediateField.AdjoinSimple.gen ℚ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta A)) rfl
  rw [hg]
  have : f pb.gen = ω := pb.lift_gen ω hroot
  rw [IntermediateField.adjoin.powerBasis_gen] at this
  exact this

example : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (A : ℕ) (ω : K), 0 < A → IsPrimitiveRoot ω A → ∃ ζ : ℕ → Kˣ, (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) ∧ (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) ∧ (ζ A : K) = ω :=
  @exists_compatible_roots_through

end GlobalTheory.RootSystem
