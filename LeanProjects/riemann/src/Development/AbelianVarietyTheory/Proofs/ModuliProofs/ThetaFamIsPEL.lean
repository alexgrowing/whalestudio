import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibresStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem GlobalTheory.thetaFam_isPEL : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (n N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∀ F : ThetaFam n em (PELClass (b := b) D a bas ρ em), ∃ τ : SAB H F.MM, IsPEL D a bas ρ F.univ τ := by
  intro h1 h2 h3 E _ _ _ H D g J _ a w w' bas hpq hbas hw hw' hcl n N' o _ b em ρ hρ hem F
  obtain ⟨hded, -, hinj⟩ := hem
  have := F.reduced
  have : LocallyOfFiniteType F.s := by
    obtain ⟨N, i, hi, -, hs⟩ := F.qproj
    have := isProper_str o N
    rw [← hs]
    infer_instance
  have : IsLocallyNoetherian F.MM := LocallyOfFiniteType.isLocallyNoetherian F.s
  exact GlobalTheory.T.exists_isPELTriple_of_dense_fibres h1 h2 h3 E H D g J a bas w w' hpq hbas hw hw' hcl (N' ^ 2) o b em ρ F.MM F.s F.univ hρ hinj F.dense
