import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticDatumModuliFamily
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_datum_moduli_family : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La), (∀ x y, D.EF (bas' x) (bas' y) = omegaStd x y) → ∀ (k : ℕ) (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (em : o →+* ℂ) (ρ : o) (ζ : B) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (s₁ : Sp V ⟶ Sp B) (s' : Sp K ⟶ Sp o) (s₁' : Sp K ⟶ Sp B) (c : SiegPre g k ζ s₁) (c' : SiegPre g k ζ s₁') (t' : TObj g k J b s') (τ' : SAB H (Sp K)), (∃ N' : ℕ, k = N' ^ 2) → em ρ = H.rt0 → ArBase em → s' = spMap (algebraMap V K) ≫ spMap β → c.Principal → SiegPB c' c (spMap (algebraMap V K)) → TSieg bas bas' t' c' → IsPEL D a bas ρ t' τ' → ∃ (t : TObj g k J b (spMap β)) (τ : SAB H (Sp V)), IsPEL D a bas ρ t τ ∧ TMap t' t (spMap (algebraMap V K)) := by
  first | exact @GlobalTheory.PELFromSiegel.exists_isPEL_extension | exact GlobalTheory.PELFromSiegel.exists_isPEL_extension | (intros; apply GlobalTheory.PELFromSiegel.exists_isPEL_extension <;> assumption)
