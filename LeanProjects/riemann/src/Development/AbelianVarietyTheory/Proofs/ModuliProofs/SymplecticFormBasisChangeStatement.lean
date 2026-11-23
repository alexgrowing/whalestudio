import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange
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
theorem _root_.GlobalTheory.T.symplectic_form_basis_change : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (g k : ℕ) (J La : Type) [AddCommGroup La] (EF : La → La → ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La), (∀ x x' y, EF (x + x') y = EF x y + EF x' y) → (∀ x y y', EF x (y + y') = EF x y + EF x y') → (∀ i j, EF (bas (Pi.single i 1)) (bas (Pi.single j 1)) = Out.stdSymp g i j) → (∀ x y, EF (bas' x) (bas' y) = omegaStd x y) → ∀ (o B : Type) [CommRing o] [CommRing B] (b : TBase o k) (ζ : B) (S : Scheme.{0}) (s : S ⟶ Sp o) (s' : S ⟶ Sp B) (t : TObj g k J b s), 1 ≤ k → (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (β : o →+* K) (β' : B →+* K), x ≫ s = spMap β → x ≫ s' = spMap β' → β (b.ζ : o) = β' ζ) → ∃ c : SiegPre g k ζ s', c.Principal ∧ TSieg bas bas' t c := by
  first | exact @GlobalTheory.SiegelOfTheta.exists_siegPre | exact GlobalTheory.SiegelOfTheta.exists_siegPre | (intros; apply GlobalTheory.SiegelOfTheta.exists_siegPre <;> assumption)
