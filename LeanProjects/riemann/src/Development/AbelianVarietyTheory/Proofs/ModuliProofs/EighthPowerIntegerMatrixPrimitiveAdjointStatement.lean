import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerIntegerMatrixPrimitiveAdjoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.eighthPower_integerMatrix_primitive_adjoint : (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (K : Type) [Field K] (o : Type) [CommRing o] (s : Sp K ⟶ Sp o) (h k : ℕ) (ζ : o) (c : SiegPre h k ζ s) (P : Out.PolAV (Sp K)) (pr : Fin 8 → (P.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T : Over (Sp K)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ P.A, ∀ u, x ≫ pr u = y u) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → ∀ (m : Matrix (Fin 8) (Fin 8) ℤ) (α : P.A ⟶ P.A), (∀ u, α ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod) → ((W + W.transpose) * m = W → LBIso P.L (cubeLB P.A ![𝟙 P.A, α] P.L)) ∧ ∀ (m' : Matrix (Fin 8) (Fin 8) ℤ) (α' : P.A ⟶ P.A), (∀ u, α' ≫ pr u = (List.ofFn fun v => pr v ^ m' u v).prod) → m.transpose * (W + W.transpose) = (W + W.transpose) * m' → LBIso (cubeLB P.A ![fst P.A P.A ≫ α, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ α'] P.L) := by
  first | exact @GlobalTheory.PowerAdjoint.matrix_primitive_adjoint | exact GlobalTheory.PowerAdjoint.matrix_primitive_adjoint | (intros; apply GlobalTheory.PowerAdjoint.matrix_primitive_adjoint <;> assumption)
