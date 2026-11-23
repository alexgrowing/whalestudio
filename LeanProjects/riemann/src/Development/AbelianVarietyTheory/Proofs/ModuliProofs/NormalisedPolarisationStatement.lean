import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormalisedPolarisation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.normalised_polarisation' : Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (w w' : P.A ⟶ P.A), IsMonHom w → IsMonHom w' → w * w' = 𝟙 P.A → LBIso (cubeLB P.A ![fst P.A P.A ≫ w, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ w'] P.L) → ∀ M : LB P.A.left, M = cubeLB P.A ![𝟙 P.A, w] P.L → M.IsLB ∧ Out.Rigidified P.A M ∧ Out.Sym P.A M ∧ Out.RelAmple P.A M ∧ Out.KTriv P.A M ∧ LBIso (abelian₂ P.A M) (abelian₂ P.A P.L) ∧ LBIso M (cubeLB P.A ![𝟙 P.A, w] M) ∧ LBIso (cubeLB P.A ![fst P.A P.A ≫ w, snd P.A P.A] M) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ w'] M) := by
  first | exact @GlobalTheory.PrimNormPol.normalised_polarisation | exact GlobalTheory.PrimNormPol.normalised_polarisation | (intros; apply GlobalTheory.PrimNormPol.normalised_polarisation <;> assumption)
