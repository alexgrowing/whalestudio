import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelPre_pullback_principal_ringChange : ∀ (h k : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j ζ = ζ' → f ≫ s = s' ≫ spMap j → (∀ c : SiegPre h k ζ s, ∃ c' : SiegPre h k ζ' s', SiegPB c' c f) ∧ (∀ (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s'), SiegPB c' c f → c.Principal → c'.Principal) ∧ ∀ c' : SiegPre h k ζ' s', ∃ c₀ : SiegPre h k ζ (s' ≫ spMap j), SiegPB c' c₀ (𝟙 _) ∧ SiegPB c₀ c' (𝟙 _) := by
  first | exact @GlobalTheory.SiegelRingChange.siegPre_pull_ringChange | exact GlobalTheory.SiegelRingChange.siegPre_pull_ringChange | (intros; apply GlobalTheory.SiegelRingChange.siegPre_pull_ringChange <;> assumption)
