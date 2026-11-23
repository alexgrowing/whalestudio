import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphism
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_preserving_map_gives_endomorphism : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (M : LB X.A.left) (g : ℕ)
    (u : HolUnif X.A M g) (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ w ∈ u.Λ, T w ∈ u.Λ) →
      ∃ α : X.A ⟶ X.A, IsMonHom α ∧ ∀ w, u.ex (T w) = u.ex w ≫ α := by
  first | exact @GlobalTheory.RealMult.Obj.exists_isMonHom_of_map_lattice | exact GlobalTheory.RealMult.Obj.exists_isMonHom_of_map_lattice | (intros; apply GlobalTheory.RealMult.Obj.exists_isMonHom_of_map_lattice <;> assumption)
