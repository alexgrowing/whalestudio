import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLatticeRegularAtP
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.second_lattice_regular_at_p : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (κ : F →+* V.X.functionField) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) ℤ) (p n : ℕ) (P Q : Matrix (Fin N) (Fin N) F), p.Prime → IsUnit J.det →
    SecondLat J p n P Q → ∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∀ i j,
      RegAt x (((Q.map κ).transpose * J.map (Int.castRingHom V.X.functionField) * Q.map κ) i j) ∧
      RegAt x ((P.map κ * (J.map (Int.castRingHom V.X.functionField))⁻¹ * (P.map κ).transpose) i j) ∧
      RegAt x ((J.map (Int.castRingHom V.X.functionField))⁻¹ i j) ∧ RegAt x ((n : V.X.functionField) * P.map κ i j) ∧
      RegAt x (J.map (Int.castRingHom V.X.functionField) i j) := by
  first | exact @GlobalTheory.ConstLat.regAt_secondLat | exact GlobalTheory.ConstLat.regAt_secondLat | (intros; apply GlobalTheory.ConstLat.regAt_secondLat <;> assumption)
