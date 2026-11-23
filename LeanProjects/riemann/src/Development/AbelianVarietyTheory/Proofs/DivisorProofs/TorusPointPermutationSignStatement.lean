import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusPointPermutationSign
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum polydisc defCoord cWt)

attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_point_permutation_sign : ∀ (F : Type) [Field F] [NumberField F] (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ))
    (π : Equiv.Perm (Fin (Module.finrank ℚ F))) (𝔞 𝔟 : FracId F) (z : (F →+* ℝ) → ℂ)
    (X : Obj F (𝔞 * 𝔟⁻¹) (Sp ℂ)) (δ : X.DetOmega),
    IsTorusPoint e 𝔞 𝔟 z X δ → IsTorusPoint (π.trans e) 𝔞 𝔟 z X ((((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℂ) • δ) := by
  first | exact @GlobalTheory.TorusRenumber.isTorusPoint_perm | exact GlobalTheory.TorusRenumber.isTorusPoint_perm | (intros; apply GlobalTheory.TorusRenumber.isTorusPoint_perm <;> assumption)
