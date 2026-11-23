import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePullbackOfRaynaudTorusWeightZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.WtPres

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa}

theorem isWt_div {α : Q.X} {V : Y.H.left.Opens} {f u u' : Γ(Y.H.left, V)} (hf : IsWt Y α V f) (hu : IsWt Y α V u)
    (h : u * u' = 1) : IsWt Y 0 V (f * u') := by
  intro S _ φ x x' c a a' ha ha' hV hV' hq hc
  have e : ∀ b : Sp S ⟶ Y.H.left, ⊤ ≤ b ⁻¹ᵁ V → valR b V u * valR b V u' = 1 := fun b hb => by
    rw [← WtAlg.valR_mul'' _ _ hb, h, WtAlg.valR_eq' _ _ hb, map_one, map_one]
  have e₁ := e a hV
  have e₂ := e a' hV'
  rw [hu S φ x x' c a a' ha ha' hV hV' hq hc] at e₂
  rw [WtAlg.valR_mul'' _ _ hV', WtAlg.valR_mul'' _ _ hV, hf S φ x x' c a a' ha ha' hV hV' hq hc,
    WtAlg.c_zero x x' c hc, Units.val_one, _root_.one_mul]
  linear_combination valR a V f * valR a V u' * e₂ - c α * valR a V f * valR a' V u' * e₁

end GlobalTheory.Heat.WtPres
