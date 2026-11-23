import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulOfScaledSectionValues
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_of_scaled_section_values : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (L : LB Y), L.IsLB → ∀ (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)) (k l : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g l s' → GlobalTheory.HeatSym.VS φ L x g (k + l) (s * s') := by
  first | exact @GlobalTheory.HeatSym.VS.mul | exact GlobalTheory.HeatSym.VS.mul | (intros; apply GlobalTheory.HeatSym.VS.mul <;> assumption)
