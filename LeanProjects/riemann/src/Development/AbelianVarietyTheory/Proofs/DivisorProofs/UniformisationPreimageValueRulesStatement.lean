import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRules
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_preimage_value_rules : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), (∀ U, IsOpen (pre u.ex U)) ∧ (∀ U b, DifferentiableOn ℂ (val u.ex U b) (pre u.ex U)) ∧ (∀ U (l : u.Λ) (z : Fin g → ℂ), z + l ∈ pre u.ex U ↔ z ∈ pre u.ex U) ∧ (∀ U b (l : u.Λ) (z : Fin g → ℂ), val u.ex U b (z + l) = val u.ex U b z) ∧ (∀ U V, pre u.ex (U ⊓ V) = pre u.ex U ∩ pre u.ex V) ∧ (∀ U V, V ≤ U → pre u.ex V ⊆ pre u.ex U) ∧ (∀ (K : Type) (W : K → A.left.Opens) z, z ∈ pre u.ex (⨆ i, W i) ↔ ∃ i, z ∈ pre u.ex (W i)) ∧ (∀ U z, z ∈ pre u.ex U → ∃ W : A.left.affineOpens, W.1 ≤ U ∧ z ∈ pre u.ex W.1) ∧ (∀ U V (h : V ≤ U) (b : Sec (str A) U), ∀ z ∈ pre u.ex V, val u.ex V (Sec.res (str A) h b) z = val u.ex U b z) ∧ (∀ U, ∀ z ∈ pre u.ex U, ∃ e : Sec (str A) U →ₐ[ℂ] ℂ, ∀ b, val u.ex U b z = e b) ∧ (∀ U b z, z ∈ pre u.ex (A.left.basicOpen b) ↔ val u.ex U b z ≠ 0) ∧ ∀ z, z ∈ pre u.ex ⊤ := by
  first | exact @GlobalTheory.CechPer.pre_val_rules | exact GlobalTheory.CechPer.pre_val_rules | (intros; apply GlobalTheory.CechPer.pre_val_rules <;> assumption)
