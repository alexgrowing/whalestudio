import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorFieldZero

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatMod

theorem valR_sub_const_mul {R S : Type} [CommRing R] [CommRing S] {X : Scheme.{0}} (p : X ⟶ Sp R) (φ : R →+* S)
    (x : Sp S ⟶ X) (hx : x ≫ p = spMap φ) (W : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (f g : Γ(X, W)) (r : R) :
    valR x W (f - constFn p W r * g) = valR x W f - φ r * valR x W g := by
  have hc : valR x W (constFn p W r) = φ r := GlobalTheory.Points.valR_constFn_of_over p φ x hx W h r
  rw [← hc]
  unfold valR
  simp only [dif_pos h, map_sub, map_mul]

theorem isWt_sub_const_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (Ω : Type) [CommRing Ω] [StarRing Ω] [Module Ω Q.X] (oa : Q.OAct Ω) (Y : Ray oa), ∀ (α : Q.X) (W : Y.H.left.Opens) (f g : Γ(Y.H.left, W)) (r : R), IsWt Y α W f → IsWt Y α W g → IsWt Y α W (f - constFn Y.H.hom W r * g) := by
  intro R _ _ Q Ω _ _ _ oa Y α W f g r hf hg S _ φ x x' c a a' ha ha' hW hW' hq hc
  have h1 := hf S φ x x' c a a' ha ha' hW hW' hq hc
  have h2 := hg S φ x x' c a a' ha ha' hW hW' hq hc
  have e : a ≫ Y.H.hom = spMap φ := by rw [ha]; exact Over.w x
  have e' : a' ≫ Y.H.hom = spMap φ := by rw [ha']; exact Over.w x'
  rw [valR_sub_const_mul _ φ a e W hW, valR_sub_const_mul _ φ a' e' W hW', h1, h2]
  ring

end GlobalTheory.HeatMod
