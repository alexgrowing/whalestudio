import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage

set_option autoImplicit false

noncomputable section

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

section General

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {n : ℕ}

def combF (dd : Fin n → Fld Z) (c : Fin n → R) : Fld Z :=
  fun W f => ∑ a, constFn s W (c a) * dd a W f

def quadF (dd : Fin n → Fld Z) (M : Matrix (Fin n) (Fin n) R) : Fld Z :=
  fun W f => ∑ a, ∑ b, constFn s W (M a b) * dd a W (dd b W f)

end General

section Raynaud

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {Ω : Type} [CommRing Ω] [StarRing Ω] [Module Ω Q.X]
  {oa : Q.OAct Ω} (Y : Ray oa)

def IsTorField (F : Fld Y.H.left) (ℓ : Q.X → R) : Prop :=
  IsField ⊤ F ∧ (∀ W r, F W (constFn Y.H.hom W r) = 0) ∧
    (∀ (α : Q.X) (W : Y.H.left.Opens), (∃ V : Q.P.A.left.Opens, W = Y.q.left ⁻¹ᵁ V) → ∀ f, IsWt Y α W f →
      F W f = constFn Y.H.hom W (ℓ α) * f) ∧
    ∀ (U : Q.P.A.left.Opens) (g : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens) (k : ℕ) (f : Γ(Y.H.left, W)),
      W ≤ Y.q.left ⁻¹ᵁ U → F W (pbT Y.q.left g W ^ k * f) = pbT Y.q.left g W ^ k * F W f

end Raynaud

end GlobalTheory.HeatMod
