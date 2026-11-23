import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatSym

def VS {R Ω : Type} [CommRing R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (L : LB Y) (x : Sp Ω ⟶ Y)
    (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)) (k : ℕ) (s : FractionRing Ω) : Prop :=
  ∃ (r : R) (σ : SecM (𝟙 Y) L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) L x g k σ ω ∧
    (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * s

theorem VS.half {R Ω : Type} [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing Ω] (φ : R →+* Ω) {Y : Scheme.{0}}
    {L : LB Y} {x : Sp Ω ⟶ Y} {g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)} {k : ℕ} {s : FractionRing Ω}
    (h : VS φ L x g k (2 * s)) : VS φ L x g k s := by
  haveI : CharZero R := algebraRat.charZero R
  obtain ⟨r, σ, ω, hr, hv, he⟩ := h
  refine ⟨2 * r, σ, ω, mul_ne_zero two_ne_zero hr, hv, ?_⟩
  rw [he, map_mul, map_mul, map_ofNat, map_ofNat]
  ring

theorem ringOp_sub {Ω : Type} [CommRing Ω] {n : ℕ} (d₁ d₂ : Ω → Ω) (dd : Fin n → Ω → Ω)
    (Θ₁ Θ₂ : Matrix (Fin n) (Fin n) Ω) (u₁ u₂ : Fin n → Ω) (p₁ p₁' p₂ p₂' : Ω) (k : ℕ) (f : Ω) :
    ringOp d₁ dd Θ₁ u₁ p₁ p₁' k f - ringOp d₂ dd Θ₂ u₂ p₂ p₂' k f =
      ringOp (fun y => d₁ y - d₂ y) dd (Θ₁ - Θ₂) (u₁ - u₂) (p₁ - p₂) (p₁' - p₂') k f := by
  simp only [ringOp, Matrix.sub_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

theorem bracket {Ω : Type} [CommRing Ω] {n : ℕ} (d : Ω → Ω) (dd : Fin n → Ω → Ω)
    (hd : ∀ x y, d (x * y) = x * d y + y * d x) (hl : ∀ a x y, dd a (x * y) = x * dd a y + y * dd a x)
    (ha : ∀ a x y, dd a (x + y) = dd a x + dd a y)
    (Θ : Matrix (Fin n) (Fin n) Ω) (hΘ : Θᵀ = Θ) (u : Fin n → Ω) (p p' : Ω) (k : ℕ) (b c : Ω) :
    b * (ringOp d dd Θ u p p' (k + k) (b * c) - b * ringOp d dd Θ u p p' k c -
        c * ringOp d dd Θ u p p' k b) -
      c * (ringOp d dd Θ u p p' (k + k) (b * b) - b * ringOp d dd Θ u p p' k b -
        b * ringOp d dd Θ u p p' k b) =
      2 * ((k : Ω) * b * (b * d c - c * d b) - ∑ a, ∑ e, Θ a e * dd a b * (b * dd e c - c * dd e b)) := by
  have sym : ∀ a e, Θ e a = Θ a e := fun a e => by
    have := congrFun (congrFun hΘ a) e
    simpa [Matrix.transpose_apply] using this
  have swap : ∑ a, ∑ e, Θ a e * (dd a c * dd e b) = ∑ a, ∑ e, Θ a e * (dd a b * dd e c) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [sym]; ring
  have s2 : ∀ f h : Ω, ∑ a, ∑ e, Θ a e * dd a (dd e (f * h)) =
      f * ∑ a, ∑ e, Θ a e * dd a (dd e h) + h * ∑ a, ∑ e, Θ a e * dd a (dd e f) +
        (∑ a, ∑ e, Θ a e * (dd a f * dd e h) + ∑ a, ∑ e, Θ a e * (dd a h * dd e f)) := by
    intro f h
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [hl, ha, hl, hl]
    ring
  have s1 : ∀ f h : Ω, ∑ a, u a * dd a (f * h) = f * ∑ a, u a * dd a h + h * ∑ a, u a * dd a f := by
    intro f h
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hl]
    ring
  have swap' : ∑ a, ∑ e, Θ a e * (dd a b * dd e c) - ∑ a, ∑ e, Θ a e * (dd a c * dd e b) = 0 := by
    rw [swap]; ring
  have t1 : ∑ a, ∑ e, Θ a e * dd a b * (b * dd e c - c * dd e b) =
      b * ∑ a, ∑ e, Θ a e * (dd a b * dd e c) - c * ∑ a, ∑ e, Θ a e * (dd a b * dd e b) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  simp only [ringOp]
  rw [s2, s2, s1, s1, t1, hd, hd]
  push_cast
  linear_combination b * swap'

end GlobalTheory.HeatSym
