import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeFaceOfInteriorCommonPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryEqReflOfCongrModGeThree
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.eq_self_of_cone_congMod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)) (q : ℕ), IsPolFan H.bar q φ → NoSelfInt H.bar q φ → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Finite (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ δ → (∀ y, y ≠ 0 → 0 < ∑ i, δ i y y) → ∀ (u : X ≃ₗ[𝓞 E] X) (a a' : Fin m → ℕ), (∀ i, 0 < a i) → (∀ i, 0 < a' i) → (∀ y z, ∑ i, (a i : ℤ) * δ i (u y) (u z) = ∑ i, (a' i : ℤ) * δ i y z) → ∀ N : ℕ, 3 ≤ N → (∀ y, ∃ z, u y = y + N • z) → ∀ y, u y = y := by
  intro E _ _ _ H φ q hfan hno X _ _ _ _ _ hX m δ hδ hdef u a a' ha ha' hsum N hN hcong
  haveI : Module.Projective (𝓞 E) X := GlobalTheory.Forms.projective_of_int (𝓞 E) X
  have hon : IsPolFanOn H.bar φ X := hfan X hX
  have hu : IsCone H.bar φ fun i => pull u.toLinearMap (δ i) := hδ.pull_equiv u
  have heq : ∑ j, a j • pull u.toLinearMap (δ j) = ∑ j, a' j • δ j := LinearMap.ext₂ fun y z => by
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using hsum y z
  have hfix : ∀ j, pull u.toLinearMap (δ j) = δ j := by
    intro j
    obtain ⟨j', hj'⟩ := GlobalTheory.Poinc.intCone_face (𝓞 E) H.bar φ X hon _ _ _ δ hu hδ a a' ha heq j
    obtain rfl := hno X hX m δ hδ u j j' hj'
    exact hj'
  have hβ : ∀ y z, (∑ i, δ i) (u y) (u z) = (∑ i, δ i) y z := fun y z => by
    simp only [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun₂ (hfix i) y z
  have he := GlobalTheory.Poinc.eq_refl_of_isometry_congMod X (∑ i, δ i)
    (fun y hy => by simpa [LinearMap.sum_apply] using hdef y hy) (u.restrictScalars ℤ) (fun y z => hβ y z) N hN
    (fun y => hcong y)
  intro y
  exact LinearEquiv.congr_fun he y
