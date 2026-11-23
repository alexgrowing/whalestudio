import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC

def PoincareDualityProjectivePoint : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
  [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver p →
  ∀ (d : ℕ) [SmoothOfRelativeDimension d p],
  ∃ (x : Spec (CommRingCat.of k) ⟶ X) (η : Ht q (sch.obj X) (2 * d) d), x ≫ p = 𝟙 _ ∧
    (∀ V : X.Opens, (V : Set X) = (Set.range x)ᶜ → pull _ (sch.map V.ι) _ _ η = 0) ∧
    (∀ t : Ht q (sch.obj X) (2 * d) d, ∃ c : ℕ, t = c • η) ∧
    (addOrderOf η = q → ∀ (n i : ℤ) (a : Ht q (sch.obj X) n i), a ≠ 0 →
      ∃ b : Ht q (sch.obj X) (2 * d - n) (d - i), cup q a b ≠ 0)

def PointClassOrder : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
  [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver p →
  ∀ (d : ℕ) [SmoothOfRelativeDimension d p] (x : Spec (CommRingCat.of k) ⟶ X) (η : Ht q (sch.obj X) (2 * d) d),
    x ≫ p = 𝟙 _ → (∀ V : X.Opens, (V : Set X) = (Set.range x)ᶜ → pull _ (sch.map V.ι) _ _ η = 0) →
    (∀ t : Ht q (sch.obj X) (2 * d) d, ∃ c : ℕ, t = c • η) → addOrderOf η = q

def PoincareDualityProjective : Prop := ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
  [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver p →
  ∀ (d : ℕ) [SmoothOfRelativeDimension d p],
  ∃ tr : Ht q (sch.obj X) (2 * d) d ≃+ ZMod q, ∀ (n i : ℤ) (φ : Ht q (sch.obj X) (2 * d - n) (d - i) →+ ZMod q),
    ∃! a : Ht q (sch.obj X) n i, ∀ b, φ b = tr ((cup q a b).cast (by ring) (by ring))

end GlobalTheory.EtC

end
