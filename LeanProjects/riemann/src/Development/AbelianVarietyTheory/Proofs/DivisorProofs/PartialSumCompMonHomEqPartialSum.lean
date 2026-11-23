import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.PsumMap

theorem psum_comp_hom : ∀ (S : Scheme.{0}) (B B₁ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] (n : ℕ) (p : B ⟶ B₁) (x : Fin n → (T ⟶ B)) (x₁ : Fin n → (T ⟶ B₁)), IsMonHom p → (∀ i, x i ≫ p = x₁ i) → ∀ I : Finset (Fin n), psum B x I ≫ p = psum B₁ x₁ I := by
  intro S B B₁ T _ _ _ _ n p x x₁ hp hx I
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil =>
    show (toUnit T ≫ η[B]) ≫ p = toUnit T ≫ η[B₁]
    rw [Category.assoc, IsMonHom.one_hom]
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    show (lift (x a) _ ≫ μ[B]) ≫ p = lift (x₁ a) _ ≫ μ[B₁]
    rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map, hx a]

end GlobalTheory.MumProd.PsumMap
