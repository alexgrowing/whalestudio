import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TowerRedToBaseIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.SerreTate
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory

open scoped TensorProduct

namespace GlobalTheory.RedQuot

open WithConv Coalgebra Bialgebra

theorem semi_mulBy {R R₀ A A' : Type} [CommRing R] [CommRing R₀] [CommRing A] [CommRing A'] [Bialgebra R A]
    [Bialgebra R₀ A'] [IsCocomm R A] [IsCocomm R₀ A'] {σ : R →+* R₀} (f : SemiBialgHom σ A A') (k : ℕ) (a : A) :
    f (mulBy R A k a) = mulBy R₀ A' k (f a) := by
  letI : Algebra R A' := ((algebraMap R₀ A').comp σ).toAlgebra
  have hB : ∀ r, algebraMap R A' r = algebraMap R₀ A' (σ r) := fun _ => rfl
  have h := map_pow (f.pts A' hB) (toConv (AlgHom.id R₀ A')) k
  have e1 : ((f.pts A' hB) (toConv (AlgHom.id R₀ A') ^ k)).ofConv a = mulBy R₀ A' k (f a) := by
    rw [SemiBialgHom.pts_apply, ← comp_mulBy_pts]; rfl
  have e2 : ((f.pts A' hB (toConv (AlgHom.id R₀ A'))) ^ k).ofConv a = f (mulBy R A k a) := by
    rw [← toConv_ofConv (f.pts A' hB (toConv (AlgHom.id R₀ A'))), ← comp_mulBy_pts]; rfl
  rw [← e1, ← e2, h]

theorem smul_pow_app {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (G : PDivGroup p O) (k n : ℕ) (a : G.A n) :
    Hom.app (((p : ℤ_[p]) ^ k) • 𝟙 G) n a = mulBy O (G.A n) (p ^ k) a := by
  rw [← Nat.cast_pow, natCast_smul_id_app]

theorem ident {p : ℕ} [Fact p.Prime] {R R₀ : Type} [CommRing R] [CommRing R₀] [Algebra R R₀]
    {G' G : PDivGroup p R} {G₀ : PDivGroup p R₀} (s : SemiHom (algebraMap R R₀) G₀ G)
    (s' : SemiHom (algebraMap R R₀) G₀ G') (ψ : G ⟶ G') (χ : G' ⟶ G) (m N : ℕ)
    (h1 : ∀ n a, s.app n (ψ.app n a) = s'.app n (Hom.app (((p : ℤ_[p]) ^ m) • 𝟙 G') n a))
    (h2 : ψ ≫ χ = ((p : ℤ_[p]) ^ N) • 𝟙 G) (n : ℕ) (a : G.A n) :
    s.app n (mulBy R (G.A n) (p ^ N) a) = mulBy R₀ (G₀.A n) (p ^ m) (s'.app n (χ.app n a)) := by
  have e2 : Hom.app (ψ ≫ χ) n a = mulBy R (G.A n) (p ^ N) a := by rw [h2, smul_pow_app]
  rw [← e2, comp_app]
  change s.app n (ψ.app n (χ.app n a)) = _
  rw [h1, smul_pow_app]
  exact semi_mulBy (s'.app n) _ _

end GlobalTheory.RedQuot
