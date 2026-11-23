import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem DeRham.corr_aeval_push : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A']
    (b : Sp R' ⟶ Sp R) (φ : A'.left ⟶ A.left) (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ b φ) (f : A ⟶ A) (f' : A' ⟶ A')
    [IsMonHom f] [IsMonHom f'], φ ≫ f.left = f'.left ≫ φ → ∀ (x : HdR A) (x' : HdR A'), m.Corr x x' →
    ∀ Q : Polynomial R, m.Corr (Polynomial.aeval (push (dp0 R) (𝟙 _) f) Q x) (Polynomial.aeval (push (dp0 R') (𝟙 _) f') (Q.map σ) x') := by
  intro R R' _ _ σ A _ A' _ b φ m f f' _ _ e
  have hT : ∀ (x : HdR A) (x' : HdR A'), m.Corr x x' →
      m.Corr (push (dp0 R) (𝟙 _) f x) (push (dp0 R') (𝟙 _) f' x') :=
    fun x x' h ↦ GrpMor.Corr.push (m := m) m f f' e h
  intro x x' hx Q
  revert x x'
  refine Polynomial.induction_on Q ?_ ?_ ?_
  · intro a x x' hx c
    simp only [Polynomial.aeval_C, Polynomial.map_C, Module.algebraMap_end_apply,
      LinearMap.smul_apply, smul_eq_mul, hx c, map_mul]
  · intro p q hp hq x x' hx c
    simp only [Polynomial.map_add, map_add, LinearMap.add_apply, hp x x' hx c, hq x x' hx c]
  · intro n a ih x x' hx
    have h := ih _ _ (hT x x' hx)
    rw [_root_.pow_succ, ← _root_.mul_assoc, Polynomial.map_mul, Polynomial.map_X]
    simp only [map_mul, Polynomial.aeval_X, Module.End.mul_apply] at h ⊢
    exact h

end GlobalTheory
