import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCorrespondencePolynomial
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_correspondence_polynomial : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A']
    (b : Sp R' ⟶ Sp R) (φ : A'.left ⟶ A.left) (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ b φ) (f : A ⟶ A) (f' : A' ⟶ A')
    [IsMonHom f] [IsMonHom f'], φ ≫ f.left = f'.left ≫ φ → ∀ (x : HdR A) (x' : HdR A'), m.Corr x x' →
    ∀ Q : Polynomial R, m.Corr (Polynomial.aeval (push (dp0 R) (𝟙 _) f) Q x) (Polynomial.aeval (push (dp0 R') (𝟙 _) f') (Q.map σ) x') := by
  first | exact @GlobalTheory.DeRham.corr_aeval_push | exact GlobalTheory.DeRham.corr_aeval_push | (intros; apply GlobalTheory.DeRham.corr_aeval_push <;> assumption)
