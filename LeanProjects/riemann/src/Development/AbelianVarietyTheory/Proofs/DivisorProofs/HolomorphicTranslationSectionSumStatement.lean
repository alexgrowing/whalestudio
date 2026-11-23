import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTranslationSectionSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactUnitPair
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts
open GlobalTheory.CxForm (relCot dRel)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_translation_section_sum : ∀ {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {σ : k →+* ℂ} (A : Over S) [GrpObj A] (g : ℕ)
    (cv : (Fin g → ℂ) → CxPts (A.hom ≫ p) σ) (hcv : ∀ u, (cv 0).1 ≫ A.hom = (cv u).1 ≫ A.hom),
    IsHolTo Set.univ (fun u => (cv u).1) →
    ∀ (W T : A.left.Opens) (hTW : T ≤ W) (F : Γ(A.left, W)), cv 0 ∈ ptsIn (A.hom ≫ p) σ T →
    ∀ (n : ℕ) (α : Fin n → Γ(A.left, T)) (W' : Fin n → (Limits.pullback A.hom A.hom).Opens)
      (hW' : ∀ a, T ≤ Limits.pullback.diagonal A.hom ⁻¹ᵁ W' a) (G : ∀ a, Γ(Limits.pullback A.hom A.hom, W' a)),
    GlobalTheory.Twist.resM (relCot A.hom) hTW (dRel A.hom W F) =
                 ∑ a, α a • GlobalTheory.Conormal.d (Limits.pullback.diagonal_fst A.hom) (hW' a) (G a) →
    fderiv ℂ (fun u => ev (A.hom ≫ p) σ W F (cv u)) 0 =
      ∑ a, ev (A.hom ≫ p) σ T (α a) (cv 0) •
        fderiv ℂ (fun u => ev _ σ (W' a) (G a) (GlobalTheory.RelCotAb.pairPt A (cv 0) (cv u) (hcv u))) 0 := by
  first | exact @GlobalTheory.CurveDer.fderiv_ev_eq_sum | exact GlobalTheory.CurveDer.fderiv_ev_eq_sum | (intros; apply GlobalTheory.CurveDer.fderiv_ev_eq_sum <;> assumption)
