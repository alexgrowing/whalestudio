import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PwIsoIsGen
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyPBScale

theorem appLE_constFn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {X Y : Scheme.{0}} {φ : Y ⟶ X}
    (p : X ⟶ Sp R) (p' : Y ⟶ Sp R') (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U)
    (a : R) : (φ.appLE U V h).hom (constFn p U a) = constFn p' V (f a) :=
  KeyVia.appLE_cst f p p' hφ h a

theorem resG_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (h : V ≤ U) (a : R) : resG X h (constFn p U a) = constFn p V a :=
  KeyVia.res_appLE (φ := p) (U := ⊤) (fun _ _ => trivial) h _

theorem lie_baseChange {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {G : Over (Sp R)} [GrpObj G]
    {G' : Over (Sp R')} [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) {n m : ℕ}
    (e : m = n) (M : Matrix (Fin n) (Fin n) R) (v v' : Fin n → (epsR R ⟶ G)) (u u' : Fin m → (epsR R' ⟶ G'))
    (hv : ∀ i, IsLieComb (M i) v (v' i))
    (hu : ∀ i : Fin m, IsLieComb (fun j : Fin m => f (M (i.cast e) (j.cast e))) u (u' i))
    (huv : ∀ i, (u i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v (i.cast e)).left) (i : Fin m) :
    (u' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (v' (i.cast e)).left := by
  subst e
  exact (lieComb_baseChange R R' f G G' φ h m v (v' i) (M i) u (u' i) huv (hv i)).2 (hu i)

theorem keyPB_scale : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (P : Out.PolAV (Sp R)) (hg rig hr th hth v hv th' hth' v' hv') (a : R) (M : Matrix (Fin P.g) (Fin P.g) R) (Q : Out.PolAV (Sp R')) (e : Q.g = P.g) (hgQ rigQ hrQ s hs u hu s' hs' u' hu'), (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) → (∀ i, IsLieComb (M i) v (v' i)) → (∀ i, LB.Sec.f s' i = constFn Q.A.hom _ (f a) * LB.Sec.f s i) → (∀ i : Fin Q.g, IsLieComb (fun j : Fin Q.g => f (M (i.cast e) (j.cast e))) u (u' i)) → KeyPB (⟨Q, hgQ, rigQ, hrQ, s, hs, u, hu⟩ : KeyIn R') (⟨P, hg, rig, hr, th, hth, v, hv⟩ : KeyIn R) f → KeyPB (⟨Q, hgQ, rigQ, hrQ, s', hs', u', hu'⟩ : KeyIn R') (⟨P, hg, rig, hr, th', hth', v', hv'⟩ : KeyIn R) f := by
  intro R R' _ _ f P hg rig hr th hth v hv th' hth' v' hv' a M Q e hgQ rigQ hrQ s hs u hu s' hs' u' hu' h₁ h₂ h₃ h₄
  rintro ⟨φ, he, w, hg', F, hp, hw, hrig, hsec, hF, hε, hlie⟩
  have hF' : F = Chart.dualMapR f := KeyCancel.dualNumber_ringHom_ext
    (fun b => (hF b).trans (by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]))
    (hε.trans (by ext <;> simp [Chart.dualMapR]))
  refine ⟨φ, he, w, hg', F, hp, hw, hrig, fun j i h => ?_, hF, hε, ?_⟩
  · have k := hsec j i h
    dsimp only at k ⊢
    rw [h₁, h₃, map_mul, map_mul, k, appLE_constFn f P.A.hom Q.A.hom hp.1.w, resG_constFn]
    exact mul_left_comm (G := Γ(Q.A.left, (P.L.pull φ).U j ⊓ Q.L.U i)) _ _ _
  · subst hF'
    exact lie_baseChange f hp e M v v' u u' h₂ h₄ hlie

end GlobalTheory.KeyPBScale
end
