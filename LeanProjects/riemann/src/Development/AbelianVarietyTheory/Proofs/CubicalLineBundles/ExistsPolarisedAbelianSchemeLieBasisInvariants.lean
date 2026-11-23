import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsUnimodularSolZeroNeg
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPeriodPairOfLatticeInLine
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConstOfSqMulTendstoZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjPolarised
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsWeierstrassCoordinatesOnLineStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

noncomputable section

namespace GlobalTheory.WeierstrassCurve

theorem fibre_over_scheme {R R' : Type} [CommRing R] [CommRing R'] (W : WeierstrassCurve R) (f : R →+* R')
    {A : Over (Sp R)} {A' : Over (Sp R')} [GrpObj A] [GrpObj A'] {ψ : A.left ⟶ scheme W} [IsIso ψ]
    (hψ : ψ ≫ toSpec W = A.hom) (he : eSec A ≫ ψ = zero W) {v : epsR R ⟶ A}
    {h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0]}
    (hv : v.left ≫ ψ = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h)
    {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A (spMap f) φ) {v' : epsR R' ⟶ A'} (hv' : IsVecOver f φ v v') :
    ∃ h' : IsUnimodularSol (W.map ((algebraMap R' (DualNumber R')).comp f)) ![DualNumber.eps, -1, 0],
      IsPullback (φ ≫ ψ) A'.hom (toSpec W) (spMap f) ∧ eSec A' ≫ φ ≫ ψ = spMap f ≫ zero W ∧
      v'.left ≫ φ ≫ ψ = ptHom W ((algebraMap R' (DualNumber R')).comp f) ![DualNumber.eps, -1, 0] h' := by
  have hρ : (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have hP : (Chart.dualMapR f ∘ ![DualNumber.eps, -1, 0]) = ![DualNumber.eps, -1, 0] := by
    ext1 j; fin_cases j
    · ext <;> simp [Chart.dualMapR]
    · simp
    · simp
  have h₁ := h.map_comp (Chart.dualMapR f)
  rw [hρ, hP] at h₁
  refine ⟨h₁, ?_, ?_, ?_⟩
  · exact hφ.1.of_iso (Iso.refl _) (asIso ψ) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp [hψ]) (by simp)
  · rw [← Category.assoc, PolBaseChange.eSec_comm hφ, Category.assoc, he]
  · rw [← Category.assoc, hv', Category.assoc, hv]
    exact (SpecMap_ptHom W _ _ h _).trans (ptHom_congr W _ _ _ hρ hP _)

theorem exists_polAV_invariants : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ → ∃ (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A), P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ (∀ (s' : R →+* ℂ) (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∃ L : PeriodPair, (∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) ∧ s' W.c₄ = 12 * L.g₂ ∧ s' W.c₆ = 216 * L.g₃ ∧ s' W.Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  intro R _ W hΔ
  obtain ⟨P, ψ, v, hg, hiso, hψ, he, ⟨h, hv⟩, hb⟩ := GlobalTheory.WeierstrassCurve.exists_polAV R W hΔ
  refine ⟨P, v, hg, hb, fun R' _ f P' φ v' hP hv' => ?_, fun s P' φ v' u w hP hv' hd => ?_⟩
  · obtain ⟨h', h1, h2, h3⟩ := fibre_over_scheme W f hψ he hv hP.2.1 hv'
    exact OriginTangent.isLieBasis_eps R W R' f P'.A (φ ≫ ψ) v' h' h1 h2 h3
  · obtain ⟨h', h1, h2, h3⟩ := fibre_over_scheme W s hψ he hv hP.2.1 hv'
    obtain ⟨hw, x, y, t, hx, hy, hper, heq, ht, ht0, ht1, hty, hlim⟩ :=
      GlobalTheory.T.exists_weierstrass_coordinates_on_line R W s P'.A (φ ≫ ψ) v' h' h1 h2 h3 P'.L P'.g u w hd
    obtain ⟨L, hL⟩ := GlobalTheory.exists_periodPair_of_lattice_in_line P'.g u.Λ w (hP.1.trans hg) hw u.discrete u.full
    have hset : (L.lattice : Set ℂ) = {z | z • w ∈ u.Λ} := Set.ext hL
    have key := GlobalTheory.invariants_eq_of_periodic_solution L (W.map s) x y t 1 one_ne_zero (hset ▸ hx) (hset ▸ hy)
      (fun l hl => hper l ((hL l).1 hl)) (fun z hz => heq z fun e => hz ((hL z).2 e)) ht ht0 ht1 hty hlim
    simp only [one_pow, _root_.one_mul, WeierstrassCurve.map_c₄, WeierstrassCurve.map_c₆, WeierstrassCurve.map_Δ] at key
    exact ⟨hw, L, hL, key⟩

end GlobalTheory.WeierstrassCurve
