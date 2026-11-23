import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem curve_lattice_baseChange : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair) (R₁ : Type) [CommRing R₁] (f : R →+* R₁) (P₁ : Out.PolAV (Sp R₁)) (φ : P₁.A.left ⟶ P.A.left) (v₁ : epsR R₁ ⟶ P₁.A), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) → IsPolFibre f P P₁ φ → IsVecOver f φ v v₁ → (P₁.g = 1 ∧ IsLieBasis ![v₁] ∧ (∀ (R' : Type) [CommRing R'] (f' : R₁ →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P₁.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P₁ P' φ' → IsVecOver f' φ' v₁ v' → IsLieBasis ![v']) ∧ ∀ s' : R₁ →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P₁.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P₁ P' φ' → IsVecOver s' φ' v₁ v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ ((fun s : R₁ →+* ℂ => Lf (s.comp f)) s').lattice ↔ z • w' ∈ u'.Λ)) := by
  intro R _ P v Lf R₁ _ f P₁ φ v₁ ⟨hg, _, hfib, hlat⟩ hP₁ hv₁

  have up : ∀ (R' : Type) [CommRing R'] (f' : R₁ →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P₁.A.left)
      (v' : epsR R' ⟶ P'.A), IsPolFibre f' P₁ P' φ' → IsVecOver f' φ' v₁ v' →
      IsPolFibre (f'.comp f) P P' (φ' ≫ φ) ∧ IsVecOver (f'.comp f) (φ' ≫ φ) v v' := by
    intro R' _ f' P' φ' v' hP' hv'
    exact ⟨PolFibre.comp hP₁ hP', (PolFibre.vec_iff hP₁.2.1.1 hP'.2.1.1.w hv₁).1 hv'⟩
  refine ⟨hP₁.1.trans hg, hfib R₁ f P₁ φ v₁ hP₁ hv₁, ?_, ?_⟩
  · intro R' _ f' P' φ' v' hP' hv'
    obtain ⟨h₁, h₂⟩ := up R' f' P' φ' v' hP' hv'
    exact hfib R' (f'.comp f) P' (φ' ≫ φ) v' h₁ h₂
  · intro s' P' φ' v' u' w' hP' hv' hd
    obtain ⟨h₁, h₂⟩ := up ℂ s' P' φ' v' hP' hv'
    exact hlat (s'.comp f) P' (φ' ≫ φ) v' u' w' h₁ h₂ hd

end GlobalTheory
