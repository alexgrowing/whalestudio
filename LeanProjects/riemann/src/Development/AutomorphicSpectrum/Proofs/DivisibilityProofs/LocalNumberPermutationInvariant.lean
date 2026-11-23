import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsCompactUnitaryPointsAtPlaceFstMemCompact
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num.RootPerm

theorem classList_mapDomain {K σ τ : Type} (cls : τ → K → ℤ) (e : σ → τ) (μ : σ →₀ ℕ) :
    classList cls (Finsupp.mapDomain e μ) = classList (cls ∘ e) μ := by
  unfold classList
  rw [← Finsupp.toMultiset_map, Multiset.map_map]

theorem classNum_rename {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ τ : Type} (cls : τ → K → ℤ) (e : σ → τ) (he : Function.Injective e)
    (H : MvPolynomial σ ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (rename e H) Q W = classNum (cls ∘ e) H Q W := by
  classical
  unfold classNum
  rw [support_rename_of_injective he,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective he h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_rename_mapDomain e he, classList_mapDomain]

theorem rename_psumExpansion {r : ℕ} (e : Equiv.Perm (Fin r)) (k : ℕ) (i : Fin r) :
    rename (Sum.map e e) (psumExpansion r k i) = psumExpansion r k (e i) := by
  simp [psumExpansion, map_sum, rename_X]

theorem root_perm : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (r : ℕ) (e : Equiv.Perm (Fin r)) (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)), (∀ (a : O) (x : Fin r → K → ℤ), laNum P a (x ∘ e) k Q = laNum P a x k Q) ∧ ∀ T : LocPair ι O (Fin r), (T.comp e).ck P k Q = T.ck P k Q := by
  intro O _ _ _ K _ _ ι _ r e P k Q
  refine ⟨fun a x => ?_, fun T => ?_⟩
  · have h : ∀ W : Ideal (MRing ι O), classNum (x ∘ e) (psum (Fin r) ℤ (k - 1)) Q W =
        classNum x (psum (Fin r) ℤ (k - 1)) Q W := fun W => by
      rw [← classNum_rename x e e.injective, rename_psum]
    simp only [laNum, h]
  · have h : ∀ (i : Fin r) (W : Ideal (MRing ι O)),
        classNum (Sum.elim (T.x ∘ e) (T.x' ∘ e)) (psumExpansion r k i) Q W =
          classNum (Sum.elim T.x T.x') (psumExpansion r k (e i)) Q W := fun i W => by
      have hc : Sum.elim T.x T.x' ∘ Sum.map e e = Sum.elim (T.x ∘ e) (T.x' ∘ e) := by
        funext s
        rcases s with s | s <;> rfl
      rw [← rename_psumExpansion, classNum_rename _ _ (Sum.map_injective.mpr ⟨e.injective, e.injective⟩), hc]
    simp only [LocPair.ck, pairNum, LocPair.comp, Function.comp_apply, h]
    exact Equiv.sum_comp e fun j => cycEval (fun W => classNum (Sum.elim T.x T.x') (psumExpansion r k j) Q W)
      (ratDiv P (T.f j) (T.g j))

end GlobalTheory.CompanionTheory.Ar.Num.RootPerm
