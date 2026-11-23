import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChernClassOnFlagPairStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagComparisonStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_ck_flag_sum

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

theorem psumExpansion_eq_rename (N k : ℕ) (i : Fin N) :
    psumExpansion N k i =
      rename (Sum.map (fun _ : Fin 1 => i) (fun _ : Fin 1 => i)) (psumExpansion 1 k 0) := by
  simp [psumExpansion]

theorem pairNum_psum {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {N : ℕ} (P : Ideal (MRing ι O)) (x x' : Fin N → K → ℤ)
    (f g : Fin N → MRing ι O) (k : ℕ) (Q : List (K → ℤ)) :
    pairNum P x x' f g (psumExpansion N k) Q =
      ∑ i, pairNum P (fun _ : Fin 1 => x i) (fun _ => x' i) (fun _ => f i) (fun _ => g i)
        (psumExpansion 1 k) Q := by
  unfold pairNum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_one]
  have he : Function.Injective (Sum.map (fun _ : Fin 1 => i) (fun _ : Fin 1 => i)) :=
    Sum.map_injective.mpr ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  have hc : Sum.elim x x' ∘ Sum.map (fun _ : Fin 1 => i) (fun _ : Fin 1 => i) =
      Sum.elim (fun _ : Fin 1 => x i) (fun _ : Fin 1 => x' i) := by
    funext s
    rcases s with s | s <;> rfl
  simp only [psumExpansion_eq_rename N k i, classNum_rename _ _ he, hc]

end PositivityTheory.Xgn.A_ck_flag_sum
