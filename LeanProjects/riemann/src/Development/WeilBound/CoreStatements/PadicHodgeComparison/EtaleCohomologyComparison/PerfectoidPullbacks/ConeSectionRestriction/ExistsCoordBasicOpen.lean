import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ExistsEtaleAwayPf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsIntegralOfSmoothPf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordsOfEtaleBasicOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordDimEqRelativeDimStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isIntegral_of_smooth {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (n : ℕ) [SmoothOfRelativeDimension n q] : IsIntegral X :=
  isIntegral_of_smooth_pf q n

theorem exists_etale_away {K A : Type} [Field K] [CharZero K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] {d : ℕ} (s : Fin d → A) (hs : AlgebraicIndependent K s)
    (halg : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range s)) A) :
    ∃ g : A, g ≠ 0 ∧ (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap A (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g).Etale :=
  exists_etale_away_pf s hs halg

theorem exists_coord_basicOpen {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W)) {d : ℕ} (s : Fin d → Γ(X, W)) :
    letI := (strV q W).toAlgebra
    (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g).Etale →
    ∃ c : Coord q (X.basicOpen g) d, ∀ k, c.t k = resO (X.basicOpen_le g) (s k) :=
  GlobalTheory.T.coords_of_etale_basic_open q hW g s

theorem coord_card_eq {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n q] {V : X.Opens} (hne : (V : Set X).Nonempty) {m : ℕ} (c : Coord q V m) : m = n :=
  GlobalTheory.T.coord_dim_eq_relative_dim q n hne c

theorem exists_frac_basicOpen {X : Scheme.{0}} {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W))
    (hne : (X.basicOpen g : Set X).Nonempty) :
    ∀ r : Γ(X, X.basicOpen g), ∃ b ∈ Set.range (resO (X.basicOpen_le g)), ∃ b' ∈ Set.range (resO (X.basicOpen_le g)),
      b' ≠ 0 ∧ r * b' = b := by
  intro r
  letI := (resO (X.basicOpen_le g)).toAlgebra
  haveI := hW.isLocalization_basicOpen g
  haveI : Nonempty (X.basicOpen g) := hne.to_subtype
  obtain ⟨k, a, hk⟩ := IsLocalization.Away.surj g r
  refine ⟨resO (X.basicOpen_le g) a, ⟨a, rfl⟩, resO (X.basicOpen_le g) (g ^ k), ⟨g ^ k, rfl⟩, ?_, ?_⟩
  · rw [map_pow]
    exact ((IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen g)) g).pow k).ne_zero
  · rw [map_pow]
    exact hk

end CrystallineSemistableComparison.Pb
