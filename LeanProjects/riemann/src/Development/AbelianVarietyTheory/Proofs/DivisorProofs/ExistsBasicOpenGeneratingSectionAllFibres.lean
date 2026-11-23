import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGenSecNear
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsAtUniformisedTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_basicOpen_genSec_fibres : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB →
    ∀ (g : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), PolFib G L g x →
    ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧
      ∃ θ : SecAt G L (spMap (algebraMap R (Localization.Away r)) ≫ x),
        ∀ (K : Type) [Field K] (i : Localization.Away r →+* K), IsGenSec G L _ (SecAt.pull G L θ i) := by
  intro S G _ L hL g R _ _ x hx p
  obtain ⟨P, α, -, hp, w, hw⟩ := hx
  have hS : SecBaseChangeAnySt := GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny
  obtain ⟨V, hpV, hV⟩ := GlobalTheory.EmbLocal.exists_isGenSec_near hS P p
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := p) (u := ((V : Set (Sp R)) : Set (PrimeSpectrum R))) hpV V.isOpen
  let j := algebraMap R (Localization.Away r)
  have hrange : Set.range (spMap j) ⊆ (V : Set (Sp R)) := by
    intro y hy
    apply hrV
    obtain ⟨z, rfl⟩ := hy
    have hz : PrimeSpectrum.comap j z ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨z, rfl⟩
    exact hz
  obtain ⟨th, hth⟩ := hV (Localization.Away r) (spMap j) hrange
  have hτ : (𝟙 (Sp (Localization.Away r)) : (Over.mk (spMap j)).left ⟶ (Over.mk (spMap j ≫ x)).left) ≫
      (Over.mk (spMap j ≫ x)).hom = (Over.mk (spMap j)).hom ≫ x := Category.id_comp _
  obtain ⟨θ, hθ⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp (T := Over.mk (spMap j)) (T₀ := Over.mk (spMap j ≫ x))
    (𝟙 _) hτ hw hL P.isLB (a := ((1 : ℕ) : ℤ)) th
  refine ⟨r, hpr, θ, fun K _ i => ?_⟩
  have hτ' : (𝟙 (Sp K) : (Over.mk (spMap i ≫ spMap j)).left ⟶ (Over.mk (spMap i ≫ spMap j ≫ x)).left) ≫
      (Over.mk (spMap i ≫ spMap j ≫ x)).hom = (Over.mk (spMap i ≫ spMap j)).hom ≫ x := by
    simp [Category.assoc]
  let ξ : Over.mk (spMap i ≫ spMap j) ⟶ Over.mk (spMap j) := Over.homMk (spMap i) rfl
  let ξ₀ : Over.mk (spMap i ≫ spMap j ≫ x) ⟶ Over.mk (spMap j ≫ x) := Over.homMk (spMap i) rfl
  have hξ : (𝟙 (Sp K) : (Over.mk (spMap i ≫ spMap j)).left ⟶ (Over.mk (spMap i ≫ spMap j ≫ x)).left) ≫ ξ₀.left =
      ξ.left ≫ (𝟙 (Sp (Localization.Away r)) : (Over.mk (spMap j)).left ⟶ (Over.mk (spMap j ≫ x)).left) :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hrel : GlobalTheory.ThetaPtMove.SecRel hp _ hτ' w (VVRank.pullS P.A ((1 : ℕ) : ℤ) ξ th)
      (VVRank.pullS G ((1 : ℕ) : ℤ) ξ₀ θ) :=
    GlobalTheory.Ex.OneGen.SecRel.pullS hp _ hτ hθ (T' := Over.mk (spMap i ≫ spMap j))
      (T₀' := Over.mk (spMap i ≫ spMap j ≫ x)) _ hτ' ξ ξ₀ hξ
  have : IsAffine (Over.mk (spMap j)).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap i ≫ spMap j)).left := inferInstanceAs (IsAffine (Spec _))
  have hg : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 ξ th) :=
    GlobalTheory.EmbPull.isGenSec_pullS P hS ξ hth
  have hg' : IsGenSec P.A P.L ((1 : ℕ) : ℤ) (VVRank.pullS P.A ((1 : ℕ) : ℤ) ξ th) := hg
  have : IsIso (C := Scheme.{0}) (X := (Over.mk (spMap i ≫ spMap j)).left)
      (Y := (Over.mk (spMap i ≫ spMap j ≫ x)).left) (𝟙 (Sp K)) := IsIso.id _
  have h2 : IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G ((1 : ℕ) : ℤ) ξ₀ θ) :=
    GlobalTheory.ThetaPtUp.isGenSec_up hp _ hτ' hw hL P.isLB hrel hg'
  exact h2

end GlobalTheory.UMin
