import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeSubsetAbelianLocusOfLevelTrait
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_subset_abelianLocus_of_levelTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (o Ω : Type) [CommRing o] [Field Ω]
    [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X),
    SysAt F W β S ρ u → ∀ (Y M : RatModel o Ω) (q : Y.Z ⟶ F.X) (U₀ : M.Z.Opens) (EE : M.Lat S.J)
    (Zh : ZHOut ρ M U₀ EE), LevAt F β u Y q → S.Over₀ M U₀ →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ξ : Sp V ⟶ M.Z) (τ : Sp V ⟶ Y.Z)
      (κ : Ω →+* FractionRing V), spMap (algebraMap V (FractionRing V)) ≫ ξ = spMap κ ≫ M.pt →
      spMap (algebraMap V (FractionRing V)) ≫ τ = spMap κ ≫ Y.pt → Set.range ξ ⊆ abLocus Zh.G := by
  first | exact @GlobalTheory.SiegTh.range_subset_abLocus_of_levelTrait | exact GlobalTheory.SiegTh.range_subset_abLocus_of_levelTrait | (intros; apply GlobalTheory.SiegTh.range_subset_abLocus_of_levelTrait <;> assumption)
