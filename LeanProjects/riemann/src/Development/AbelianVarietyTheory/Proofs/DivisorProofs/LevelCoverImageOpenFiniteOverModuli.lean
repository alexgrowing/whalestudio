import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveFunctionFieldModelHomOfProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrCentredPointGenericBothModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeSubsetAbelianLocusOfLevelTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenFiniteOntoOfLevelCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OpenLev

theorem exists_open_finite : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (Y X M : RatModel o Ω) (q : Y.Z ⟶ F.X) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (fM : M.Z ⟶ X.Z) (Xab : X.Z.Opens) (Zh : ZHOut ρ M U₀ EE) (d : Y.Z ⟶ X.Z), LevAt F β u Y q → MinorAt S X M U₀ EE fM Xab → (abLocus Zh.G : Set M.Z) = fM ⁻¹' (Xab : Set X.Z) → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d → ∃ (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), OpenAt F β u M U c ∧ (U : Set M.Z) ⊆ abLocus Zh.G := by
  intro g n _ _ _ F W _ o Ω _ _ _ _ β S ρ u hsys Y X M q U₀ EE fM Xab Zh d hlev hmin hab hd hdo
  obtain ⟨-, -, -, h0, -, hfM, -, hiso⟩ := hmin
  have hsurj := GlobalTheory.T.surjective_functionFieldModelHom_of_projective o Ω X M fM hfM h0.proj
  have hrange : Set.range d ⊆ Xab := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hsurj (d y)
    obtain ⟨V, _, _, _, ξ, τ, κ, hzξ, h1, h2⟩ := GlobalTheory.T.exists_dvr_centred_point_generic_both_models o Ω Y X M fM d hfM hd hdo z ⟨y, hz.symm⟩
    have hzab : z ∈ (abLocus Zh.G : Set M.Z) :=
      GlobalTheory.T.range_subset_abelianLocus_of_levelTrait g n F W o Ω β S ρ u hsys Y M q U₀ EE Zh hlev h0 V ξ τ κ h1 h2 hzξ
    rw [hab] at hzab
    show d y ∈ (Xab : Set X.Z)
    rw [← hz]
    exact hzab
  obtain ⟨U, c, hc, hU⟩ := GlobalTheory.T.exists_open_finite_onto_of_levelCover g n F o Ω β S u Y X M q fM Xab d hlev hfM hiso hd hdo hrange
  exact ⟨U, c, hc, hab ▸ hU⟩

end GlobalTheory.OpenLev
