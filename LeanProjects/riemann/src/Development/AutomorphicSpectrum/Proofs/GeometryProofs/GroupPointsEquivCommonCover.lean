import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsPullbackFieldPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.MarkFibre

theorem exists_fibre_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S₁ S₂ V : Scheme.{0}) (t₁ : SAB H S₁) (t₂ : SAB H S₂) (tV : SAB H V) (f₁ : V ⟶ S₁) (f₂ : V ⟶ S₂) (m₁ : SABMap tV t₁ f₁) (m₂ : SABMap tV t₂ f₂) (x : Sp ℂ ⟶ V) (y₁ : Sp ℂ ⟶ S₁) (y₂ : Sp ℂ ⟶ S₂), x ≫ f₁ = y₁ → x ≫ f₂ = y₂ → ∃ Φ : (Over.mk y₂ ⟶ t₂.G) ≃ (Over.mk y₁ ⟶ t₁.G), (∀ q q', Φ (q * q') = Φ q * Φ q') ∧ (∀ q, ∃ w : Sp ℂ ⟶ tV.G.left, w ≫ tV.G.hom = x ∧ w ≫ m₂.φ = q.left ∧ w ≫ m₁.φ = (Φ q).left) ∧ ∀ (N : ℕ) (q q' : Over.mk y₂ ⟶ t₂.G) (ζ : (Γ(Sp ℂ, ⊤))ˣ), GlobalTheory.UU.CubWeil t₁.cub N (Φ q) (Φ q') ζ → GlobalTheory.UU.CubWeil t₂.cub N q q' ζ := by
  intro E _ _ _ H S₁ S₂ V t₁ t₂ tV f₁ f₂ m₁ m₂ x y₁ y₂ h₁ h₂
  subst h₁ h₂
  have hw₁ : m₁.cm.F ≫ t₁.G.hom = tV.G.hom ≫ f₁ := m₁.cart.1.w
  have hw₂ : m₂.cm.F ≫ t₂.G.hom = tV.G.hom ≫ f₂ := m₂.cart.1.w
  obtain ⟨e₁, he₁, -⟩ := GlobalTheory.AlphaPair.exists_pullEquiv m₁ 0 x (x ≫ f₁) rfl
  obtain ⟨e₂, he₂, -⟩ := GlobalTheory.AlphaPair.exists_pullEquiv m₂ 0 x (x ≫ f₂) rfl
  have mul₁ : ∀ (T : Over V) (a b : T ⟶ tV.G), Out.toBase hw₁ (a * b) = Out.toBase hw₁ a * Out.toBase hw₁ b :=
    fun T a b => Over.OverMorphism.ext (m₁.cart.2 T a b (Out.toBase hw₁ a) (Out.toBase hw₁ b) rfl rfl).symm
  have mul₂ : ∀ (T : Over V) (a b : T ⟶ tV.G), Out.toBase hw₂ (a * b) = Out.toBase hw₂ a * Out.toBase hw₂ b :=
    fun T a b => Over.OverMorphism.ext (m₂.cart.2 T a b (Out.toBase hw₂ a) (Out.toBase hw₂ b) rfl rfl).symm
  have b₁ : ∀ p, Out.toBase hw₁ (e₁ p) = p := fun p => Over.OverMorphism.ext (he₁ p)
  have b₂ : ∀ p, Out.toBase hw₂ (e₂ p) = p := fun p => Over.OverMorphism.ext (he₂ p)
  have key : ∀ q, e₁ ((e₂.trans e₁.symm) q) = e₂ q := fun q => e₁.apply_symm_apply _
  refine ⟨(e₂.trans e₁.symm).toEquiv, fun q q' => map_mul (e₂.trans e₁.symm) q q', fun q =>
    ⟨(e₂ q).left, Over.w (e₂ q), he₂ q, ?_⟩, fun N q q' ζ h => ?_⟩
  · have := he₁ ((e₂.trans e₁.symm) q)
    rw [key] at this
    exact this
  · have ha : e₂ q ^ N = 1 := by
      rw [← key, ← map_pow]
      exact (congrArg e₁ h.1).trans (map_one e₁)
    have ha' : e₂ q' ^ N = 1 := by
      rw [← key, ← map_pow]
      exact (congrArg e₁ h.2.1).trans (map_one e₁)
    obtain ⟨ζ', hζ', -⟩ := GlobalTheory.UU.existsUnique_cubWeil tV.cub ha ha'
    have c₁ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f₁ _ _ m₁.cm hw₁ mul₁ _ _ t₁.cub tV.cub m₁.lin N _ _ _ ζ' hζ'
    have c₂ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f₂ _ _ m₂.cm hw₂ mul₂ _ _ t₂.cub tV.cub m₂.lin N _ _ _ ζ' hζ'
    rw [b₂, b₂] at c₂
    rw [← key q, ← key q', b₁, b₁] at c₁
    obtain rfl : ζ' = ζ := c₁.unique h
    exact c₂

end GlobalTheory.CompanionTheory.Ar.MarkFibre
