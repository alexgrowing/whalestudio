import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalCoeffF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodMapLevelCoverWeightZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodMapLevelDividesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGoodMapSideCoverStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.LvCover

theorem exists_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (Z : ∀ (l : Level H) (c : Coeff l), (∀ p : ℕ, p.Prime → l.GoodAt p) → GMod (Xo l) c)
    (l₁ : Level H) (c₁ : Coeff l₁) (h₁ : ∀ p : ℕ, p.Prime → l₁.GoodAt p)
    (l₂ : Level H) (c₂ : Coeff l₂) (h₂ : ∀ p : ℕ, p.Prime → l₂.GoodAt p),
    ∃ (l : Level H) (c : Coeff l) (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (b₁ : 𝓞 c₁.F →+* 𝓞 c.F) (b₂ : 𝓞 c₂.F →+* 𝓞 c.F)
      (r₁ : (Xo l).XF c ⟶ (Xo l₁).XF c₁) (r₂ : (Xo l).XF c ⟶ (Xo l₂).XF c₂)
      (_ : TwMap (RingEquiv.refl (𝓞 E)) (Z l c hg).oF.t (Z l₁ c₁ h₁).oF.t r₁)
      (_ : TwMap (RingEquiv.refl (𝓞 E)) (Z l c hg).oF.t (Z l₂ c₂ h₂).oF.t r₂),
      b₁.Finite ∧ b₂.Finite ∧ Function.Surjective r₁ ∧ Function.Surjective r₂ ∧
      r₁ ≫ (Z l₁ c₁ h₁).j ≫ (Z l₁ c₁ h₁).s = (Z l c hg).j ≫ (Z l c hg).s ≫ spMap b₁ ∧
      r₂ ≫ (Z l₂ c₂ h₂).j ≫ (Z l₂ c₂ h₂).s = (Z l c hg).j ≫ (Z l c hg).s ≫ spMap b₂ := by
  intro E _ _ _ H D Xo Z l₁ c₁ h₁ l₂ c₂ h₂
  haveI := (coeffTop c₁ c₂).fin
  obtain ⟨r₁, hr₁⟩ : ∃ r, GoodMap (le_coeffF₁ c₁ c₂) (Z (top l₁ l₂) (coeffTop c₁ c₂) h₁) (Z l₁ c₁ h₁) r := by
    by_cases hD : D.p + D.q = 0
    · exact GlobalTheory.T.exists_good_map_level_cover_weight_zero E H D hD _ _ _ _ _ _ _ _ _
    · exact GlobalTheory.T.exists_good_map_level_divides E H D (by omega) _ _ (dvd_top l₁ l₂) _ _ _ _ _ _ _
  obtain ⟨r₂, hr₂⟩ : ∃ r, GoodMap (le_coeffF₂ c₁ c₂) (Z (top l₁ l₂) (coeffTop c₁ c₂) h₁) (Z l₂ c₂ h₂) r := by
    by_cases hD : D.p + D.q = 0
    · exact GlobalTheory.T.exists_good_map_level_cover_weight_zero E H D hD _ _ _ _ _ _ _ _ _
    · obtain ⟨a, ha⟩ := GlobalTheory.T.exists_good_map_side_cover E H D l₁ l₂ (Xo _) (Xo (side l₁ l₂)) c₁ c₂ (Z _ _ h₁)
        (Z (side l₁ l₂) (coeffSide c₁ c₂) h₂)
      obtain ⟨b, hb⟩ := GlobalTheory.T.exists_good_map_level_divides E H D (by omega) _ _ (dvd_side l₁ l₂) (Xo _) (Xo l₂) (coeffSide c₁ c₂) c₂
        (le_coeffF₂ c₁ c₂) (Z (side l₁ l₂) (coeffSide c₁ c₂) h₂) (Z l₂ c₂ h₂)
      exact ⟨a ≫ b, ha.comp hb⟩
  obtain ⟨⟨m₁⟩, s₁, e₁⟩ := hr₁
  obtain ⟨⟨m₂⟩, s₂, e₂⟩ := hr₂
  exact ⟨top l₁ l₂, coeffTop c₁ c₂, h₁, intMap (le_coeffF₁ c₁ c₂), intMap (le_coeffF₂ c₁ c₂), r₁, r₂, m₁, m₂,
    intMap_finite _, intMap_finite _, s₁, s₂, j_s_of_snd _ _ _ _ e₁, j_s_of_snd _ _ _ _ e₂⟩

end GlobalTheory.LvCover
