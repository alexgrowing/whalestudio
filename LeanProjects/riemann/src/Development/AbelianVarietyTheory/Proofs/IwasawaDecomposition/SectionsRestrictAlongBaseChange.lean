import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperRestrictPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelCoverField
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaPull

theorem pull_theta_gen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (U : S.Opens) (V : S'.Opens), V ≤ f ⁻¹ᵁ U → ∀ (θ : ∀ i, Γ(t.G.left, t.G.hom ⁻¹ᵁ U ⊓ t.PP.L.U i)), θ ∈ secOn t.PP.L (t.G.hom ⁻¹ᵁ U) → (∀ y ∈ U, ∃ (g : t.G.left) (i : t.PP.L.ι), t.G.hom g = y ∧ g ∈ t.G.left.basicOpen (θ i)) → ∃ θ' : ∀ i, Γ(t'.G.left, t'.G.hom ⁻¹ᵁ V ⊓ t'.PP.L.U i), θ' ∈ secOn t'.PP.L (t'.G.hom ⁻¹ᵁ V) ∧ ∀ y ∈ V, ∃ (g : t'.G.left) (i : t'.PP.L.ι), t'.G.hom g = y ∧ g ∈ t'.G.left.basicOpen (θ' i) := by
  intro E _ _ _ H S S' t t' f m U V hVU θ hθ hnv
  have hW : t'.G.hom ⁻¹ᵁ V ≤ m.cm.F ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U) := fun y hy => by
    show t.G.hom (m.cm.F y) ∈ U
    rw [← Scheme.Hom.comp_apply, m.cart.1.w, Scheme.Hom.comp_apply]
    exact hVU hy
  obtain ⟨θ', hθ', hb⟩ := GlobalTheory.AbLocusPull.exists_secOn_pull t.PP.isLB t'.PP.isLB (GlobalTheory.LevCover.sabMap_lbIso m) hW hθ
  refine ⟨θ', hθ', fun y hy => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := hnv (f y) (hVU hy)
  obtain ⟨g', h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 g y hg
  obtain ⟨k, hk⟩ := exists_chart t'.PP.isLB g'
  refine ⟨g', k, h₂, hb g' ?_ i k hk (h₁ ▸ hi)⟩
  show t'.G.hom g' ∈ V
  rw [h₂]; exact hy

end GlobalTheory.ThetaPull
