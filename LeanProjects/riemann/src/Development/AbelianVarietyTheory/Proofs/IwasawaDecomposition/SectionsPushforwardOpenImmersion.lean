import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFibrewiseThetaOfOpenImmersionCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecTransport

theorem exists_secOn_image : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} (t : SAB H S) (t' : SAB H S') (v : S' ⟶ S) [IsOpenImmersion v] (n : SABMap t' t v) (U' : S'.Opens) (θ' : ∀ i, Γ(t'.G.left, t'.G.hom ⁻¹ᵁ U' ⊓ t'.PP.L.U i)), θ' ∈ secOn t'.PP.L (t'.G.hom ⁻¹ᵁ U') → ∃ θ : ∀ i, Γ(t.G.left, t.G.hom ⁻¹ᵁ (v ''ᵁ U') ⊓ t.PP.L.U i), θ ∈ secOn t.PP.L (t.G.hom ⁻¹ᵁ (v ''ᵁ U')) ∧ ∀ (g : t'.G.left) (j : t'.PP.L.ι), g ∈ t'.G.left.basicOpen (θ' j) → ∃ i, n.φ.base g ∈ t.G.left.basicOpen (θ i) := by
  intro E _ _ _ H S S' t t' v _ n U' θ' hθ'
  have h := n.cart.1
  have : IsOpenImmersion n.cm.F := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip ‹_›
  obtain ⟨w, g, -⟩ := n.lin
  have sq : ∀ x, t.G.hom (n.cm.F x) = v (t'.G.hom x) := fun x => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  have hr : t.G.hom ⁻¹ᵁ (v ''ᵁ U') ≤ n.cm.F.opensRange := by
    rintro x ⟨y', -, e⟩
    obtain ⟨x', h₁, -⟩ := Scheme.exists_preimage_of_isPullback h x y' e.symm
    exact ⟨x', h₁⟩
  have hW : n.cm.F ⁻¹ᵁ (t.G.hom ⁻¹ᵁ (v ''ᵁ U')) ≤ t'.G.hom ⁻¹ᵁ U' := by
    rintro x ⟨y', hy', e⟩
    have e' : y' = t'.G.hom x := v.isOpenEmbedding.injective (e.trans (sq x))
    show t'.G.hom x ∈ U'
    rw [← e']; exact hy'
  obtain ⟨θ, hθ, hb⟩ := GlobalTheory.ThetaLocal.exists_secOn_push t.PP.isLB t'.PP.isLB ⟨w, g⟩ hr hW hθ'
  refine ⟨θ, hθ, fun x k hk => ?_⟩
  obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart t.PP.isLB (n.cm.F x)
  have hx : t'.G.hom x ∈ U' := (t'.G.left.basicOpen_le _ hk).1
  exact ⟨j, hb x ⟨t'.G.hom x, hx, (sq x).symm⟩ j k hj hk⟩

end GlobalTheory.SecTransport
