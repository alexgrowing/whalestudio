import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsPushforwardOpenImmersion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_pushforward_open_immersion : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} (t : SAB H S) (t' : SAB H S') (v : S' ⟶ S) [IsOpenImmersion v] (n : SABMap t' t v) (U' : S'.Opens) (θ' : ∀ i, Γ(t'.G.left, t'.G.hom ⁻¹ᵁ U' ⊓ t'.PP.L.U i)), θ' ∈ secOn t'.PP.L (t'.G.hom ⁻¹ᵁ U') → ∃ θ : ∀ i, Γ(t.G.left, t.G.hom ⁻¹ᵁ (v ''ᵁ U') ⊓ t.PP.L.U i), θ ∈ secOn t.PP.L (t.G.hom ⁻¹ᵁ (v ''ᵁ U')) ∧ ∀ (g : t'.G.left) (j : t'.PP.L.ι), g ∈ t'.G.left.basicOpen (θ' j) → ∃ i, n.φ.base g ∈ t.G.left.basicOpen (θ i) := by
  first | exact @GlobalTheory.SecTransport.exists_secOn_image | exact GlobalTheory.SecTransport.exists_secOn_image | (intros; apply GlobalTheory.SecTransport.exists_secOn_image <;> assumption)
