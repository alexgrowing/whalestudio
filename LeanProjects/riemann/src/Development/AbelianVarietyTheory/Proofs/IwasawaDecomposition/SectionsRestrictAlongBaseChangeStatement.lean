import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsRestrictAlongBaseChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_restrict_along_base_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (U : S.Opens) (V : S'.Opens), V ≤ f ⁻¹ᵁ U → ∀ (θ : ∀ i, Γ(t.G.left, t.G.hom ⁻¹ᵁ U ⊓ t.PP.L.U i)), θ ∈ secOn t.PP.L (t.G.hom ⁻¹ᵁ U) → (∀ y ∈ U, ∃ (g : t.G.left) (i : t.PP.L.ι), t.G.hom g = y ∧ g ∈ t.G.left.basicOpen (θ i)) → ∃ θ' : ∀ i, Γ(t'.G.left, t'.G.hom ⁻¹ᵁ V ⊓ t'.PP.L.U i), θ' ∈ secOn t'.PP.L (t'.G.hom ⁻¹ᵁ V) ∧ ∀ y ∈ V, ∃ (g : t'.G.left) (i : t'.PP.L.ι), t'.G.hom g = y ∧ g ∈ t'.G.left.basicOpen (θ' i) := by
  first | exact @GlobalTheory.ThetaPull.pull_theta_gen | exact GlobalTheory.ThetaPull.pull_theta_gen | (intros; apply GlobalTheory.ThetaPull.pull_theta_gen <;> assumption)
