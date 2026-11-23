import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapMapPullbackFstLocalization
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapMapEqOfLocallyGenerated
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralAppOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenPowIdeal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem relGen_multiple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : GlobalTheory.EffCartierData Y.X) (k : ℕ) (ρ : gen Y ⟶ gen X),
    Y.jQ ≫ ρ = X.jQ → GlobalTheory.IsAmpleLB (polOf Y k BY) → (∀ x ∈ BY.idealSheaf.support, x ∉ abLocus Y.t.G) →
    ∃ n : ℕ, 0 < n ∧ (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).comap (ρ ≫ genι X) =
      (BY.idealSheaf ^ n).comap (genι Y) := by
  intro E _ _ _ H D l Xo c X Y BY k ρ hρ hamp _
  obtain ⟨n, hn, hg⟩ := GlobalTheory.GenPow.gen_pow_ideal E H D l Xo c X Y BY k ρ hρ hamp
  refine ⟨n, hn, ?_⟩
  have := c.fin
  have : NumberField c.F := {}
  have := GlobalTheory.GenPush.isProper_of_jQ X Y ρ hρ
  rw [Scheme.IdealSheafData.map_comp, Scheme.IdealSheafData.comap_comp,
    GlobalTheory.LocClosure.comap_map_pullback_fst_localization (nonZeroDivisors (𝓞 c.F)) X.X X.s]
  exact GlobalTheory.IdealPush.comap_map_eq_of_locally_generated ρ _ (GlobalTheory.GenPush.main E H D l Xo c X Y ρ hρ) hg

end GlobalTheory.TorRef
