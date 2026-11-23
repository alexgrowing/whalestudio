import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianTypePropagationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleExtensionNormalBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleExtensionUniquenessStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat

namespace GlobalTheory.GroupBplus

theorem groupSt : GlobalTheory.Published.RaynaudExtension → GlobalTheory.Published.GrothendieckOrthogonality → GlobalTheory.Published.DualAbelianScheme →
    GlobalTheory.Published.CubeTheorem → GroupSt := by
  intro hR _ hD hC E _ _ _ H Dw p _ X Z _ _ g tZ hX hgen t m
  obtain ⟨t₀, ⟨m₀⟩, ht₀⟩ := hgen
  obtain ⟨GG₀, act₀, pol₀, θ₀, ε₀, τ₀, hP₀⟩ := GlobalTheory.T.cm_abelian_type_propagation E H Dw p (Kbar X) t₀ ht₀
  choose GG act pol θ ε τ hU using fun U =>
    GlobalTheory.T.p_divisible_extension_normal_base hR hD hC E H Dw p X Z g tZ hX t₀ m₀ ht₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ hP₀ U (t U) (m U)
  exact ⟨GG, act, pol, θ, ε, τ, fun U => (hU U).1, fun U U' h =>
    GlobalTheory.T.p_divisible_extension_uniqueness E H Dw p X Z g tZ hX t₀ m₀ ht₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ hP₀ U U' h (t U) (m U) (t U') (m U')
      _ _ _ _ _ _ _ _ _ _ _ _ (hU U).1 (hU U).2 (hU U').1 (hU U').2⟩

end GlobalTheory.GroupBplus
