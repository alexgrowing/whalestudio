import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ValCount
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open CategoryTheory AlgebraicGeometry IsLocalRing GlobalTheory GlobalTheory.ValCount GlobalTheory.TrueGeo
open scoped Classical

theorem UpperTheory.order_eq_valuation_codim_one :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (x : X) (W : ValuationSubring X.functionField), Order.coheight x = 1 → DominatesStalk W x → ∀ f : X.functionField, Scheme.ord f x = vord W f := by
  intro X _ _ _ x W hx h f
  have hW := h.isDiscreteValuationRing hx
  have hS := IsNormalScheme.isDiscreteValuationRing_stalk hx
  obtain ⟨e, he⟩ := h.exists_ringEquiv hx
  by_cases hf : f = 0
  · subst hf
    rw [vord_eq, map_zero, Scheme.ord_zero]
    simp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk x)
  have hϖ' : Irreducible (e ϖ) := (MulEquiv.irreducible_iff e).2 hϖ
  obtain ⟨n, u, hu, hu'⟩ := exists_eq_unit_mul_zpow W hϖ' hf
  obtain ⟨v, rfl⟩ := e.surjective u
  have hv : IsUnit v := (MulEquiv.isUnit_map (f := e)).1 hu
  have h1 : ((e v : W) : X.functionField) ≠ 0 := fun h => hu.ne_zero (Subtype.ext h)
  have h2 : ((e ϖ : W) : X.functionField) ≠ 0 := fun h => hϖ'.ne_zero (Subtype.ext h)
  have h3 : vord W f = n := by
    rw [hu', vord_mul _ h1 (zpow_ne_zero _ h2), vord_of_isUnit _ hu, vord_zpow,
      vord_irreducible _ hϖ']
    ring
  rw [h3, Scheme.ord_eq_iff hx hf]
  change Ring.ordFrac (X.presheaf.stalk x) f = _
  rw [hu', he, he, map_mul, map_zpow₀, Ring.ordFrac_of_isUnit hv, Ring.ordFrac_irreducible hϖ,
    one_mul, ← WithZero.exp_zsmul, smul_eq_mul, mul_one]
  rfl
