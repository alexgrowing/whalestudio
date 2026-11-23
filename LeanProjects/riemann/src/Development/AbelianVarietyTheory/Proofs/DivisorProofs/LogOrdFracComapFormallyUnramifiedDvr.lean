import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RestrictOrd

open IsLocalRing

theorem isLocalHom_restrict {K L : Type} [Field K] [Field L] (φ : K →+* L)
    (V : ValuationSubring L) :
    IsLocalHom (φ.restrict (V.comap φ) V fun _ hx => hx) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, hb⟩ := ha
  have hb' : ((b : V) : L) = φ (a : K) := by
    rw [hb]; rfl
  have ha0 : (a : K) ≠ 0 := by
    intro h0
    have : ((b : V) : L) = 0 := by rw [hb', h0, map_zero]
    exact b.ne_zero (Subtype.ext this)
  have hmem : (a : K)⁻¹ ∈ V.comap φ := by
    change φ (a : K)⁻¹ ∈ V
    rw [map_inv₀, ← hb']
    have : ((b⁻¹ : Vˣ) : V) * (b : V) = 1 := b.inv_mul
    have h2 : (((b⁻¹ : Vˣ) : V) : L) = ((b : V) : L)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (congrArg Subtype.val this)
    rw [← h2]
    exact ((b⁻¹ : Vˣ) : V).2
  exact isUnit_iff_exists_inv.2 ⟨⟨(a : K)⁻¹, hmem⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

theorem log_ordFrac_comap (K L : Type) [Field K] [Field L] (φ : K →+* L)
    (V : ValuationSubring L) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap φ)] :
    (letI := (φ.restrict (V.comap φ) V fun _ hx => hx).toAlgebra;
      Algebra.FormallyUnramified (V.comap φ) V ∧ Algebra.EssFiniteType (V.comap φ) V) →
    ∀ g : K, g ≠ 0 →
      WithZero.log (Ring.ordFrac V (φ g)) = WithZero.log (Ring.ordFrac (V.comap φ) g) := by
  intro h g hg
  set ψ := φ.restrict (V.comap φ) V fun _ hx => hx with hψdef
  letI := ψ.toAlgebra
  obtain ⟨hu, he⟩ := h
  haveI : IsLocalHom ψ := isLocalHom_restrict φ V
  haveI : IsLocalHom (algebraMap (V.comap φ) V) := inferInstanceAs (IsLocalHom ψ)
  have hmap : (maximalIdeal (V.comap φ)).map (algebraMap (V.comap φ) V) = maximalIdeal V :=
    Algebra.FormallyUnramified.map_maximalIdeal
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (V.comap φ)
  have ht' : Irreducible (ψ t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmap,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht, Ideal.map_span,
      Set.image_singleton]
    rfl
  exact GlobalTheory.EtaleDiv.log_ordFrac_map (V.comap φ) V φ ψ (fun _ => rfl) ht ht' hg

end GlobalTheory.RestrictOrd
