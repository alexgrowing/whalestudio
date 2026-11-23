import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateCondCongr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem asIdeal_spMap_field {B k : Type} [CommRing B] [Field k] (φ : B →+* k) (u : Sp k) :
    ((spMap φ).base u).asIdeal = RingHom.ker φ := by
  have hu : u.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ u.isPrime
  rw [RingHom.ker_eq_comap_bot, ← hu]
  rw [spMap, Spec.map_base]
  rfl

theorem exists_ringHom_pair_of_specializes {X : Scheme.{0}} {k k' : Type} [Field k] [Field k'] (x : Sp k ⟶ X)
    (x' : Sp k' ⟶ X) (u : Sp k) (u' : Sp k') (h : x'.base u' ⤳ x.base u) :
    ∃ (B : Type) (_ : CommRing B) (g : B →+* k) (g' : B →+* k') (ρ : Sp B ⟶ X),
      RingHom.ker g' ≤ RingHom.ker g ∧ spMap g ≫ ρ = x ∧ spMap g' ≫ ρ = x' := by
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x.base u ∈ (⊤ : X.Opens) from trivial)
  have hV' : IsAffineOpen V := hV
  have hx'V : x'.base u' ∈ V := h.mem_open V.isOpen hxV
  have hsub : Set.range x.base ⊆ Set.range hV'.fromSpec := by
    rw [hV'.range_fromSpec]
    rintro _ ⟨v, rfl⟩
    rwa [Subsingleton.elim v u]
  have hsub' : Set.range x'.base ⊆ Set.range hV'.fromSpec := by
    rw [hV'.range_fromSpec]
    rintro _ ⟨v, rfl⟩
    rwa [Subsingleton.elim v u']
  let xV := IsOpenImmersion.lift hV'.fromSpec x hsub
  let x'V := IsOpenImmersion.lift hV'.fromSpec x' hsub'
  have hfx : xV ≫ hV'.fromSpec = x := IsOpenImmersion.lift_fac _ _ _
  have hfx' : x'V ≫ hV'.fromSpec = x' := IsOpenImmersion.lift_fac _ _ _
  have e1 : spMap (Spec.preimage xV).hom = xV := Spec.map_preimage xV
  have e2 : spMap (Spec.preimage x'V).hom = x'V := Spec.map_preimage x'V
  refine ⟨Γ(X, V), inferInstance, (Spec.preimage xV).hom, (Spec.preimage x'V).hom, hV'.fromSpec, ?_, ?_, ?_⟩
  · rw [← asIdeal_spMap_field _ u, ← asIdeal_spMap_field _ u']
    refine (PrimeSpectrum.le_iff_specializes ((spMap (Spec.preimage x'V).hom).base u')
      ((spMap (Spec.preimage xV).hom).base u)).mpr ?_
    rw [e1, e2]
    have h2 : hV'.fromSpec (x'V u') ⤳ hV'.fromSpec (xV u) := by
      rw [← hfx, ← hfx'] at h
      simpa only [Scheme.Hom.comp_apply] using h
    exact (hV'.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp h2
  · rw [e1]; exact hfx
  · rw [e2]; exact hfx'

end GlobalTheory
