import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.MemShaSubmoduleCohomologyAddEquivOfEquivIff
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.Kummer
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GlobalEulerFormulaInf
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CoprimeTwist
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFixed
import GroundTheory.GlobalFields.IdeleClassGroup.InvariantsGalois

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)

theorem roots_trivial (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ) :
    ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (t : gsRootsZMod S ℓ),
      (gsRootsZMod S ℓ).ρ g t = t := by
  obtain ⟨ζ, hζ⟩ := hζ
  intro g t
  have hfix : ∀ x : L.1, (g : galUnramifiedOutside K.1 ℚ̄ S) (gsEmbedding hL x) = gsEmbedding hL x :=
    (mem_gsOpenSubgroup_iff S hL g).1 g.2
  have hprim : IsPrimitiveRoot (gsEmbedding hL ζ) ℓ := hζ.map_of_injective (gsEmbedding hL).injective
  change Additive (rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S)) at t
  set u : rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S) := Additive.toMul t with hu
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one (ξ := ((u : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S))
    (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one])
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change (g : galUnramifiedOutside K.1 ℚ̄ S) ((u : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) : maxUnramifiedOutside K.1 ℚ̄ S) = _
  rw [← hk, map_pow, hfix]
  exact hk

instance moduleFinite_gsRootsZMod : Module.Finite (ZMod ℓ) (gsRootsZMod S ℓ) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : Finite (gsRootsZMod S ℓ) :=
    inferInstanceAs (Finite (Additive (rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S))))
  exact Module.Finite.of_finite

theorem normal_of_gsOpenSubgroup_normal
    (h : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).Normal) : Normal K.1 L.1 := by
  have hmap : ∀ g : ℚ̄ ≃ₐ[ℚ] ℚ̄, g ∈ K.1.fixingSubgroup → ∀ x ∈ L.1, g x ∈ L.1 := by
    intro g hg x hx
    let g' : ℚ̄ ≃ₐ[K.1] ℚ̄ := AlgEquiv.ofRingEquiv (f := g.toRingEquiv)
      (fun c => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg c c.2)
    let gS : galUnramifiedOutside K.1 ℚ̄ S := g'.restrictNormal (maxUnramifiedOutside K.1 ℚ̄ S)
    have hgS : ∀ y : maxUnramifiedOutside K.1 ℚ̄ S, ((gS y : maxUnramifiedOutside K.1 ℚ̄ S) : ℚ̄) = g y :=
      fun y => g'.restrictNormal_commutes _ y
    have hxS : x ∈ maxUnramifiedOutside K.1 ℚ̄ S := hL ⟨x, hx⟩
    have he : gsEmbedding hL ⟨x, hx⟩ = ⟨x, hxS⟩ := Subtype.ext rfl
    have key := mem_of_forall_gsOpenSubgroup_fixes S hL (gS ⟨x, hxS⟩) (fun σ hσ => by
      have hc : gS⁻¹ * σ * gS ∈ gsOpenSubgroup S hL := by
        have := h.conj_mem σ hσ gS⁻¹
        simpa [mul_assoc] using this
      have hfx : (gS⁻¹ * σ * gS) ⟨x, hxS⟩ = ⟨x, hxS⟩ := by
        have := (mem_gsOpenSubgroup_iff S hL _).1 hc ⟨x, hx⟩
        rwa [he] at this
      calc σ (gS ⟨x, hxS⟩) = gS ((gS⁻¹ * σ * gS) ⟨x, hxS⟩) := by
            simp only [AlgEquiv.mul_apply]
            rw [← AlgEquiv.mul_apply gS, mul_inv_cancel, AlgEquiv.one_apply]
        _ = gS ⟨x, hxS⟩ := by rw [hfx])
    rwa [hgS] at key
  have : (L.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf, IntermediateField.mem_fixingSubgroup_iff] at hn ⊢
    intro x hx
    have hx' := hmap _ (inv_mem g.2) x hx
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply]
    rw [hn _ hx']
    exact AlgEquiv.apply_symm_apply _ x⟩
  have := FiniteSubfield.isGalois_of_normal (F := K) (E := L)
  infer_instance

open scoped Classical in

theorem card_infinitePlace_eq (K : FiniteSubfield) : Fintype.card (InfinitePlace K.1) =
    Fintype.card {v : InfinitePlace K.1 // v.IsReal} + Fintype.card {v : InfinitePlace K.1 // v.IsComplex} := by
  have h2 : Fintype.card {v : InfinitePlace K.1 // v.IsComplex} =
      Fintype.card {v : InfinitePlace K.1 // ¬ v.IsReal} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun v => InfinitePlace.not_isReal_iff_isComplex.symm)
  have h := Fintype.card_subtype_compl (fun v : InfinitePlace K.1 => v.IsReal)
  have h3 := Fintype.card_subtype_le (fun v : InfinitePlace K.1 => v.IsReal)
  rw [h2, h]
  omega

end PositivityTheory.Lit1.GEN.X
