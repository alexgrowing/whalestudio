import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.StabilizersDefs
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.OrbitInvariants
import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingMackeyPlaces
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal MulAction

universe u

noncomputable section

section PlaceAction

variable {F L : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  {v : HeightOneSpectrum (𝓞 F)}

theorem placeOfAlgHom_comp_algEquiv (j : L →ₐ[F] AlgebraicClosure (v.adicCompletion F))
    (τ : L ≃ₐ[F] L) :
    placeOfAlgHom (j.comp (τ : L →ₐ[F] L)) = τ⁻¹ • placeOfAlgHom j := by
  set w := placeOfAlgHom j
  have h : w.1 = τ • (τ⁻¹ • w).1 := by
    rw [coe_smul_placesOver, smul_inv_smul]
  let c : (τ⁻¹ • w).1.adicCompletion L →ₐ[v.adicCompletion F]
      AlgebraicClosure (v.adicCompletion F) :=
    (completionEmbeddingOfAlgHom j).comp (galEquiv v τ (τ⁻¹ • w).1 w.1 h).toAlgHom
  refine (eq_placeOfAlgHom (j.comp (τ : L →ₐ[F] L)) c fun x => ?_).symm
  change completionEmbeddingOfAlgHom j (galEquiv v τ (τ⁻¹ • w).1 w.1 h (algebraMap L _ x)) = j (τ x)
  rw [galEquiv_algebraMap, completionEmbeddingOfAlgHom_algebraMap]

end PlaceAction

section Finite

variable {F L Ω : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
  [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] [IsGalois F Ω]
  {S : Set (HeightOneSpectrum (𝓞 F))}
  (hL : ∀ x : L, algebraMap L Ω x ∈ maxUnramifiedOutside F Ω S) [IsGalois F L]
  (ιs : ∀ v : S, Ω →ₐ[F] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))

theorem gsLocalEmbedding_mul_left (v : S) (σ x : galUnramifiedOutside F Ω S) :
    gsLocalEmbedding hL ιs v (σ * x) =
      (gsLocalEmbedding hL ιs v x).comp (((gsRestrictGal hL σ)⁻¹ : L ≃ₐ[F] L) : L →ₐ[F] L) := by
  ext l
  change ιs v ((((σ * x)⁻¹ : galUnramifiedOutside F Ω S) (gsEmbedding hL l) :
      maxUnramifiedOutside F Ω S) : Ω) = ιs v ((((x⁻¹ : galUnramifiedOutside F Ω S)
      (gsEmbedding hL ((gsRestrictGal hL σ)⁻¹ l))) : maxUnramifiedOutside F Ω S) : Ω)
  rw [← map_inv, gsEmbedding_gsRestrictGal, mul_inv_rev, AlgEquiv.mul_apply]

theorem gsRestrictGal_smul_gsLocalPlace (v : S) (σ x : galUnramifiedOutside F Ω S) :
    gsRestrictGal hL σ • gsLocalPlace hL ιs v x = gsLocalPlace hL ιs v (σ * x) := by
  change _ = placeOfAlgHom (gsLocalEmbedding hL ιs v (σ * x))
  rw [gsLocalEmbedding_mul_left, placeOfAlgHom_comp_algEquiv, inv_inv]

theorem mem_stabilizer_gsLocalPlace_iff (v : S) (τ : L ≃ₐ[F] L) :
    τ ∈ MulAction.stabilizer (L ≃ₐ[F] L) (gsLocalPlace hL ιs v 1) ↔ τ ∈ gsDecompGroup hL ιs v := by
  rw [mem_stabilizer_iff]
  constructor
  · intro hτ
    obtain ⟨σ, rfl⟩ := gsRestrictGal_surjective hL τ
    rw [gsRestrictGal_smul_gsLocalPlace, mul_one] at hτ
    obtain ⟨g, hg⟩ := exists_algEquiv_of_placeOfAlgHom_eq _ _ hτ
    refine ⟨g, (gsRestrictGal_eq_iff hL _ _).2 fun l => ?_⟩
    rw [gsEmbedding_gsRestrictGal]
    have h1 := hg (gsRestrictGal hL σ l)
    rw [gsLocalEmbedding_apply, gsLocalEmbedding_apply, inv_one, AlgEquiv.one_apply,
      gsEmbedding_gsRestrictGal, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply,
      ← gsFinFamily_apply] at h1
    exact (Subtype.ext ((ιs v).injective h1)).symm
  · rintro ⟨g, rfl⟩
    change gsRestrictGal hL (gsFinFamily S ιs v g) • _ = _
    rw [gsRestrictGal_smul_gsLocalPlace]
    have h := gsLocalPlace_mul hL ιs v 1 (one_mem _) g
    rwa [mul_one, one_mul] at h

theorem stabilizer_gsLocalPlace (v : S) :
    MulAction.stabilizer (L ≃ₐ[F] L) (gsLocalPlace hL ιs v 1) = gsDecompGroup hL ιs v :=
  Subgroup.ext fun τ => mem_stabilizer_gsLocalPlace_iff hL ιs v τ

omit [NumberField F] [NumberField L] [IsGalois F L] in

theorem galSmul_mem_placesOver (τ : L ≃ₐ[F] L) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∈ placesOver S) : τ • w ∈ placesOver S := by
  obtain ⟨v, hv, hlies⟩ := hw
  exact ⟨v, hv, (τ • (⟨w, hlies⟩ : PlacesOver L v)).2⟩

variable (S) in

abbrev placesOverAction : MulAction (L ≃ₐ[F] L) (placesOver S : Set (HeightOneSpectrum (𝓞 L))) :=
  stableMulAction (placesOver S) fun τ _ hw => galSmul_mem_placesOver τ hw

def gsPlaceAbove (v : S) : (placesOver S : Set (HeightOneSpectrum (𝓞 L))) :=
  ⟨(gsLocalPlace hL ιs v 1).1, v.1, v.2, (gsLocalPlace hL ιs v 1).2⟩

theorem stabilizer_gsPlaceAbove (v : S) :
    let _ := placesOverAction (L := L) S
    MulAction.stabilizer (L ≃ₐ[F] L) (gsPlaceAbove hL ιs v) = gsDecompGroup hL ιs v := by
  let _ := placesOverAction (L := L) S
  rw [← stabilizer_gsLocalPlace hL ιs v]
  ext τ
  rw [mem_stabilizer_iff, mem_stabilizer_iff, Subtype.ext_iff, Subtype.ext_iff]
  rfl

omit [IsGalois F L] in

theorem finite_placesOver [Finite S] :
    Finite (placesOver S : Set (HeightOneSpectrum (𝓞 L))) := by
  refine Finite.of_surjective (fun p : Σ v : S, PlacesOver L (v : HeightOneSpectrum (𝓞 F)) =>
    (⟨p.2.1, p.1.1, p.1.2, p.2.2⟩ : (placesOver S : Set (HeightOneSpectrum (𝓞 L))))) ?_
  rintro ⟨w, v, hv, hw⟩
  exact ⟨⟨⟨v, hv⟩, ⟨w, hw⟩⟩, rfl⟩

theorem bijective_mk_gsPlaceAbove :
    let _ := placesOverAction (L := L) S
    Function.Bijective fun v : S =>
      Quotient.mk (orbitRel (L ≃ₐ[F] L) (placesOver S : Set (HeightOneSpectrum (𝓞 L))))
        (gsPlaceAbove hL ιs v) := by
  let _ := placesOverAction (L := L) S
  constructor
  · intro v v' h
    obtain ⟨τ, hτ⟩ := Quotient.exact h
    have hτ' : τ • (gsPlaceAbove hL ιs v').1 = (gsPlaceAbove hL ιs v).1 := congrArg Subtype.val hτ
    have e1 := eq_placeBelow_of_liesOver (K := F) (gsLocalPlace hL ιs v 1).2
    have e2 := eq_placeBelow_of_liesOver (K := F) (gsLocalPlace hL ιs v' 1).2
    apply Subtype.ext
    rw [e1, e2]
    change placeBelow (gsPlaceAbove hL ιs v).1 = placeBelow (gsPlaceAbove hL ιs v').1
    rw [← hτ', placeBelow_smul]
  · intro ω
    induction ω using Quotient.inductionOn with
    | h w =>
      obtain ⟨v0, hv0, hw⟩ := w.2
      let v : S := ⟨v0, hv0⟩
      obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq (L ≃ₐ[F] L) (gsLocalPlace hL ιs v 1)
        (⟨w.1, hw⟩ : PlacesOver L v0)
      refine ⟨v, Quotient.sound ⟨τ⁻¹, ?_⟩⟩
      apply Subtype.ext
      change τ⁻¹ • w.1 = (gsLocalPlace hL ιs v 1).1
      have := congrArg Subtype.val hτ
      change τ • (gsLocalPlace hL ιs v 1).1 = w.1 at this
      rw [← this, inv_smul_smul]

variable {k N : Type*} [Field k] [AddCommGroup N] [Module k N] [FiniteDimensional k N]
  (σN : Representation k (L ≃ₐ[F] L) N)

theorem finrank_invariants_funPermRep_placesOver [Fintype S] :
    let _ := placesOverAction (L := L) S
    Module.finrank k ((funPermRep k (L ≃ₐ[F] L)
        (placesOver S : Set (HeightOneSpectrum (𝓞 L)))).tprod σN).invariants =
      ∑ v : S, Module.finrank k (Representation.invariants (σN.comp (gsDecompGroup hL ιs v).subtype)) := by
  intro _
  classical
  have := finite_placesOver (L := L) (S := S)
  let _ := Fintype.ofFinite (placesOver S : Set (HeightOneSpectrum (𝓞 L)))
  let _ := Fintype.ofFinite (orbitRel.Quotient (L ≃ₐ[F] L) (placesOver S : Set (HeightOneSpectrum (𝓞 L))))
  rw [finrank_invariants_funPermRep_tprod]
  refine (Fintype.sum_bijective _ (bijective_mk_gsPlaceAbove hL ιs) _ _ fun v => ?_).symm
  have h1 := orbitMover_smul (Γ := L ≃ₐ[F] L) (gsPlaceAbove hL ιs v)
  rw [← stabilizer_gsPlaceAbove hL ιs v]
  conv_lhs => rw [← h1]
  rw [finrank_invariants_stabilizer_smul]

end Finite

end

end GroundTheory.ProfCoh
