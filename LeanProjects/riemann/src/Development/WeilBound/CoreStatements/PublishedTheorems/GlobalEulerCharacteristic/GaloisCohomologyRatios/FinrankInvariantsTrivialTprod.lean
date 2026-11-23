import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.Places

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global
open scoped TensorProduct

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

section Helpers

variable {k Γ Δ V : Type*} [CommRing k] [Group Γ] [Group Δ] [AddCommGroup V] [Module k V]

theorem invariants_comp_surjective (σ : Representation k Γ V) (f : Δ →* Γ)
    (hf : Function.Surjective f) : Representation.invariants (σ.comp f) = σ.invariants := by
  ext n
  simp only [Representation.mem_invariants, MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · intro h g
    obtain ⟨d, rfl⟩ := hf g
    exact h d
  · intro h d
    exact h (f d)

theorem invariants_comp_subtype_top (σ : Representation k Γ V) (R : Subgroup Γ)
    (hR : ∀ γ, γ ∈ R) : Representation.invariants (σ.comp R.subtype) = σ.invariants :=
  invariants_comp_surjective σ R.subtype fun γ => ⟨⟨γ, hR γ⟩, rfl⟩

theorem invariants_comp_equiv_map (σ : Representation k Γ V) (e : Γ ≃* Δ) (R : Subgroup Γ)
    (D : Subgroup Δ) (hD : R.map e.toMonoidHom = D) :
    Representation.invariants ((σ.comp e.symm.toMonoidHom).comp D.subtype) =
      Representation.invariants (σ.comp R.subtype) := by
  ext n
  simp only [Representation.mem_invariants, MonoidHom.coe_comp, Function.comp_apply,
    Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
  constructor
  · intro h r
    have hm : e r.1 ∈ D := by
      rw [← hD]
      exact ⟨r.1, r.2, rfl⟩
    have := h ⟨e r.1, hm⟩
    simpa using this
  · intro h d
    have hm : d.1 ∈ R.map e.toMonoidHom := by rw [hD]; exact d.2
    obtain ⟨r, hr, hrd⟩ := hm
    have := h ⟨r, hr⟩
    simp only at this
    rw [← hrd]
    simpa using this

theorem finrank_invariants_trivial_tprod {k Γ N : Type} [CommRing k] [Group Γ] [AddCommGroup N]
    [Module k N] (σ : Representation k Γ N) :
    Module.finrank k ((Representation.trivial k Γ (ULift.{0} k)).tprod σ).invariants =
      Module.finrank k σ.invariants := by
  let eT : ULift.{0} k ⊗[k] N ≃ₗ[k] N :=
    (TensorProduct.congr ULift.moduleEquiv (LinearEquiv.refl _ _)).trans (TensorProduct.lid _ _)
  refine finrank_invariants_eq_of_linearEquiv _ eT fun g x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a n => simp [eT, Representation.tprod_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end Helpers

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]
  (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
  (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m)
  (hΓ : Nat.Coprime (Nat.card (L.1 ≃ₐ[K.1] L.1)) ℓ)

theorem global_dual_invariants_finrank (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal) :
    (Module.finrank (ZMod ℓ) (dualRep (gsRootsZMod S ℓ) M).ρ.invariants : ℤ) = (dN hL hζ M hM hΓ).one := by
  classical
  have hT : Module.finrank (ZMod ℓ) (gsRootsZMod S ℓ) = 1 := finrank_gsRootsZMod ℓ hℓS
  have hN := homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM
  have hfin : Finite (galUnramifiedOutside K.1 ℚ̄ S ⧸ PP hL) :=
    Finite.of_equiv _ (gsQuotientGalEquiv hL).symm.toEquiv
  have : Fintype ((QuotientGroup.mk' (PP hL)).comp (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S))).range :=
    Fintype.ofFinite _
  have hD : (Fintype.card ((QuotientGroup.mk' (PP hL)).comp
      (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S))).range : ZMod ℓ) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have h1 := Subgroup.card_subgroup_dvd_card ((QuotientGroup.mk' (PP hL)).comp
      (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S))).range
    have h2 : Nat.card (galUnramifiedOutside K.1 ℚ̄ S ⧸ PP hL) = Nat.card (L.1 ≃ₐ[K.1] L.1) :=
      Nat.card_congr (gsQuotientGalEquiv hL).toEquiv
    rw [h2] at h1
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : ℓ.Prime)).1 hΓ.symm (dvd_trans hdvd h1)
  have key := finrank_invariants_dualRep_comp (gsRootsZMod S ℓ) M hT (PP hL) hN
    (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S)) hD
  have hsurj : ∀ γ, γ ∈ ((QuotientGroup.mk' (PP hL)).comp
      (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S))).range := fun γ => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (PP hL) γ
    exact ⟨x, rfl⟩
  have e1 : Representation.invariants ((dualRep (gsRootsZMod S ℓ) M).ρ.comp
      (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S))) = (dualRep (gsRootsZMod S ℓ) M).ρ.invariants :=
    invariants_comp_surjective (dualRep (gsRootsZMod S ℓ) M).ρ
      (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S)) Function.surjective_id
  have e2 : Representation.invariants ((quotientRep (PP hL) (homRep (gsRootsZMod S ℓ) M) hN).comp
      ((QuotientGroup.mk' (PP hL)).comp (MonoidHom.id (galUnramifiedOutside K.1 ℚ̄ S))).range.subtype) =
      (quotientRep (PP hL) (homRep (gsRootsZMod S ℓ) M) hN).invariants :=
    invariants_comp_subtype_top _ _ hsurj
  have key2 : Module.finrank (ZMod ℓ) (dualRep (gsRootsZMod S ℓ) M).ρ.invariants =
      Module.finrank (ZMod ℓ) (quotientRep (PP hL) (homRep (gsRootsZMod S ℓ) M) hN).invariants :=
    ((congrArg (fun p : Submodule (ZMod ℓ) _ => Module.finrank (ZMod ℓ) p) e1).symm.trans key).trans
      (congrArg (fun p : Submodule (ZMod ℓ) _ => Module.finrank (ZMod ℓ) p) e2)
  rw [key2]
  have e3 : Representation.invariants (nRep hL hζ M hM) =
      (quotientRep (PP hL) (homRep (gsRootsZMod S ℓ) M) hN).invariants := by
    unfold nRep
    exact invariants_comp_surjective _ _ (gsQuotientGalEquiv hL).symm.surjective
  have e4 := finrank_invariants_trivial_tprod (nRep hL hζ M hM)
  have e4' := e4.trans (congrArg (fun p : Submodule (ZMod ℓ) _ => Module.finrank (ZMod ℓ) p) e3)
  have e5 : (dN hL hζ M hM hΓ).one = (Module.finrank (ZMod ℓ)
      ((Representation.trivial (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1) (ULift.{0} (ZMod ℓ))).tprod
        (nRep hL hζ M hM)).invariants : ℤ) :=
    AdditiveFunction.invariantsTensor_apply _ _ _ _ _ _
  exact (congrArg (Nat.cast : ℕ → ℤ) e4'.symm).trans e5.symm

theorem local_dual_invariants_sum [Fintype S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) :
    ∑ v : S, (Module.finrank (ZMod ℓ) (Representation.invariants
          ((dualRep (gsRootsZMod S ℓ) M).ρ.comp (gsFinFamily S ιs v).toMonoidHom)) : ℤ) =
      dPlaces (S := S) (dN hL hζ M hM hΓ) := by
  classical
  have hT : Module.finrank (ZMod ℓ) (gsRootsZMod S ℓ) = 1 := finrank_gsRootsZMod ℓ hℓS
  have hN := homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM
  have hfin : Finite (galUnramifiedOutside K.1 ℚ̄ S ⧸ PP hL) :=
    Finite.of_equiv _ (gsQuotientGalEquiv hL).symm.toEquiv
  have hv : ∀ v : S, Module.finrank (ZMod ℓ) (Representation.invariants
      ((dualRep (gsRootsZMod S ℓ) M).ρ.comp (gsFinFamily S ιs v).toMonoidHom)) =
      Module.finrank (ZMod ℓ) (Representation.invariants
        ((nRep hL hζ M hM).comp (gsDecompGroup hL ιs v).subtype)) := by
    intro v
    have : Fintype ((QuotientGroup.mk' (PP hL)).comp (gsFinFamily S ιs v).toMonoidHom).range :=
      Fintype.ofFinite _
    have hD : (Fintype.card ((QuotientGroup.mk' (PP hL)).comp
        (gsFinFamily S ιs v).toMonoidHom).range : ZMod ℓ) ≠ 0 := by
      rw [← Nat.card_eq_fintype_card, Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have h1 := Subgroup.card_subgroup_dvd_card ((QuotientGroup.mk' (PP hL)).comp
        (gsFinFamily S ιs v).toMonoidHom).range
      have h2 : Nat.card (galUnramifiedOutside K.1 ℚ̄ S ⧸ PP hL) = Nat.card (L.1 ≃ₐ[K.1] L.1) :=
        Nat.card_congr (gsQuotientGalEquiv hL).toEquiv
      rw [h2] at h1
      exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : ℓ.Prime)).1 hΓ.symm (dvd_trans hdvd h1)
    have key := finrank_invariants_dualRep_comp (gsRootsZMod S ℓ) M hT (PP hL) hN
      (gsFinFamily S ιs v).toMonoidHom hD
    have e := invariants_comp_equiv_map (quotientRep (PP hL) (homRep (gsRootsZMod S ℓ) M) hN)
      (gsQuotientGalEquiv hL) _ _ (map_range_gsQuotientGalEquiv hL ιs v)
    exact key.trans (congrArg (fun p : Submodule (ZMod ℓ) _ => Module.finrank (ZMod ℓ) p) e.symm)
  have hsum : (letI := placesOverAction (L := L.1) S
      Module.finrank (ZMod ℓ) ((funPermRep (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1)
        (placesOver S : Set (HeightOneSpectrum (𝓞 L.1)))).tprod (nRep hL hζ M hM)).invariants) =
      ∑ v : S, Module.finrank (ZMod ℓ) (Representation.invariants
        ((nRep hL hζ M hM).comp (gsDecompGroup hL ιs v).subtype)) :=
    finrank_invariants_funPermRep_placesOver (hL := hL) (ιs := ιs) (σN := nRep hL hζ M hM)
  have hP : dPlaces (S := S) (dN hL hζ M hM hΓ) = ((letI := placesOverAction (L := L.1) S
      Module.finrank (ZMod ℓ) ((funPermRep (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1)
        (placesOver S : Set (HeightOneSpectrum (𝓞 L.1)))).tprod (nRep hL hζ M hM)).invariants : ℕ) : ℤ) :=
    rfl
  refine Eq.trans ?_ hP.symm
  refine Eq.trans ?_ (congrArg (Nat.cast : ℕ → ℤ) hsum).symm
  refine Eq.trans ?_ (Nat.cast_sum _ _).symm
  exact Finset.sum_congr rfl fun v _ => congrArg (Nat.cast : ℕ → ℤ) (hv v)
end PositivityTheory.Lit1.GEN.X
