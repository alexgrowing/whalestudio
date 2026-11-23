import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.Places
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.MemShaSubmoduleCohomologyAddEquivOfEquivIff
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CoprimeRegular

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

theorem invariants_eq_of_pointwise {k V Γ₁ Γ₂ H : Type*} [CommRing k] [AddCommGroup V] [Module k V]
    [Group Γ₁] [Group Γ₂] [Group H] (ρ₁ : Representation k Γ₁ V) (ρ₂ : Representation k Γ₂ V)
    (f₁ : H →* Γ₁) (f₂ : H →* Γ₂) (h₁ : Function.Surjective f₁) (h₂ : Function.Surjective f₂)
    (h : ∀ g, ρ₁ (f₁ g) = ρ₂ (f₂ g)) : ρ₁.invariants = ρ₂.invariants := by
  ext x
  simp only [Representation.mem_invariants]
  constructor
  · intro hx γ
    obtain ⟨g, rfl⟩ := h₂ γ
    rw [← h g]
    exact hx _
  · intro hx γ
    obtain ⟨g, rfl⟩ := h₁ γ
    rw [h g]
    exact hx _

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]
  (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
  (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m)
  (hΓ : Nat.Coprime (Nat.card (L.1 ≃ₐ[K.1] L.1)) ℓ)

theorem modNRep_actA_one_apply (g : galUnramifiedOutside K.1 ℚ̄ S) :
    (letI := actA hL 1; modNRep (L.1 ≃ₐ[K.1] L.1) (AA hL 1) ℓ (gsRestrictGal hL g)) =
      gsH1SUnitsModRep ℓ hL (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) g) := by
  refine LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun y => ?_
  have h1 := conjActionOf_smul (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (gsRestrictGal hL) (gsRestrictGal_surjective hL) (ker_gsRestrictGal_le hL) (galSUnitsMax K.1 ℚ̄ S) 1 g y
  have h2 := conjActionOf_smul (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _).le (galSUnitsMax K.1 ℚ̄ S) 1 g y
  exact congrArg Submodule.Quotient.mk (h1.trans h2.symm)

omit [Module.Finite (ZMod ℓ) M] in

theorem nRep_gsRestrictGal (g : galUnramifiedOutside K.1 ℚ̄ S) :
    nRep hL hζ M hM (gsRestrictGal hL g) =
      quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
        (homRep (gsRootsZMod S ℓ) M)
        (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM)
        (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) g) := by
  have h1 : (gsQuotientGalEquiv hL).symm (gsRestrictGal hL g) =
      (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) g := by
    rw [MulEquiv.symm_apply_eq, QuotientGroup.mk'_apply, gsQuotientGalEquiv_mk]
  exact congrArg (quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (homRep (gsRootsZMod S ℓ) M)
    (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM)) h1

omit [Module.Finite (ZMod ℓ) M] in

theorem tprod_gsRestrictGal (g : galUnramifiedOutside K.1 ℚ̄ S) :
    (letI := actA hL 1; (modNRep (L.1 ≃ₐ[K.1] L.1) (AA hL 1) ℓ).tprod (nRep hL hζ M hM)) (gsRestrictGal hL g) =
      ((gsH1SUnitsModRep ℓ hL).tprod
        (quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (homRep (gsRootsZMod S ℓ) M)
          (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM)))
        (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) g) := by
  exact congrArg₂ TensorProduct.map (modNRep_actA_one_apply hL g) (nRep_gsRestrictGal hL hζ M hM g)

theorem dMod_one_eq_pf [Finite (ModN (AA hL 1) ℓ)] :
    dMod hL (dN hL hζ M hM hΓ) 1 =
      Module.finrank (ZMod ℓ) ((gsH1SUnitsModRep ℓ hL).tprod
        (quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (homRep (gsRootsZMod S ℓ) M)
          (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM))).invariants := by
  have hinv : (letI := actA hL 1;
      ((modNRep (L.1 ≃ₐ[K.1] L.1) (AA hL 1) ℓ).tprod (nRep hL hζ M hM)).invariants) =
      ((gsH1SUnitsModRep ℓ hL).tprod
        (quotientRep (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))
          (homRep (gsRootsZMod S ℓ) M)
          (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM))).invariants := by
    exact invariants_eq_of_pointwise _ _ (gsRestrictGal hL)
      (QuotientGroup.mk' (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
      (gsRestrictGal_surjective hL) (QuotientGroup.mk'_surjective _) (tprod_gsRestrictGal hL hζ M hM)
  have e1 : dMod hL (dN hL hζ M hM hΓ) 1 = (Module.finrank (ZMod ℓ) (letI := actA hL 1;
      ((modNRep (L.1 ≃ₐ[K.1] L.1) (AA hL 1) ℓ).tprod (nRep hL hζ M hM)).invariants) : ℤ) :=
    AdditiveFunction.invariantsTensor_apply _ _ _ _ _ _
  exact e1.trans (congrArg (fun p : Submodule (ZMod ℓ) _ => (Module.finrank (ZMod ℓ) p : ℤ)) hinv)

end PositivityTheory.Lit1.GEN.X
