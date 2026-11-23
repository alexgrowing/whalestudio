import Development.WeilBound.CoreStatements.PublishedTheorems.GlobalEulerCharacteristic.GaloisCohomologyRatios.ModuleFiniteHomRep
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CoprimeRegular
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummerDefs
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.KummerShaOpen
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global

namespace PositivityTheory.Lit1.GEN.X

local notation "ℚ̄" => AlgebraicClosure ℚ

attribute [local instance 2000] Rep.hV2

variable {K L : FiniteSubfield} [Fact (K ≤ L)] {S : Set (HeightOneSpectrum (𝓞 K.1))} {ℓ : ℕ} [Fact ℓ.Prime]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) [Normal K.1 L.1]
  (hζ : ∃ ζ : L.1, IsPrimitiveRoot ζ ℓ)
  (M : Rep.{0} (ZMod ℓ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Module.Finite (ZMod ℓ) M]
  (hM : ∀ (g : (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) (m : M), M.ρ g m = m)
  (hΓ : Nat.Coprime (Nat.card (L.1 ≃ₐ[K.1] L.1)) ℓ)

noncomputable abbrev rootsRepGal (i : ℕ) :
    Representation (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1)
      (cohomology (Rep.res (PP hL).subtype (gsRootsZMod S ℓ)) i) :=
  (cohomologyConjRep (gsRootsZMod S ℓ) (PP hL) i).comp (gsQuotientGalEquiv hL).symm.toMonoidHom

theorem compactSpace_PP : CompactSpace (PP hL) :=
  compactSpace_openSubgroup (gsOpenSubgroup S hL)

noncomputable abbrev rootsZModEquiv (i : ℕ) :
    cohomology (Rep.res (PP hL).subtype (gsRoots S ℓ)) i ≃+
      cohomology (Rep.res (PP hL).subtype (gsRootsZMod S ℓ)) i :=
  cohomologyAddEquivOfEquiv (A := Rep.res (PP hL).subtype (gsRoots S ℓ))
    (A' := Rep.res (PP hL).subtype (gsRootsZMod S ℓ))
    (zmodRepOfTorsionEquiv ℓ (gsRoots S ℓ) (nsmul_galRootsOfUnity_eq_zero ℓ)) (fun _ _ => rfl) i

theorem rootsRepGal_rootsZModEquiv (i : ℕ) (g : galUnramifiedOutside K.1 ℚ̄ S)
    (y : cohomology (Rep.res (PP hL).subtype (gsRoots S ℓ)) i) :
    rootsRepGal hL i (gsRestrictGal hL g) (rootsZModEquiv hL i y) =
      rootsZModEquiv hL i ((cohomologyConj (gsRoots S ℓ) (PP hL) i g).hom y) := by
  have hq : (gsQuotientGalEquiv hL).symm (gsRestrictGal hL g) =
      (QuotientGroup.mk g : galUnramifiedOutside K.1 ℚ̄ S ⧸ PP hL) := by
    rw [MulEquiv.symm_apply_eq, gsQuotientGalEquiv_mk]
  simp only [rootsRepGal, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hq, cohomologyConjRep_mk]
  exact (cohomologyAddEquivOfEquiv_cohomologyConj (A := gsRoots S ℓ) (A' := gsRootsZMod S ℓ)
    (zmodRepOfTorsionEquiv ℓ (gsRoots S ℓ) (nsmul_galRootsOfUnity_eq_zero ℓ)) (fun _ _ => rfl)
    (PP hL) i g y).symm

theorem rootsZModEquiv_symm_conj (i : ℕ) (g : galUnramifiedOutside K.1 ℚ̄ S)
    (x : cohomology (Rep.res (PP hL).subtype (gsRootsZMod S ℓ)) i) :
    (rootsZModEquiv hL i).symm (rootsRepGal hL i (gsRestrictGal hL g) x) =
      (cohomologyConj (gsRoots S ℓ) (PP hL) i g).hom ((rootsZModEquiv hL i).symm x) := by
  have h1 := rootsRepGal_rootsZModEquiv hL i g ((rootsZModEquiv hL i).symm x)
  exact (AddEquiv.symm_apply_eq _).2
    ((congrArg (fun z => rootsRepGal hL i (gsRestrictGal hL g) z)
      ((rootsZModEquiv hL i).apply_symm_apply x)).symm.trans h1)

theorem finite_cohomology_rootsZMod [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (i : ℕ) (hi : i ≤ 2) : Finite (cohomology (Rep.res (PP hL).subtype (gsRootsZMod S ℓ)) i) := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨f⟩ := nonempty_addEquiv_gsRoots_of_mem S (n := ℓ) fun v hv => by
    by_contra h
    exact hℓS v h hv
  have hcard : Nat.card (Rep.res (PP hL).subtype (gsRoots S ℓ)) = ℓ :=
    (Nat.card_congr f.toEquiv).trans (Nat.card_zmod ℓ)
  have : Finite (Rep.res (PP hL).subtype (gsRoots S ℓ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hℓ.ne_zero)
  have h := finite_cohomology_openSubgroup K S (gsOpenSubgroup S hL)
    (Rep.res (PP hL).subtype (gsRoots S ℓ)) (fun v hv => by
      rw [hcard] at hv
      by_contra h
      exact hℓS v h hv) i hi
  exact Finite.of_equiv _ (rootsZModEquiv hL i).toEquiv

theorem toFun_rootsRepGal_zero (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1))
    [Finite (TorsN (AA hL 0) ℓ)]
    [Finite (cohomology (Rep.res (PP hL).subtype (gsRootsZMod S ℓ)) 0)] :
    d.toFun _ (rootsRepGal hL 0) = dTors hL d 0 := by
  haveI := compactSpace_PP hL
  exact toFun_eq_torsN_zero (PP hL) (gsRestrictGal hL) (gsRestrictGal_surjective hL)
    (ker_gsRestrictGal_le hL) (gsKummer_shortExact S ℓ hℓS) d (rootsRepGal hL 0)
    (rootsZModEquiv hL 0).symm (rootsZModEquiv_symm_conj hL 0)

theorem finrank_tprod_comp_eq {Γ₁ Γ₂ V W : Type*} [Group Γ₁] [Group Γ₂] [AddCommGroup V]
    [Module (ZMod ℓ) V] [AddCommGroup W] [Module (ZMod ℓ) W] (ρ : Representation (ZMod ℓ) Γ₁ V)
    (σ : Representation (ZMod ℓ) Γ₁ W) (e : Γ₂ →* Γ₁) (he : Function.Surjective e) :
    Module.finrank (ZMod ℓ) (Representation.tprod (ρ.comp e) (σ.comp e)).invariants =
      Module.finrank (ZMod ℓ) (Representation.tprod ρ σ).invariants := by
  have h : Representation.tprod (ρ.comp e) (σ.comp e) = (Representation.tprod ρ σ).comp e := rfl
  rw [h, invariants_comp_of_surjective _ _ he]

theorem dN_toFun' {X : Type} [AddCommGroup X] [Module (ZMod ℓ) X] [Finite X]
    (ρX : Representation (ZMod ℓ) (L.1 ≃ₐ[K.1] L.1) X) :
    (dN hL hζ M hM hΓ).toFun X ρX = Module.finrank (ZMod ℓ) (ρX.tprod (nRep hL hζ M hM)).invariants :=
  AdditiveFunction.invariantsTensor_apply _ _ _ _ X ρX

theorem finrank_eq_toFun' (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    (i : ℕ) [Finite (cohomology (Rep.res (PP hL).subtype (gsRootsZMod S ℓ)) i)] :
    (Module.finrank (ZMod ℓ) (cohomology M i) : ℤ) =
      (dN hL hζ M hM hΓ).toFun _ (rootsRepGal hL i) := by
  have hlp : ℓ.Prime := Fact.out
  have hTr : Module.finrank (ZMod ℓ) (gsRootsZMod S ℓ) = 1 := finrank_gsRootsZMod ℓ hℓS
  have hP : (((gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index : ℕ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hlp).1 hcop.symm
  have hkey := finrank_cohomology_eq_finrank_invariants (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M
    (roots_trivial hL hζ) hM hTr hP i
  have h3 := finrank_tprod_comp_eq (cohomologyConjRep (gsRootsZMod S ℓ) (PP hL) i)
    (quotientRep (PP hL) (homRep (gsRootsZMod S ℓ) M)
      (homRep_ρ_of_mem (gsOpenSubgroup S hL) (gsRootsZMod S ℓ) M (roots_trivial hL hζ) hM))
    (gsQuotientGalEquiv hL).symm.toMonoidHom (gsQuotientGalEquiv hL).symm.surjective
  exact (congrArg (fun n : ℕ => (n : ℤ)) (hkey.trans h3.symm)).trans
    (dN_toFun' hL hζ M hM hΓ (rootsRepGal hL i)).symm

theorem toFun_rootsRepGal_one (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (d : AdditiveFunction.{0} ℓ (L.1 ≃ₐ[K.1] L.1))
    [Finite (ModN (AA hL 0) ℓ)] [Finite (TorsN (AA hL 1) ℓ)]
    [Finite (cohomology (Rep.res (PP hL).subtype (gsRootsZMod S ℓ)) 1)] :
    d.toFun _ (rootsRepGal hL 1) = dMod hL d 0 + dTors hL d 1 := by
  haveI := compactSpace_PP hL
  have h := toFun_eq_modN_add_torsN (PP hL) (gsRestrictGal hL) (gsRestrictGal_surjective hL)
    (ker_gsRestrictGal_le hL) (gsKummer_shortExact S ℓ hℓS) d 0 (rootsRepGal hL 1)
    (rootsZModEquiv hL 1).symm (rootsZModEquiv_symm_conj hL 1)
  exact h

theorem h0_eq [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    [Finite (TorsN (AA hL 0) ℓ)] :
    (Module.finrank (ZMod ℓ) (cohomology M 0) : ℤ) = dTors hL (dN hL hζ M hM hΓ) 0 := by
  have := finite_cohomology_rootsZMod hL hℓS 0 (by norm_num)
  exact (finrank_eq_toFun' hL hζ M hM hΓ hℓS hcop 0).trans (toFun_rootsRepGal_zero hL hℓS _)

theorem finrank_H1_euler_formula [Finite S] (hℓS : ∀ v ∉ S, ((ℓ : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
    (hcop : Nat.Coprime (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).index ℓ)
    [Finite (ModN (AA hL 0) ℓ)] [Finite (TorsN (AA hL 1) ℓ)] :
    (Module.finrank (ZMod ℓ) (cohomology M 1) : ℤ) =
      dMod hL (dN hL hζ M hM hΓ) 0 + dTors hL (dN hL hζ M hM hΓ) 1 := by
  have := finite_cohomology_rootsZMod hL hℓS 1 (by norm_num)
  exact (finrank_eq_toFun' hL hζ M hM hΓ hℓS hcop 1).trans (toFun_rootsRepGal_one hL hℓS _)

end PositivityTheory.Lit1.GEN.X
