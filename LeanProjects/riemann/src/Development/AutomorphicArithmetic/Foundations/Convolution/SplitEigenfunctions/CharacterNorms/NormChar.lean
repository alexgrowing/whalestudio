import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv
import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini
import GroundTheory.GlobalFields.HasseNorm
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Hilbert90AdeleRingTensorQuadratic

noncomputable section

open NumberField IsDedekindDomain GroundTheory.Global Formalism.L2.Host

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.A

local notation "𝔸[" K "]" => AdeleRing (𝓞 K) K

section Ext

variable {G H : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [SigmaCompactSpace G]
  [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]

private theorem exists_extend (R : Subgroup H) (f : R →* ℂˣ) : ∃ g : H →* ℂˣ, ∀ x : R, g x = f x := by
  haveI : DivisibleBy (Additive ℂˣ) ℤ := divisibleByOfSMulRightSurj (Additive ℂˣ) ℤ fun {k} hk x => by
    have hk' : (k : ℂ) ≠ 0 := Int.cast_ne_zero.2 hk
    have hx : ((Additive.toMul x : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    refine ⟨Additive.ofMul (Units.mk0 (Complex.exp (Complex.log (Additive.toMul x : ℂˣ) / k)) (Complex.exp_ne_zero _)), ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    change ((Units.mk0 (Complex.exp (Complex.log (Additive.toMul x : ℂˣ) / k)) (Complex.exp_ne_zero _) ^ k : ℂˣ) : ℂ) = _
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.exp_int_mul, mul_div_cancel₀ _ hk', Complex.exp_log hx]
  have hI := AddCommGrpCat.injective_of_divisible (Additive ℂˣ)
  let i : AddCommGrpCat.of (Additive R) ⟶ AddCommGrpCat.of (Additive H) :=
    AddCommGrpCat.ofHom (MonoidHom.toAdditive R.subtype)
  let j : AddCommGrpCat.of (Additive R) ⟶ AddCommGrpCat.of (Additive ℂˣ) :=
    AddCommGrpCat.ofHom (MonoidHom.toAdditive f)
  haveI : CategoryTheory.Mono i := (AddCommGrpCat.mono_iff_injective i).2 fun a b h => by
    exact Additive.toMul.injective (Subtype.ext (Additive.ofMul.injective h))
  refine ⟨MonoidHom.toAdditive.symm (CategoryTheory.Injective.factorThru j i).hom, fun x => ?_⟩
  have := CategoryTheory.Injective.comp_factorThru j i
  exact congrArg (fun t => t.hom (Additive.ofMul x)) this

theorem exists_lift (n : G →* H) (hn : Continuous n) (ho : IsOpen (n.range : Set H)) (ψ : G →* ℂˣ)
    (hψ : Continuous ψ) (hk : n.ker ≤ ψ.ker) : ∃ χ : H →* ℂˣ, Continuous χ ∧ ∀ g, χ (n g) = ψ g := by
  have hs : Function.Surjective n.rangeRestrict := n.rangeRestrict_surjective
  have hc : Continuous n.rangeRestrict := hn.subtype_mk _
  haveI : LocallyCompactSpace n.range := ho.locallyCompactSpace
  have hop : IsOpenMap n.rangeRestrict := MonoidHom.isOpenMap_of_sigmaCompact _ hs hc
  have hq := hop.isQuotientMap hc hs
  let f : n.range →* ℂˣ := n.rangeRestrict.liftOfSurjective hs ⟨ψ, by rwa [MonoidHom.ker_rangeRestrict]⟩
  have hf : ∀ g, f (n.rangeRestrict g) = ψ g := fun g =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have hfc : Continuous f := hq.continuous_iff.2 (by convert hψ using 1; funext g; exact hf g)
  obtain ⟨χ, hχ⟩ := exists_extend n.range f
  refine ⟨χ, continuous_of_continuousAt_one χ ?_, fun g => ?_⟩
  · have h1 : ContinuousOn χ (n.range : Set H) := by
      rw [continuousOn_iff_continuous_restrict]
      exact hfc.congr fun x => (hχ x).symm
    exact h1.continuousAt (ho.mem_nhds (one_mem _))
  · exact (hχ (n.rangeRestrict g)).trans (hf g)

end Ext

section Field

variable {E : Type} [Field E] [NumberField E]

private theorem gal_eq (hE : Module.finrank ℚ E = 2) :
    ∃ c : E ≃ₐ[ℚ] E, c ≠ 1 ∧ c * c = 1 ∧ ∀ g : E ≃ₐ[ℚ] E, g = 1 ∨ g = c := by
  haveI := (isGalois_isCyclic_of_finrank_eq_two (K := ℚ) (L := E) hE).1
  have hcard : Nat.card (E ≃ₐ[ℚ] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, hE]
  obtain ⟨c, hc, hx⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[ℚ] E)).1 hcard
  have hc1 : c ≠ 1 := hc
  have hall : ∀ g : E ≃ₐ[ℚ] E, g = 1 ∨ g = c := GlobalTheory.AdLat.aut_eq_one_or_of_finrank_two c hE hc1
  refine ⟨c, hc1, ?_, hall⟩
  rcases hall (c * c) with h | h
  · exact h
  · exact absurd (by simpa using h) hc1

theorem exists_galois_quotient_of_ideleNorm_eq_one_quadratic (hE : Module.finrank ℚ E = 2) (z : IdeleGroup E) (hz : ideleNorm ℚ E z = 1) :
    ∃ (c : E ≃ₐ[ℚ] E) (y : IdeleGroup E), z = y * (c • y)⁻¹ := by
  classical
  haveI := (isGalois_isCyclic_of_finrank_eq_two (K := ℚ) (L := E) hE).1
  obtain ⟨c, hc1, hcc, hall⟩ := gal_eq hE
  haveI : FiniteDimensional ℚ E := inferInstance
  have huniv : (Finset.univ : Finset (E ≃ₐ[ℚ] E)) = {1, c} := by
    ext g
    simpa using hall g
  let σ : 𝔸[E] →+* 𝔸[E] := MulSemiringAction.toRingHom (E ≃ₐ[ℚ] E) 𝔸[E] c
  have hσd : ∀ x, σ x = c • x := fun _ => rfl
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    rw [hσd, hσd, smul_smul, hcc, one_smul]
  have hu : (z : 𝔸[E]) * σ z = 1 := by
    have h := ideleEmbedding_ideleNorm (K := ℚ) (L := E) z
    rw [hz, map_one, huniv, Finset.prod_pair hc1.symm, one_smul] at h
    have h2 := congrArg (Units.val) h
    simpa [coe_smul_idele, hσd] using h2.symm
  obtain ⟨a, ha⟩ := AdeleBaseChange.exists_adeleMap_eq_sum_smul (K := ℚ) (L := E) (z : 𝔸[E])
  rw [huniv, Finset.sum_pair hc1.symm, one_smul] at ha
  obtain ⟨e, he, hun⟩ := GlobalTheory.T.exists_idempotent_isUnit_one_add_or_sub_adele ℚ (algebraMap ℚ 𝔸[ℚ] (1 / 2) * a)
  obtain ⟨y, hy⟩ : ∃ y : E, c y ≠ y := by
    by_contra h
    push Not at h
    exact hc1 (AlgEquiv.ext h)
  let am := AdeleBaseChange.adeleMap ℚ E
  have hamσ : ∀ t, σ (am t) = am t := fun t => AdeleBaseChange.smul_adeleMap c t
  have hcy : c (c y) = y := by
    have := congrArg (fun g : E ≃ₐ[ℚ] E => g y) hcc
    simpa using this
  have key : ∃ x : (𝔸[E])ˣ, (x : 𝔸[E]) = z * σ x := by
    refine GlobalTheory.AdLat.hilbert90_involution_of_idempotent_unit σ hσ (z : 𝔸[E]) (algebraMap E 𝔸[E] (y - c y)) (am e)
      (am (algebraMap ℚ 𝔸[ℚ] (1 / 2) * a)) hu ?_ ?_ ?_ ?_ (hamσ e) ?_ ?_
    · rw [hσd, AdeleBaseChange.smul_algebraMap, map_sub, hcy, ← map_neg, neg_sub]
    · exact (IsUnit.mk0 _ (sub_ne_zero.2 hy.symm)).map (algebraMap E 𝔸[E])
    · have := (IsUnit.mk0 (2 : E) two_ne_zero).map (algebraMap E 𝔸[E])
      rwa [map_ofNat] at this
    · rw [← map_mul, he]
    · have h2 : (2 : 𝔸[E]) * am (algebraMap ℚ 𝔸[ℚ] (1 / 2)) = 1 := by
        rw [← map_ofNat am 2, ← map_mul, ← map_ofNat (algebraMap ℚ 𝔸[ℚ]) 2, ← map_mul]
        norm_num
      rw [map_mul, ← mul_assoc, h2, one_mul]
      exact ha.symm
    · have := hun.map am
      simpa only [map_add, map_mul, map_sub, map_one] using this
  obtain ⟨x, hx⟩ := key
  refine ⟨c, x, ?_⟩
  have hcx : (((c • x : IdeleGroup E)) : 𝔸[E]) = σ x := coe_smul_idele c x
  refine eq_mul_inv_iff_mul_eq.2 (Units.ext ?_)
  rw [Units.val_mul, hcx, ← hx]

theorem char_eq_one_of_norm (hE : Module.finrank ℚ E = 2) (ψ : HChar E)
    (h : ∀ (c : E ≃ₐ[ℚ] E) (z : IdeleGroup E), ψ.1 (c • z) = ψ.1 z) (z : IdeleGroup E) (q : ℚˣ)
    (hz : ideleNorm ℚ E z = IdeleGroup.diagonal ℚ q) : ψ.1 z = 1 := by
  obtain ⟨e, he⟩ := (mem_range_norm_iff_diagonal_mem_range_ideleNorm_of_finrank_eq_two hE q).2 ⟨z, hz⟩
  have h1 : ideleNorm ℚ E (z * (IdeleGroup.diagonal E e)⁻¹) = 1 := by
    rw [map_mul, map_inv, ideleNorm_diagonal, he, hz, mul_inv_cancel]
  obtain ⟨c, y, hy⟩ := exists_galois_quotient_of_ideleNorm_eq_one_quadratic hE _ h1
  have h2 : ψ.1 (IdeleGroup.diagonal E e) = 1 := ψ.2.2 e
  have h3 : ψ.1 z = ψ.1 (z * (IdeleGroup.diagonal E e)⁻¹) := by
    rw [map_mul, map_inv, h2, inv_one, mul_one]
  rw [h3, hy, map_mul, map_inv, h, mul_inv_cancel]

theorem normChar_of_inv (hE : Module.finrank ℚ E = 2) (ψ : HChar E)
    (h : ∀ (c : E ≃ₐ[ℚ] E) (z : IdeleGroup E), ψ.1 (c • z) = ψ.1 z) :
    ∃ χ : HChar ℚ, ∀ z : IdeleGroup E, ψ.1 z = χ.1 (ideleNorm ℚ E z) := by
  obtain ⟨hG, hC⟩ := isGalois_isCyclic_of_finrank_eq_two (K := ℚ) (L := E) hE
  haveI : IsAbelianGalois ℚ E := { }
  let ψ' : IdeleClassGroup E →* ℂˣ := QuotientGroup.lift _ ψ.1 (by
    rintro _ ⟨k, rfl⟩
    exact ψ.2.2 k)
  have hψ' : Continuous ψ' := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ψ.2.1
  obtain ⟨χ, hχ, hχn⟩ := exists_lift (ideleClassNorm ℚ E) continuous_ideleClassNorm isOpen_range_ideleClassNorm ψ' hψ' (by
    intro x hx
    obtain ⟨z, rfl⟩ := IdeleClassGroup.mk_surjective E x
    rw [MonoidHom.mem_ker, ideleClassNorm_mk] at hx
    obtain ⟨q, hq⟩ := (QuotientGroup.eq_one_iff _).1 hx
    exact char_eq_one_of_norm hE ψ h z q hq.symm)
  refine ⟨⟨χ.comp (IdeleClassGroup.mk ℚ), hχ.comp (IdeleClassGroup.continuous_mk ℚ), fun k => ?_⟩, fun z => ?_⟩
  · change χ (IdeleClassGroup.mk ℚ (IdeleGroup.diagonal ℚ k)) = 1
    have hm : IdeleClassGroup.mk ℚ (IdeleGroup.diagonal ℚ k) = 1 :=
      (QuotientGroup.eq_one_iff (N := (IdeleGroup.diagonal ℚ).range) _).2 ⟨k, rfl⟩
    rw [hm, map_one]
  · exact (hχn (IdeleClassGroup.mk E z)).symm

end Field

end UpperTheory.ConvolutionTheory.RankTwoDescent.A
