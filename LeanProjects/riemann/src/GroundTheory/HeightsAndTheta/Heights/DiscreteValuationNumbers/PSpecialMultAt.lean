import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem length_localizedModule_eq_of_surjective {S T : Type*} [CommRing S] [CommRing T]
    (π : S →+* T) (hπ : Function.Surjective π) (Q : Ideal T) [Q.IsPrime] (W : Ideal S) [W.IsPrime]
    (hW : W = Q.comap π) (M N : Type*) [AddCommGroup M] [Module S M] [AddCommGroup N] [Module T N]
    (e : M ≃+ N) (he : ∀ (s : S) (x : M), e (s • x) = π s • e x) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M) =
      Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl N) := by
  let φ : Localization.AtPrime W →+* Localization.AtPrime Q := Localization.localRingHom W Q π hW
  have hmem : ∀ s : S, s ∈ W.primeCompl ↔ π s ∈ Q.primeCompl := fun s => by
    subst hW; rfl
  have hφ : ∀ s : S, φ (algebraMap S _ s) = algebraMap T _ (π s) :=
    Localization.localRingHom_to_map W Q π hW
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨⟨t, u⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl b
    obtain ⟨s, rfl⟩ := hπ t
    obtain ⟨v, hv⟩ := hπ u
    refine ⟨IsLocalization.mk' _ s (⟨v, (hmem v).2 (hv ▸ u.2)⟩ : W.primeCompl), ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hv
  let _ : Algebra (Localization.AtPrime W) (Localization.AtPrime Q) := φ.toAlgebra
  let _ : Module (Localization.AtPrime W) (LocalizedModule Q.primeCompl N) := Module.compHom _ φ
  have _ : IsScalarTower (Localization.AtPrime W) (Localization.AtPrime Q)
      (LocalizedModule Q.primeCompl N) :=
    ⟨fun a b n => mul_smul (φ a) b n⟩
  let _ : Module S (LocalizedModule Q.primeCompl N) := Module.compHom _ (φ.comp (algebraMap S _))
  have _ : IsScalarTower S (Localization.AtPrime W) (LocalizedModule Q.primeCompl N) :=
    ⟨fun s a n => by
      show φ (s • a) • n = φ (algebraMap S _ s) • (φ a • n)
      rw [Algebra.smul_def, map_mul, mul_smul]⟩
  have hsmul : ∀ (s : S) (y : LocalizedModule Q.primeCompl N), s • y = π s • y := fun s y => by
    show φ (algebraMap S _ s) • y = _
    rw [hφ, algebraMap_smul]
  let g : M →ₗ[S] LocalizedModule Q.primeCompl N :=
    { toFun := fun x => LocalizedModule.mkLinearMap Q.primeCompl N (e x)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun s x => by
        rw [RingHom.id_apply, hsmul, he, LinearMap.map_smul] }
  have hg : IsLocalizedModule W.primeCompl g := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
    · have hu : IsUnit (φ (algebraMap S _ (s : S))) :=
        (IsLocalization.map_units (Localization.AtPrime W) s).map φ
      rw [Module.End.isUnit_iff]
      refine ⟨fun y z h => ?_, fun y => ⟨((hu.unit⁻¹ : (Localization.AtPrime Q)ˣ) :
        Localization.AtPrime Q) • y, ?_⟩⟩
      · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply] at h
        exact hu.smul_left_cancel.mp h
      · rw [Module.algebraMap_end_apply]
        show φ (algebraMap S _ (s : S)) • _ = y
        rw [← mul_smul, hu.mul_val_inv, one_smul]
    · induction y using LocalizedModule.induction_on with
      | h n t =>
      obtain ⟨s, hs⟩ := hπ t
      refine ⟨(e.symm n, ⟨s, (hmem s).2 (hs ▸ t.2)⟩), ?_⟩
      show s • LocalizedModule.mk n t = LocalizedModule.mk (e (e.symm n)) 1
      rw [hsmul, hs, AddEquiv.apply_symm_apply, LocalizedModule.smul'_mk]
      exact LocalizedModule.mk_cancel t n
    · have h' : LocalizedModule.mk (e x₁) (1 : Q.primeCompl) = LocalizedModule.mk (e x₂) 1 := h
      obtain ⟨c, hc⟩ := LocalizedModule.mk_eq.mp h'
      obtain ⟨s, hs⟩ := hπ c
      refine ⟨⟨s, (hmem s).2 (hs ▸ c.2)⟩, e.injective ?_⟩
      show e (s • x₁) = e (s • x₂)
      rw [he, he, hs]
      simpa [Submonoid.smul_def] using hc
  let eA := (IsLocalizedModule.iso W.primeCompl g).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)
  rw [eA.length_eq]
  exact Module.length_eq_of_surjective hsurj

theorem SpecialMultAt.proof : SpecialMultAt.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P W _ hW _
  let π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O)
  have hspec : ∀ I : Ideal (MRing ι O), specialIdeal I = I.map π := fun _ => rfl
  have hπ : Function.Surjective π := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π = Ideal.span {C ϖ} := by
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hcm : ∀ I : Ideal (MRing ι O), (specialIdeal I).comap π = I ⊔ Ideal.span {C ϖ} := by
    intro I
    rw [hspec, Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, hker]
  have hWc : W = (specialIdeal W).comap π := by
    rw [hcm]
    exact (sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hW))).symm
  let f : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.Quotient.mk _).comp π
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hπ
  have hkerf : RingHom.ker f = P ⊔ Ideal.span {C ϖ} := by
    rw [← hcm]
    ext x
    simp [f, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  let e := ((Ideal.quotEquivOfEq hkerf.symm).trans (RingHom.quotientKerEquivOfSurjective hf))
  have hemk : ∀ z, e (Ideal.Quotient.mk _ z) = f z := fun z => rfl
  have he : ∀ (s : MRing ι O) (x : MRing ι O ⧸ (P ⊔ Ideal.span {C ϖ})),
      e.toAddEquiv (s • x) = π s • e.toAddEquiv x := by
    intro s x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, hemk]
    simp [f]
    rw [← map_mul]
    rfl
  exact length_localizedModule_eq_of_surjective π hπ (specialIdeal W) W hWc _ _ e.toAddEquiv he

end

end GroundTheory.Heights₂.Heights.NumbersDVR
