import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published

namespace GlobalTheory.RayTopGalois

theorem count_comap {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [DecidableEq (Associates (Ideal R))] [∀ p : Associates (Ideal R), Decidable (Irreducible p)]
    [DecidableEq (Associates (Ideal S))] [∀ p : Associates (Ideal S), Decidable (Irreducible p)]
    (e : R ≃+* S) (p : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    (Associates.mk (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal).count (Associates.mk (I.comap e.symm)).factors =
      (Associates.mk p.asIdeal).count (Associates.mk I).factors := by
  have hI' : I.comap e.symm ≠ ⊥ := by
    rw [← Ideal.map_comap_of_equiv]
    exact fun h => hI ((Ideal.map_eq_bot_iff_of_injective e.injective).1 h)
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI') (HeightOneSpectrum.associates_irreducible _),
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI) (HeightOneSpectrum.associates_irreducible _),
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le]
  have : (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal = p.asIdeal.map (e : R →+* S) := by
    rw [Ideal.map_comap_of_equiv]; rfl
  rw [this, ← Ideal.map_pow, Ideal.map_comap_of_equiv]
  exact Ideal.comap_le_comap_iff_of_surjective e.symm e.symm.surjective _ _

section Transport

variable {K K' N : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field N] [NumberField N]
  [Algebra K N] [Algebra K' N] (s : K ≃+* K') (hs : ∀ x, algebraMap K' N (s x) = algebraMap K N x)

def autEquiv : (N ≃ₐ[K] N) ≃* (N ≃ₐ[K'] N) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    obtain ⟨y, rfl⟩ := s.surjective x
    rw [hs]; exact σ.commutes y
  invFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => by
    rw [← hs]; exact σ.commutes _
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

abbrev primeEquiv : HeightOneSpectrum (𝓞 K) ≃ HeightOneSpectrum (𝓞 K') :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s)

include hs in
omit [NumberField K] [NumberField K'] [NumberField N] in
theorem liesOver_iff (𝔭 : HeightOneSpectrum (𝓞 K)) (P : Ideal (𝓞 N)) :
    P.LiesOver (primeEquiv s 𝔭).asIdeal ↔ P.LiesOver 𝔭.asIdeal := by
  have h : ∀ x : 𝓞 K, algebraMap (𝓞 K') (𝓞 N) (RingOfIntegers.mapRingEquiv s x) = algebraMap (𝓞 K) (𝓞 N) x :=
    fun x => RingOfIntegers.ext (hs x)
  have h2 : ∀ x : 𝓞 K, RingOfIntegers.mapRingEquiv s x ∈ (primeEquiv s 𝔭).asIdeal ↔ x ∈ 𝔭.asIdeal := fun x => by
    change (RingOfIntegers.mapRingEquiv s).symm (RingOfIntegers.mapRingEquiv s x) ∈ 𝔭.asIdeal ↔ _
    rw [RingEquiv.symm_apply_apply]
  refine ⟨fun ⟨H⟩ => ⟨Ideal.ext fun x => ?_⟩, fun ⟨H⟩ => ⟨Ideal.ext fun x => ?_⟩⟩
  · rw [← h2, H, Ideal.mem_under, Ideal.mem_under, h]
  · obtain ⟨y, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective x
    rw [h2, H, Ideal.mem_under, Ideal.mem_under, h]

theorem absNorm_primeEquiv (𝔭 : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm (primeEquiv s 𝔭).asIdeal = Ideal.absNorm 𝔭.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv s) ?_).toEquiv).symm
  exact (Ideal.map_comap_of_equiv _).symm

omit [NumberField N] in
theorem isFrob_iff' (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : N ≃ₐ[K] N) :
    IsFrob N (primeEquiv s 𝔭) (autEquiv s hs σ) ↔ IsFrob N 𝔭 σ := by
  unfold IsFrob
  rw [absNorm_primeEquiv]
  exact exists_congr fun P => and_congr_right' (and_congr (liesOver_iff s hs 𝔭 P) Iff.rfl)

omit [NumberField K] [NumberField K'] [NumberField N] in
theorem inInertia_iff' (𝔭 : HeightOneSpectrum (𝓞 K)) (σ : N ≃ₐ[K] N) :
    InInertia N (primeEquiv s 𝔭) (autEquiv s hs σ) ↔ InInertia N 𝔭 σ :=
  exists_congr fun P => and_congr_right' (and_congr (liesOver_iff s hs 𝔭 P) Iff.rfl)

theorem heckeVal_transport [IsGalois K N] [IsGalois K' N] (χ : (N ≃ₐ[K'] N) →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    heckeVal N χ (primeEquiv s 𝔭) = heckeVal N (χ.comp (autEquiv s hs).toMonoidHom) 𝔭 := by
  by_cases h : ∀ τ, InInertia N (primeEquiv s 𝔭) τ → χ τ = 1
  · obtain ⟨σ, hσ⟩ := exists_isFrob N 𝔭
    rw [heckeVal_eq N _ 𝔭 (fun τ hτ => h _ ((inInertia_iff' s hs 𝔭 τ).2 hτ)) hσ,
      heckeVal_eq N χ _ h ((isFrob_iff' s hs 𝔭 σ).2 hσ)]
    rfl
  · rw [heckeVal_eq_zero N χ _ h, heckeVal_eq_zero N _ 𝔭 fun h' => h fun τ hτ => ?_]
    obtain ⟨σ, rfl⟩ := (autEquiv s hs).surjective τ
    exact h' σ ((inInertia_iff' s hs 𝔭 σ).1 hτ)

theorem heckeIdeal_transport [IsGalois K N] [IsGalois K' N] (χ : (N ≃ₐ[K'] N) →* ℂˣ) {a : 𝓞 K} (ha : a ≠ 0) :
    heckeIdeal N χ (Ideal.span {RingOfIntegers.mapRingEquiv s a}) =
      heckeIdeal N (χ.comp (autEquiv s hs).toMonoidHom) (Ideal.span {a}) := by
  have e : Ideal.span {RingOfIntegers.mapRingEquiv s a} =
      (Ideal.span {a}).comap (RingOfIntegers.mapRingEquiv s).symm := by
    rw [← Ideal.map_comap_of_equiv, Ideal.map_span, Set.image_singleton]
    rfl
  unfold heckeIdeal
  rw [← finprod_comp_equiv (primeEquiv s)]
  refine finprod_congr fun 𝔭 => ?_
  rw [heckeVal_transport s hs, e, count_comap _ _ (by simpa using ha)]

include hs in

theorem isModulus_top_transport [IsGalois K N] [IsGalois K' N] (h : ∀ χ : (N ≃ₐ[K] N) →* ℂˣ, IsModulus N χ ⊤)
    (χ : (N ≃ₐ[K'] N) →* ℂˣ) : IsModulus N χ ⊤ := by
  have hc : ∀ J : Ideal (𝓞 K), IsCoprime J ⊤ := fun J => by
    rw [← Ideal.one_eq_top]; exact isCoprime_one_right
  refine ⟨top_ne_bot, fun 𝔭 _ => ?_, fun α β hr => ?_⟩
  · obtain ⟨𝔮, rfl⟩ := (primeEquiv s).surjective 𝔭
    rw [heckeVal_transport s hs]
    exact (h _).2.1 𝔮 fun h => 𝔮.isPrime.ne_top (top_le_iff.1 (Ideal.le_of_dvd h))
  · obtain ⟨a, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective α
    obtain ⟨b, rfl⟩ := (RingOfIntegers.mapRingEquiv s).surjective β
    have ha : a ≠ 0 := fun h => hr.1 (by rw [h, map_zero])
    have hb : b ≠ 0 := fun h => hr.2.1 (by rw [h, map_zero])
    rw [heckeIdeal_transport s hs χ ha, heckeIdeal_transport s hs χ hb]
    refine (h _).2.2 a b ⟨ha, hb, hc _, hc _, trivial, fun φ => ?_⟩
    have := hr.2.2.2.2.2 (φ.comp s.symm.toRingHom)
    change 0 < φ (s.symm (s a)) * φ (s.symm (s b)) at this
    rwa [s.symm_apply_apply, s.symm_apply_apply] at this

include hs in
omit [NumberField K] [NumberField K'] in
theorem isAbelianGalois_transport [CharZero K] [IsAbelianGalois K N] : IsAbelianGalois K' N := by
  have : IsGalois K' N := IsGalois.of_equiv_equiv (f := s) (g := RingEquiv.refl N) (RingHom.ext hs)
  have : IsMulCommutative (N ≃ₐ[K'] N) := ⟨⟨fun a b => by
    obtain ⟨a, rfl⟩ := (autEquiv s hs).surjective a
    obtain ⟨b, rfl⟩ := (autEquiv s hs).surjective b
    rw [← map_mul, ← map_mul, mul_comm' a b]⟩⟩
  exact {}

end Transport

theorem exists_extension {L N : Type} [Field L] [NumberField L] [Field N] [NumberField N] [i : Algebra L N]
    (h : IsRayField L N ⊤) (s : L ≃+* L) :
    ∃ f : N →+* N, ∀ x, f (algebraMap L N x) = algebraMap L N (s x) := by
  have hab := h.1
  let j : Algebra L N := ((@algebraMap L N _ _ i).comp s.symm.toRingHom).toAlgebra
  have hs : ∀ x, @algebraMap L N _ _ j (s x) = @algebraMap L N _ _ i x := fun x =>
    congrArg (@algebraMap L N _ _ i) (s.symm_apply_apply x)
  have hab' := @isAbelianGalois_transport L L N _ _ _ _ i j s hs _ hab
  have hm := @GlobalTheory.RayMaximal.isModulus_of_isRay L _ _ N _ _ i hab ⊤ ⊤ h.2 dvd_rfl top_ne_bot
  obtain ⟨f⟩ := @rayClassFieldMaximalSt_holds L N N _ _ _ _ i hab _ _ j hab' ⊤ top_ne_bot h.2
    (@isModulus_top_transport L L N _ _ _ _ _ _ i j s hs (@IsAbelianGalois.toIsGalois _ _ _ _ i hab)
      (@IsAbelianGalois.toIsGalois _ _ _ _ j hab') hm)
  refine ⟨@AlgHom.toRingHom L N N _ _ _ j i f, fun x => ?_⟩
  rw [← hs]
  exact @AlgHom.commutes L N N _ _ _ j i f (s x)

theorem isGalois_of_isRayField_top : ∀ (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field N]
    [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L],
    GlobalTheory.Mem.Fld.IsRayField L N ⊤ → IsGalois K N := by
  intro K L N _ _ _ _ _ _ _ _ _ _ _ h
  have hab := h.1
  refine IsGalois.of_fixedField_eq_bot K N (eq_bot_iff.2 fun x hx => ?_)
  rw [IntermediateField.mem_fixedField_iff] at hx
  obtain ⟨y, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := L) x).2 fun σ =>
    hx (σ.restrictScalars K) trivial
  obtain ⟨z, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) y).2 fun s => by
    obtain ⟨f, hf⟩ := exists_extension h s.toRingEquiv
    let g : N →ₐ[K] N := { f with
      commutes' := fun k => by
        rw [IsScalarTower.algebraMap_apply K L N]
        exact (hf _).trans (congrArg _ (s.commutes k)) }
    exact (algebraMap L N).injective ((hf y).symm.trans
      (hx (AlgEquiv.ofBijective g (Algebra.IsAlgebraic.algHom_bijective g)) trivial))
  rw [← IsScalarTower.algebraMap_apply]
  exact IntermediateField.algebraMap_mem _ z

end GlobalTheory.RayTopGalois

end
