import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LengthEqAddEigen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.GsTransport

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω']
  {l : ℕ} [Fact l.Prime]

private theorem mem_sha_iff_res_mem_absolute_sha (D : LData F Ω l) (e : ℤ) (x : H1 (qzTw D e)) :
    x ∈ Sha D e ↔ resH1 (qzTw D e) (toGS Ω _) (continuous_toGS Ω _) x ∈
      ShaAbs ((qzTw D e).comp (toGS Ω _)) (Above F l) := by
  constructor
  · intro hx
    rw [← map_Sha D e]
    exact Submodule.mem_map_of_mem hx
  · intro hx
    rw [← map_Sha D e] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← injective_infl D e hyx]

private theorem pairH1DecompositionMap_qzTw_mem_sha (D : LData F Ω l) (D' : LData F' Ω' l) (e : ℤ) (f : F →+* F') (σ : Ω ≃+* Ω')
    (hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) (φ : G F' Ω' →* G F Ω)
    (hφ : ∀ g x, σ (φ g x) = g (σ x))
    (ψ : GS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F'))) →* GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))))
    (hψ : Continuous ψ) (hc : ∀ g, ψ (toGS Ω' _ g) = toGS Ω _ (φ g))
    (hq : ∀ g m, (LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) (qzTw D e (ψ g) m) = qzTw D' e g (LinearMap.id (R := ℤ_[l]) m))
    (x : H1 (qzTw D e)) (hx : x ∈ Sha D e) :
    pairH1DecompositionMap (qzTw D e) (qzTw D' e) ψ hψ LinearMap.id continuous_id hq x ∈ Sha D' e := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mem_sha_iff_res_mem_absolute_sha] at hx ⊢
  simp only [resH1, pairH1DecompositionMap, Submodule.mapQ_apply] at hx ⊢
  rw [mk_mem_ShaAbs] at hx ⊢
  obtain ⟨hxa, hxb⟩ := hx
  constructor
  · intro v' hv' A' hA'
    obtain ⟨v, A, hA, hab, -, hdec, hine⟩ := placeTransport F Ω F' Ω' f σ hσ φ hφ v' A' hA'
    obtain ⟨m, hm⟩ := hxa v ((hab l).2 hv') A hA
    refine ⟨m, fun g hg => ?_⟩
    have h1 := hm (φ g) ((hdec g).2 hg)
    have h2 := hq (toGS Ω' (↑D'.S : Set (HeightOneSpectrum (𝓞 F'))) g) m
    simp only [LinearMap.id_apply] at h2
    change (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 F))) → QZ l) (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 F))) (φ g)) = qzTw D e (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 F))) (φ g)) m - m at h1
    change LinearMap.id ((z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 F))) → QZ l) (ψ (toGS Ω' (↑D'.S : Set (HeightOneSpectrum (𝓞 F'))) g))) = qzTw D' e (toGS Ω' (↑D'.S : Set (HeightOneSpectrum (𝓞 F'))) g) m - m
    rw [LinearMap.id_apply, hc, h1, ← hc, h2]
  · intro v' hv' A' hA'
    obtain ⟨v, A, hA, hab, -, hdec, hine⟩ := placeTransport F Ω F' Ω' f σ hσ φ hφ v' A' hA'
    obtain ⟨m, hm⟩ := hxb v (fun h => hv' ((hab l).1 h)) A hA
    refine ⟨m, fun g hg => ?_⟩
    have h1 := hm (φ g) ((hine g).2 hg)
    have h2 := hq (toGS Ω' (↑D'.S : Set (HeightOneSpectrum (𝓞 F'))) g) m
    simp only [LinearMap.id_apply] at h2
    change (z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 F))) → QZ l) (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 F))) (φ g)) = qzTw D e (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 F))) (φ g)) m - m at h1
    change LinearMap.id ((z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 F))) → QZ l) (ψ (toGS Ω' (↑D'.S : Set (HeightOneSpectrum (𝓞 F'))) g))) = qzTw D' e (toGS Ω' (↑D'.S : Set (HeightOneSpectrum (𝓞 F'))) g) m - m
    rw [LinearMap.id_apply, hc, h1, ← hc, h2]

end

theorem UpperTheory.V.LDataCardLeFinrank.H1_transport_field_iso :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (D' : LData F' Ω' l) (f : F ≃+* F') (e : ℤ), ∃ Φ : H1 (qzTw D e) ≃ₗ[ℤ_[l]] H1 (qzTw D' e),
      (Sha D e).map Φ.toLinearMap = Sha D' e ∧ ∀ (τ : F ≃+* F) (τ' : F' ≃+* F'), (∀ x, f (τ x) = τ' (f x)) → ∀ x, Φ (UpperTheory.V.galoisActionOnCohomology D e τ x) = UpperTheory.V.galoisActionOnCohomology D' e τ' (Φ x) := by
  intro F Ω _ _ _ _ _ F' Ω' _ _ _ _ _ l _ D D' f e
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : IsAlgClosed Ω' := IsAlgClosure.isAlgClosed F'
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : CharZero Ω' := charZero_of_injective_algebraMap (algebraMap F' Ω').injective
  let σ : Ω ≃+* Ω' := IsAlgClosure.equivOfEquiv Ω Ω' f
  have hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x) :=
    fun x => IsAlgClosure.equivOfEquiv_algebraMap Ω Ω' f x
  obtain ⟨φ, ψ, -, -, hψ, hψs, hφ, hc, hchi⟩ := gsTransport F Ω F' Ω' l D D' f σ hσ
  have hq : ∀ g m, (LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) (qzTw D e ((ψ : GS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F'))) →* GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) g) m) = qzTw D' e g (LinearMap.id (R := ℤ_[l]) m) := by
    intro g m
    simp only [LinearMap.id_apply, UpperTheory.V.qzTw_apply, MonoidHom.coe_coe, hchi]
  have hq' : ∀ g m, (LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) (qzTw D' e ((ψ.symm : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) →* GS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F')))) g) m) = qzTw D e g (LinearMap.id (R := ℤ_[l]) m) := by
    intro g m
    simp only [LinearMap.id_apply, UpperTheory.V.qzTw_apply, MonoidHom.coe_coe, ← hchi, MulEquiv.apply_symm_apply]
  let Φ := pairH1DecompositionMap (qzTw D e) (qzTw D' e) (ψ : GS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F'))) →* GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) hψ LinearMap.id continuous_id hq
  let Ψ := pairH1DecompositionMap (qzTw D' e) (qzTw D e) (ψ.symm : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) →* GS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F')))) hψs LinearMap.id continuous_id hq'
  have hΦΨ : Φ.comp Ψ = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext z g
    simp [Φ, Ψ, pairH1DecompositionMap, compatiblePairCocycles1]
  have hΨΦ : Ψ.comp Φ = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext z g
    simp [Φ, Ψ, pairH1DecompositionMap, compatiblePairCocycles1]
  have hσ' : ∀ x, σ.symm (algebraMap F' Ω' x) = algebraMap F Ω (f.symm x) := by
    intro x
    rw [RingEquiv.symm_apply_eq, hσ, RingEquiv.apply_symm_apply]
  have hφ' : ∀ g x, σ.symm (φ.symm g x) = g (σ.symm x) := by
    intro g x
    have h := hφ (φ.symm g) (σ.symm x)
    rw [MulEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at h
    rw [← h, RingEquiv.symm_apply_apply]
  have hc' : ∀ g, ψ.symm (toGS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 F))) g) = toGS Ω' (↑D'.S : Set (HeightOneSpectrum (𝓞 F'))) (φ.symm g) := by
    intro g
    rw [MulEquiv.symm_apply_eq, hc, MulEquiv.apply_symm_apply]
  refine ⟨LinearEquiv.ofLinear Φ Ψ hΦΨ hΨΦ, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact pairH1DecompositionMap_qzTw_mem_sha D D' e f.toRingHom σ hσ φ.toMonoidHom hφ _ hψ (fun g => hc g) hq x hx
    · intro y hy
      refine ⟨Ψ y, ?_, ?_⟩
      · exact pairH1DecompositionMap_qzTw_mem_sha D' D e f.symm.toRingHom σ.symm hσ' φ.symm.toMonoidHom hφ' _ hψs (fun g => hc' g) hq' y hy
      · exact LinearMap.congr_fun hΦΨ y
  · intro τ τ' hτ x
    obtain ⟨σ1, h1⟩ := UpperTheory.V.exists_isLift (Ω := Ω) τ
    let σ1' : Ω' ≃+* Ω' := σ.symm.trans (σ1.trans σ)
    have h1' : UpperTheory.V.IsLift τ' σ1' := by
      intro y
      obtain ⟨y0, rfl⟩ := f.surjective y
      show σ (σ1 (σ.symm (algebraMap F' Ω' (f y0)))) = algebraMap F' Ω' (τ' (f y0))
      rw [← hσ, RingEquiv.symm_apply_apply, h1, hσ, hτ]
    rw [UpperTheory.V.galois_action_cohomology_eq_conj D e h1, UpperTheory.V.galois_action_cohomology_eq_conj D' e h1']
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨z1, hz1, hz1v⟩ := UpperTheory.V.exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h1 z
    simp only [LinearEquiv.ofLinear_apply]
    rw [hz1]
    have hΦmk : ∀ w, Φ (Submodule.Quotient.mk w) = Submodule.Quotient.mk (compatiblePairCocycles1 (qzTw D e) (qzTw D' e) _ hψ LinearMap.id continuous_id hq w) := fun w => rfl
    rw [hΦmk, hΦmk]
    obtain ⟨z2, hz2, hz2v⟩ := UpperTheory.V.exists_cocycle_h1TwistConjByLift_mk_eq_mk D' e h1' (compatiblePairCocycles1 (qzTw D e) (qzTw D' e) _ hψ LinearMap.id continuous_id hq z)
    rw [hz2]
    congr 1
    apply Subtype.ext
    funext g'
    rw [hz2v]
    show LinearMap.id ((z1 : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 F))) → QZ l) (ψ g')) = UpperTheory.V.twScal l σ1' e • LinearMap.id ((z : GS Ω (↑D.S : Set (HeightOneSpectrum (𝓞 F))) → QZ l) (ψ (UpperTheory.V.conjGS D' h1' g')))
    rw [LinearMap.id_apply, LinearMap.id_apply, hz1v]
    have htw : UpperTheory.V.twScal l σ1' e = UpperTheory.V.twScal l σ1 e := by
      unfold UpperTheory.V.twScal
      rw [KStar.TotallyRealRoots.cyclotomicCharacter_conj (l := l) σ σ1 σ1' (fun x => by simp [σ1'])]
    have hsurj : Function.Surjective (toGS Ω' (↑D'.S : Set (HeightOneSpectrum (𝓞 F')))) := QuotientGroup.mk'_surjective _
    have hconj : UpperTheory.V.conjGS D h1 (ψ g') = ψ (UpperTheory.V.conjGS D' h1' g') := by
      obtain ⟨g0, rfl⟩ := hsurj g'
      rw [hc, UpperTheory.V.conjGS_toGS, UpperTheory.V.conjGS_toGS, hc]
      congr 1
      have key : ∀ y, φ g0 y = σ.symm (g0 (σ y)) := fun y => by rw [RingEquiv.eq_symm_apply, hφ]
      ext x
      apply σ.injective
      rw [hφ, UpperTheory.V.conjGal_apply, UpperTheory.V.conjGal_apply, key]
      simp [σ1']
    rw [htw, hconj]
