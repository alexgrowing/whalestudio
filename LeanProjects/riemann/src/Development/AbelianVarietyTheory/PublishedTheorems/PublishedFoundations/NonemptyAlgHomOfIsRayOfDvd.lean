import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ForallHeckeIdealIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotInjectiveTwoPrimesEqualNormCofinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwoPrimesSameNormOfTrivialFrobenius
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosureFrobeniusElementsEqTop

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.FieldSize

namespace GlobalTheory.Published

def RayClassFieldSt : Prop := GlobalTheory.NT.RayField

theorem rayClassFieldSt_iff_artinIso : RayClassFieldSt ↔
    ∀ (K : Type) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L), IsAbelianGalois K L ∧
        ∃ Art : GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.RayClassGroup 𝔪 ≃* (L ≃ₐ[K] L),
          ∀ (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ 𝔭.asIdeal ∣ 𝔪),
            UnramIn L 𝔭 ∧ IsFrob L 𝔭 (Art (GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals.primeClass 𝔪 𝔭 h)) :=
  GlobalTheory.RayFieldCompare.rayField_iff

theorem rayClassFieldSt_iff_isRayField : RayClassFieldSt ↔
    ∀ (K : Type) [Field K] [NumberField K] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L), GlobalTheory.Mem.Fld.IsRayField K L 𝔪 :=
  GlobalTheory.Mem.Fld.rayField_iff

def RayClassFieldMaximalSt : Prop :=
  ∀ (K L L' : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    [Field L'] [NumberField L'] [Algebra K L'] [IsAbelianGalois K L'] (𝔪 : Ideal (𝓞 K)), 𝔪 ≠ ⊥ → IsRay L 𝔪 →
    (∀ χ : (L' ≃ₐ[K] L') →* ℂˣ, IsModulus L' χ 𝔪) → Nonempty (L' →ₐ[K] L)

end GlobalTheory.Published

namespace GlobalTheory.RayMaximal

open GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals GlobalTheory.RayFieldCompare

variable {K : Type} [Field K] [NumberField K]

theorem eq_of_forall_char {L : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    {σ τ : L ≃ₐ[K] L} (h : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, χ σ = χ τ) : σ = τ := by
  by_contra hne
  letI : CommGroup (L ≃ₐ[K] L) := { (inferInstance : Group (L ≃ₐ[K] L)) with mul_comm := mul_comm' }
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (L ≃ₐ[K] L) ℂ
    (mt mul_inv_eq_one.1 hne)
  exact hχ (by rw [map_mul, map_inv, h χ, mul_inv_cancel])

theorem unramIn_of_isModulus {L : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    {𝔪 : Ideal (𝓞 K)} (h : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, IsModulus L χ 𝔪) {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hp : ¬ 𝔭.asIdeal ∣ 𝔪) : UnramIn L 𝔭 := fun σ hσ => eq_of_forall_char fun χ => by
  by_contra hne
  exact (h χ).2.1 𝔭 hp (heckeVal_eq_zero L χ 𝔭 fun H => hne (by rw [H σ hσ, map_one]))

theorem isModulus_of_isRay {L : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    {𝔪 𝔫 : Ideal (𝓞 K)} (h : IsRay L 𝔪) (hd : 𝔪 ∣ 𝔫) (hn : 𝔫 ≠ ⊥) (χ : (L ≃ₐ[K] L) →* ℂˣ) : IsModulus L χ 𝔫 := by
  obtain ⟨Art, hA⟩ := (clauses_iff L 𝔪).1 h
  refine ⟨hn, fun 𝔭 hp => ?_, ?_⟩
  · have hp' : ¬ 𝔭.asIdeal ∣ 𝔪 := fun h => hp (h.trans hd)
    rw [heckeVal_of_unramIn L χ (hA 𝔭 hp').1 (hA 𝔭 hp').2]
    exact Units.ne_zero _
  · rintro α β ⟨ha, hb, ha', hb', hab, hpos⟩
    have ha0 : Ideal.span {α} ≠ ⊥ := by simpa using ha
    have hb0 : Ideal.span {β} ≠ ⊥ := by simpa using hb
    have hr : RayPair 𝔪 α β := ⟨ha, hb, ha'.of_isCoprime_of_dvd_right hd, hb'.of_isCoprime_of_dvd_right hd,
      Ideal.le_of_dvd hd hab, hpos⟩
    obtain ⟨A, hA'⟩ := exists_integral 𝔪 _ ha0 hr.2.2.1
    obtain ⟨B, hB'⟩ := exists_integral 𝔪 _ hb0 hr.2.2.2.1
    let ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L) := Art.toMonoidHom.comp (QuotientGroup.mk' _)
    rw [heckeIdeal_eq L 𝔪 ψ hA χ _ ha0 A hA', heckeIdeal_eq L 𝔪 ψ hA χ _ hb0 B hB']
    have : (QuotientGroup.mk B : RayClassGroup 𝔪) = QuotientGroup.mk A := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have haK : (α : K) ≠ 0 := by exact_mod_cast ha
      have hbK : (β : K) ≠ 0 := by exact_mod_cast hb
      refine ⟨Units.mk0 ((α : K) / β) (div_ne_zero haK hbK), ⟨α, β, hr, by simp [hbK]⟩, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv, eq_inv_mul_iff_mul_eq]
      apply Units.ext
      rw [Units.val_mul, hA', hB', coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
      congr 1
      exact mul_div_cancel₀ _ hbK
    change ((χ (Art (QuotientGroup.mk A)) : ℂˣ) : ℂ) = χ (Art (QuotientGroup.mk B))
    rw [this]

theorem isFrob_restrictNormal {L M : Type} [Field L] [Field M] [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [Normal K L] {𝔭 : HeightOneSpectrum (𝓞 K)} {σ : M ≃ₐ[K] M} (h : IsFrob M 𝔭 σ) :
    IsFrob L 𝔭 (σ.restrictNormal L) := by
  obtain ⟨P, hP, hPo, hx⟩ := h
  refine ⟨P.under (𝓞 L), inferInstance, inferInstance, fun x => ?_⟩
  have h1 : algebraMap (𝓞 L) (𝓞 M) (σ.restrictNormal L • x) = σ • algebraMap (𝓞 L) (𝓞 M) x :=
    RingOfIntegers.ext (σ.restrictNormal_commutes L x)
  rw [Ideal.mem_under, map_sub, map_pow, h1]
  exact hx _

theorem unramIn_of_tower {L M : Type} [Field L] [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra K M]
    [Algebra L M] [IsScalarTower K L M] [IsGalois K L] [IsGalois K M] {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h : UnramIn M 𝔭) : UnramIn L 𝔭 := by
  rintro σ ⟨P, hP, hPo, hσ⟩
  have := 𝔭.isMaximal
  obtain ⟨⟨Q, hQ, hQo⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 M)))
  have hQo' : Q.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans Q P 𝔭.asIdeal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have : P.IsMaximal := hP.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P)
  have : Q.IsMaximal := hQ.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q)
  have h1 : Q.inertia (M ≃ₐ[K] M) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun τ hτ => h τ ⟨Q, hQ, hQo', hτ⟩
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[K] M) 𝔭.asIdeal Q
  have h3 := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) 𝔭.asIdeal P
  rw [h1, Subgroup.card_bot, Ideal.ramificationIdxIn_eq_ramificationIdx _ Q (M ≃ₐ[K] M),
    Ideal.ramificationIdx_tower P Q] at h2
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (L ≃ₐ[K] L), Nat.eq_one_of_mul_eq_one_right h2.symm,
    Subgroup.card_eq_one] at h3
  exact (Subgroup.eq_bot_iff_forall _).1 h3 σ hσ

theorem closure_isFrob_eq_top (M : Type) [Field M] [NumberField M] [Algebra K M] [IsGalois K M] {𝔪 : Ideal (𝓞 K)}
    (hm : 𝔪 ≠ ⊥) :
    Subgroup.closure {σ : M ≃ₐ[K] M | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔪 ∧ IsFrob M 𝔭 σ} = ⊤ := by
  have hS : {𝔭 : HeightOneSpectrum (𝓞 K) | 𝔭.asIdeal ∣ 𝔪}.Finite := Ideal.finite_factors hm
  refine GlobalTheory.Mem.FieldsEx.closure_frob_eq_top K M _ hS fun F _ _ _ hF σ => ?_
  by_contra hσ
  obtain ⟨T, hT, H⟩ := GlobalTheory.Mem.Fld.exists_two_primes_of_isFrob_one K F σ hσ
  choose P Q hne hP hQ hNP hNQ using fun v : {v // v ∉ {𝔭 : HeightOneSpectrum (𝓞 K) | 𝔭.asIdeal ∣ 𝔪} ∪ T} =>
    H v.1 (fun h => v.2 (Or.inr h)) (hF v.1 fun h => v.2 (Or.inl h))
  have hu : ∀ x : _ × Bool, (cond x.2 (P x.1) (Q x.1)).asIdeal.under (𝓞 K) = x.1.1.asIdeal := by
    rintro ⟨v, _ | _⟩
    exacts [(hQ v).over.symm, (hP v).over.symm]
  refine GlobalTheory.Mem.ZetaPole.not_injective_double_primes K F _ (hS.union hT) (fun x => cond x.2 (P x.1) (Q x.1))
    (fun x y h => ?_) ?_
  · have e : x.1 = y.1 := Subtype.ext (HeightOneSpectrum.ext (by rw [← hu x, ← hu y]; exact congrArg _ (congrArg _ h)))
    obtain ⟨v, a⟩ := x
    obtain ⟨w, b⟩ := y
    obtain rfl : v = w := e
    cases a <;> cases b
    exacts [rfl, absurd h.symm (hne v), absurd h (hne v), rfl]
  · rintro ⟨v, _ | _⟩
    exacts [hNQ v, hNP v]

theorem range_le {L L' M : Type} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    [Field L'] [NumberField L'] [Algebra K L'] [IsAbelianGalois K L'] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] [Algebra L M] [IsScalarTower K L M] [Algebra L' M] [IsScalarTower K L' M] {𝔪 : Ideal (𝓞 K)}
    (hM : Subgroup.closure {σ : M ≃ₐ[K] M | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔪 ∧ IsFrob M 𝔭 σ} = ⊤)
    (h : IsRay L 𝔪) (h' : ∀ χ : (L' ≃ₐ[K] L') →* ℂˣ, IsModulus L' χ 𝔪) :
    (IsScalarTower.toAlgHom K L' M).fieldRange ≤ (IsScalarTower.toAlgHom K L M).fieldRange := by
  obtain ⟨Art, hA⟩ := (clauses_iff L 𝔪).1 h
  letI : CommGroup (L' ≃ₐ[K] L') := { (inferInstance : Group (L' ≃ₐ[K] L')) with mul_comm := mul_comm' }
  choose fr hfr using GlobalTheory.NT.exists_isFrob (K := K) L'
  let ψ' : idealsPrimeTo 𝔪 →* (L' ≃ₐ[K] L') := extend 𝔪 fr
  have hψ' : ∀ 𝔭 hp, UnramIn L' 𝔭 ∧ IsFrob L' 𝔭 (ψ' (primeElt 𝔪 𝔭 hp)) := fun 𝔭 hp =>
    ⟨unramIn_of_isModulus h' hp, by rw [extend_primeElt]; exact hfr 𝔭⟩
  let ψ : idealsPrimeTo 𝔪 →* (L ≃ₐ[K] L) := Art.toMonoidHom.comp (QuotientGroup.mk' _)
  have key : ∀ g : M ≃ₐ[K] M, ∃ J, AlgEquiv.restrictNormalHom L g = ψ J ∧ AlgEquiv.restrictNormalHom L' g = ψ' J := by
    intro g
    have hg : g ∈ Subgroup.closure _ := hM ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨𝔭, hp, hx⟩ := hx
      exact ⟨primeElt 𝔪 𝔭 hp, isFrob_unique L (hA 𝔭 hp).1 (isFrob_restrictNormal hx) (hA 𝔭 hp).2,
        isFrob_unique L' (hψ' 𝔭 hp).1 (isFrob_restrictNormal hx) (hψ' 𝔭 hp).2⟩
    | one => exact ⟨1, by simp, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, h1, h2⟩ := hx
      obtain ⟨b, h3, h4⟩ := hy
      exact ⟨a * b, by rw [map_mul, map_mul, h1, h3], by rw [map_mul, map_mul, h2, h4]⟩
    | inv x _ hx =>
      obtain ⟨a, h1, h2⟩ := hx
      exact ⟨a⁻¹, by rw [map_inv, map_inv, h1], by rw [map_inv, map_inv, h2]⟩
  have hker : ∀ J, ψ J = 1 → ψ' J = 1 := by
    intro J hJ
    have hJ' : J ∈ (rayPrincipal 𝔪).subgroupOf (idealsPrimeTo 𝔪) :=
      (QuotientGroup.eq_one_iff J).1 (Art.map_eq_one_iff.1 hJ)
    obtain ⟨x, ⟨α, β, hr, hx⟩, hxJ⟩ := Subgroup.mem_subgroupOf.1 hJ'
    have ha0 : Ideal.span {α} ≠ ⊥ := by simpa using hr.1
    have hb0 : Ideal.span {β} ≠ ⊥ := by simpa using hr.2.1
    obtain ⟨A, hA'⟩ := exists_integral 𝔪 _ ha0 hr.2.2.1
    obtain ⟨B, hB'⟩ := exists_integral 𝔪 _ hb0 hr.2.2.2.1
    have e : J * B = A := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Units.val_mul, hA', hB', ← hxJ, coe_toPrincipalIdeal,
        FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.spanSingleton_mul_spanSingleton]
      exact congrArg _ hx
    have e' : ψ' A = ψ' B := eq_of_forall_char fun χ => Units.ext (by
      rw [← heckeIdeal_eq L' 𝔪 ψ' hψ' χ _ ha0 A hA', ← heckeIdeal_eq L' 𝔪 ψ' hψ' χ _ hb0 B hB']
      exact (h' χ).2.2 α β hr)
    rw [← e, map_mul] at e'
    exact mul_eq_right.1 e'
  rintro _ ⟨y, rfl⟩
  rw [← IsGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom K L M).fieldRange, IntermediateField.mem_fixedField_iff]
  intro g hg
  obtain ⟨J, h1, h2⟩ := key g
  have h3 : AlgEquiv.restrictNormalHom L g = 1 := AlgEquiv.ext fun x => (algebraMap L M).injective
    ((g.restrictNormal_commutes L x).trans ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ ⟨x, rfl⟩))
  rw [hker J (h1 ▸ h3)] at h2
  exact (g.restrictNormal_commutes L' y).symm.trans (congrArg (algebraMap L' M) (AlgEquiv.congr_fun h2 y))

end GlobalTheory.RayMaximal

namespace GlobalTheory.Published

theorem rayClassFieldMaximalSt_holds : RayClassFieldMaximalSt := by
  intro K L L' _ _ _ _ _ _ _ _ _ _ 𝔪 hm h h'
  let i : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let j : L' →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let e := AlgEquiv.ofInjectiveField i
  let e' := AlgEquiv.ofInjectiveField j
  have : IsGalois K i.fieldRange := IsGalois.of_algEquiv e
  have : IsGalois K j.fieldRange := IsGalois.of_algEquiv e'
  have : FiniteDimensional K i.fieldRange := e.toLinearEquiv.finiteDimensional
  have : FiniteDimensional K j.fieldRange := e'.toLinearEquiv.finiteDimensional
  let M : IntermediateField K (AlgebraicClosure K) := i.fieldRange ⊔ j.fieldRange
  have : IsGalois K M := {}
  have : NumberField M := NumberField.of_module_finite K M
  let i' : L →ₐ[K] M := (IntermediateField.inclusion le_sup_left).comp e.toAlgHom
  let j' : L' →ₐ[K] M := (IntermediateField.inclusion le_sup_right).comp e'.toAlgHom
  let _ := i'.toRingHom.toAlgebra
  let _ := j'.toRingHom.toAlgebra
  have : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun x => (i'.commutes x).symm
  have : IsScalarTower K L' M := IsScalarTower.of_algebraMap_eq fun x => (j'.commutes x).symm
  have hle := GlobalTheory.RayMaximal.range_le (GlobalTheory.RayMaximal.closure_isFrob_eq_top M hm) h h'
  exact ⟨(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L M)).symm.toAlgHom.comp
    ((IntermediateField.inclusion hle).comp (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L' M)).toAlgHom)⟩

theorem nonempty_algHom_of_isRay_of_dvd {K L L' : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsAbelianGalois K L] [Field L'] [NumberField L'] [Algebra K L']
    [IsAbelianGalois K L'] {𝔪 𝔫 : Ideal (𝓞 K)} (hn : 𝔫 ≠ ⊥) (hd : 𝔪 ∣ 𝔫) (h : IsRay L 𝔫) (h' : IsRay L' 𝔪) :
    Nonempty (L' →ₐ[K] L) :=
  rayClassFieldMaximalSt_holds K L L' 𝔫 hn h (GlobalTheory.RayMaximal.isModulus_of_isRay h' hd hn)

theorem nonempty_algHom_iff_isModulus {K L L' : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsAbelianGalois K L] [Field L'] [NumberField L'] [Algebra K L']
    [IsAbelianGalois K L'] {𝔪 : Ideal (𝓞 K)} (hm : 𝔪 ≠ ⊥) (h : IsRay L 𝔪) :
    Nonempty (L' →ₐ[K] L) ↔ ∀ χ : (L' ≃ₐ[K] L') →* ℂˣ, IsModulus L' χ 𝔪 := by
  refine ⟨fun ⟨f⟩ χ => ?_, rayClassFieldMaximalSt_holds K L L' 𝔪 hm h⟩
  let _ := f.toRingHom.toAlgebra
  have : IsScalarTower K L' L := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have hM := GlobalTheory.RayMaximal.isModulus_of_isRay h dvd_rfl hm (χ.comp (AlgEquiv.restrictNormalHom L'))
  have hv : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔪 →
      heckeVal L' χ 𝔭 = heckeVal L (χ.comp (AlgEquiv.restrictNormalHom L')) 𝔭 := fun 𝔭 hp => by
    obtain ⟨σ, hσ⟩ := GlobalTheory.NT.exists_isFrob L 𝔭
    rw [heckeVal_of_unramIn L _ (h.1 𝔭 hp) hσ,
      heckeVal_of_unramIn L' χ (GlobalTheory.RayMaximal.unramIn_of_tower (h.1 𝔭 hp)) (GlobalTheory.RayMaximal.isFrob_restrictNormal hσ)]
    rfl
  have hi : ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔪 →
      heckeIdeal L' χ I = heckeIdeal L (χ.comp (AlgEquiv.restrictNormalHom L')) I := fun I hI hc => by
    classical
    refine finprod_congr fun 𝔭 => ?_
    by_cases hp : 𝔭.asIdeal ∣ 𝔪
    · have h0 : (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors = 0 := by
        by_contra hne
        exact 𝔭.prime.not_isUnit (hc.isUnit_of_dvd' ((Associates.count_ne_zero_iff_dvd hI 𝔭.irreducible).1 hne) hp)
      simp only [h0, pow_zero]
    · rw [hv 𝔭 hp]
  refine ⟨hm, fun 𝔭 hp => hv 𝔭 hp ▸ hM.2.1 𝔭 hp, fun α β hr => ?_⟩
  rw [hi _ (by simpa using hr.1) hr.2.2.1, hi _ (by simpa using hr.2.1) hr.2.2.2.1, hM.2.2 α β hr]

theorem RayClassFieldSt.exists_maximal (H : RayClassFieldSt) (K : Type) [Field K]
    [NumberField K] (𝔪 : Ideal (𝓞 K)) (hm : 𝔪 ≠ ⊥) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsAbelianGalois K L), IsRay L 𝔪 ∧
      ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [IsAbelianGalois K L'],
        (∀ χ : (L' ≃ₐ[K] L') →* ℂˣ, IsModulus L' χ 𝔪) → Nonempty (L' →ₐ[K] L) := by
  obtain ⟨L, _, _, _, _, h⟩ := H K 𝔪 hm
  exact ⟨L, _, inferInstance, _, inferInstance, h, fun L' _ _ _ _ h' => rayClassFieldMaximalSt_holds K L L' 𝔪 hm h h'⟩

end GlobalTheory.Published

end
