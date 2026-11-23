import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published
open scoped Pointwise

namespace GlobalTheory.FrobTransfer

theorem pow_smul_sub_mem {G S : Type} [Group G] [CommRing S] [MulSemiringAction G S] {P : Ideal S} {σ : G} {q : ℕ}
    (h : ∀ x, σ • x - x ^ q ∈ P) (n : ℕ) (x : S) : σ ^ n • x - x ^ q ^ n ∈ P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := h (σ ^ n • x)
    rw [← Ideal.Quotient.eq] at h1 ih ⊢
    rw [pow_succ', mul_smul, h1, map_pow, ih, ← map_pow, ← pow_mul, pow_succ]

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem orderOf_eq_inertiaDeg {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) {P : Ideal (𝓞 L)} [hP : P.IsPrime]
    [hPo : P.LiesOver 𝔭.asIdeal] {σ : L ≃ₐ[K] L} (h : ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P) :
    orderOf σ = P.inertiaDeg (𝓞 K) := by
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have : P.IsMaximal := hP.isMaximal hne
  let := Ideal.Quotient.field P
  let := Fintype.ofFinite (𝓞 L ⧸ P)
  have hc : Fintype.card (𝓞 L ⧸ P) = Ideal.absNorm 𝔭.asIdeal ^ P.inertiaDeg (𝓞 K) := by
    rw [Ideal.absNorm_pow_inertiaDeg, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hq : 1 < Ideal.absNorm 𝔭.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm 𝔭
  have hf := Ideal.inertiaDeg_pos P (𝓞 K)
  apply le_antisymm
  · refine orderOf_le_of_pow_eq_one hf (hu _ ⟨P, hP, hPo, fun x => ?_⟩)
    have h1 := pow_smul_sub_mem h (P.inertiaDeg (𝓞 K)) x
    rw [← Ideal.Quotient.eq] at h1 ⊢
    rw [h1, map_pow, ← hc, FiniteField.pow_card]
  · have ho : 0 < orderOf σ := orderOf_pos σ
    have hlt : 1 < Ideal.absNorm 𝔭.asIdeal ^ orderOf σ := Nat.one_lt_pow ho.ne' hq
    have h2 := (FiniteField.forall_pow_eq_one_iff (𝓞 L ⧸ P) (Ideal.absNorm 𝔭.asIdeal ^ orderOf σ - 1)).1 fun u => by
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 L ⧸ P)
      have h1 := pow_smul_sub_mem h (orderOf σ) x
      rw [pow_orderOf_eq_one, one_smul, ← Ideal.Quotient.eq, map_pow, hx] at h1
      have h3 : u ^ Ideal.absNorm 𝔭.asIdeal ^ orderOf σ = u := Units.ext (by rw [Units.val_pow_eq_pow_val, ← h1])
      rw [pow_sub u hlt.le, h3, pow_one, mul_inv_cancel]
    have h4 := Nat.le_of_dvd (by omega) h2
    rw [hc] at h4
    exact (Nat.pow_le_pow_iff_right hq).1 (by omega)

omit [NumberField K] [NumberField L] in

theorem card_inertia {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) (P : Ideal (𝓞 L)) [hP : P.IsPrime]
    [hPo : P.LiesOver 𝔭.asIdeal] : Nat.card (P.inertia (L ≃ₐ[K] L)) = 1 := by
  have h1 : P.inertia (L ≃ₐ[K] L) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun τ hτ => hu τ ⟨P, hP, hPo, hτ⟩
  rw [h1, Subgroup.card_bot]

theorem stabilizer_eq [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) {P : Ideal (𝓞 L)}
    [hP : P.IsPrime] [hPo : P.LiesOver 𝔭.asIdeal] {σ : L ≃ₐ[K] L}
    (h : ∀ x : 𝓞 L, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ P) :
    Subgroup.zpowers σ = MulAction.stabilizer (L ≃ₐ[K] L) P := by
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have hF : IsArithFrobAt (𝓞 K) σ P := by
    unfold IsArithFrobAt AlgHom.IsArithFrobAt
    rw [← hPo.over, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact h
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hF.mem_stabilizer) ?_
  rw [Ideal.card_stabilizer_eq_card_inertia_mul_finrank (G := L ≃ₐ[K] L) 𝔭.asIdeal P, card_inertia hu, one_mul,
    Nat.card_zpowers, orderOf_eq_inertiaDeg hu h]

theorem map_eq_prod [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn L 𝔭) :
    𝔭.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)) = ∏ P : 𝔭.asIdeal.primesOver (𝓞 L), P.1 := by
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  rw [Ideal.map_algebraMap_eq_finsetProd_pow 𝔭.ne_bot, ← Finset.prod_set_coe]
  refine Finset.prod_congr rfl fun ⟨P, hP, hPo⟩ _ => ?_
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal P (L ≃ₐ[K] L),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) 𝔭.asIdeal P, card_inertia hu, pow_one]

theorem heckeIdeal_prod {ι : Type} (χ : (L ≃ₐ[K] L) →* ℂˣ) (s : Finset ι) (f : ι → Ideal (𝓞 K))
    (hf : ∀ i, f i ≠ 0) : heckeIdeal L χ (∏ i ∈ s, f i) = ∏ i ∈ s, heckeIdeal L χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.NT.Model.heckeIdeal_top L χ
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      GlobalTheory.NT.Model.heckeIdeal_mul L χ (hf a) (Finset.prod_ne_zero_iff.2 fun i _ => hf i), ih]

variable {N : Type} [Field N] [NumberField N] [Algebra L N] [Algebra K N] [IsScalarTower K L N]

omit [NumberField K] [NumberField L] [NumberField N] in
theorem algebraMap_restrict_smul [Normal K L] (g : N ≃ₐ[K] N) (x : 𝓞 L) :
    algebraMap (𝓞 L) (𝓞 N) (AlgEquiv.restrictNormalHom L g • x) = g • algebraMap (𝓞 L) (𝓞 N) x :=
  RingOfIntegers.ext (g.restrictNormal_commutes L x)

omit [NumberField K] [NumberField L] [NumberField N] in
theorem under_inv_smul [Normal K L] (g : N ≃ₐ[K] N) (Q : Ideal (𝓞 N)) :
    (g⁻¹ • Q).under (𝓞 L) = (AlgEquiv.restrictNormalHom L g)⁻¹ • Q.under (𝓞 L) := by
  ext x
  rw [Ideal.mem_under, Ideal.mem_inv_pointwise_smul_iff, Ideal.mem_inv_pointwise_smul_iff, Ideal.mem_under,
    algebraMap_restrict_smul]

omit [NumberField K] [NumberField L] [NumberField N] in

theorem exists_restrictScalars [Normal K L] (g : N ≃ₐ[K] N) (hg : AlgEquiv.restrictNormalHom L g = 1) :
    ∃ τ : N ≃ₐ[L] N, τ.restrictScalars K = g := by
  refine ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun x => ?_, rfl⟩
  have := g.restrictNormal_commutes L x
  rw [show g.restrictNormal L = 1 from hg] at this
  exact this.symm

omit [NumberField K] [NumberField L] [NumberField N] in

theorem unramIn_top {𝔭 : HeightOneSpectrum (𝓞 K)} (hu : UnramIn N 𝔭) (P : HeightOneSpectrum (𝓞 L))
    [P.asIdeal.LiesOver 𝔭.asIdeal] : UnramIn N P := by
  rintro τ ⟨Q, hQ, hQo, hτ⟩
  have := hu (τ.restrictScalars K) ⟨Q, hQ, Ideal.LiesOver.trans Q P.asIdeal 𝔭.asIdeal, hτ⟩
  exact AlgEquiv.ext fun x => DFunLike.congr_fun this x

omit [NumberField K] [NumberField L] [NumberField N] in

theorem minimalPeriod_eq [Normal K L] (σ : N ≃ₐ[K] N)
    (c : (N ≃ₐ[K] N) ⧸ (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker) :
    Function.minimalPeriod (σ • ·) c = orderOf (AlgEquiv.restrictNormalHom L σ) := by
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective c
  refine Nat.dvd_right_iff_eq.1 fun n => ?_
  rw [← MulAction.pow_smul_eq_iff_minimalPeriod_dvd, orderOf_dvd_iff_pow_eq_one, MulAction.Quotient.smul_mk,
    QuotientGroup.eq, MonoidHom.mem_ker, smul_eq_mul, map_mul, map_inv, map_mul, inv_mul_eq_one, mul_eq_right,
    map_pow]

theorem heckeIdeal_under [IsGalois K L] [IsGalois K N] [IsGalois L N] {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hu : UnramIn N 𝔭) {Q : Ideal (𝓞 N)} [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] {σ : N ≃ₐ[K] N}
    (h : ∀ x : 𝓞 N, σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q) (χ : (N ≃ₐ[L] N) →* ℂˣ) (t : N ≃ₐ[K] N)
    (τ : N ≃ₐ[L] N) (hτ : τ.restrictScalars K = t⁻¹ * σ ^ (Q.under (𝓞 L)).inertiaDeg (𝓞 K) * t) :
    heckeIdeal N χ ((t⁻¹ • Q).under (𝓞 L)) = (χ τ : ℂˣ) := by
  let P : HeightOneSpectrum (𝓞 L) :=
    ⟨(t⁻¹ • Q).under (𝓞 L), inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _⟩
  have : P.asIdeal.LiesOver 𝔭.asIdeal := inferInstanceAs (((t⁻¹ • Q).under (𝓞 L)).LiesOver 𝔭.asIdeal)
  have := P.isPrime
  change heckeIdeal N χ P.asIdeal = _
  rw [GlobalTheory.NT.Model.heckeIdeal_prime]
  refine heckeVal_of_unramIn N χ (unramIn_top hu P) ⟨t⁻¹ • Q, inferInstance, ⟨rfl⟩, fun x => ?_⟩
  rw [← Ideal.absNorm_pow_inertiaDeg 𝔭.asIdeal P.asIdeal,
    ← Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal P.asIdeal (L ≃ₐ[K] L),
    Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal (Q.under (𝓞 L)) (L ≃ₐ[K] L), Ideal.mem_inv_pointwise_smul_iff,
    show τ • x = τ.restrictScalars K • x from rfl, hτ, smul_sub, smul_pow', ← mul_smul, mul_assoc,
    mul_inv_cancel_left, mul_smul]
  exact pow_smul_sub_mem h _ _

theorem heckeIdeal_map_eq_transfer : ∀ (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field N] [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L] [IsGalois K N] [IsAbelianGalois L N] (𝔭 : HeightOneSpectrum (𝓞 K)), GlobalTheory.NT.UnramIn N 𝔭 → ∀ σ : N ≃ₐ[K] N, GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ (χ : (N ≃ₐ[L] N) →* ℂˣ) (φ : (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker →* ℂˣ), (∀ (τ : N ≃ₐ[L] N) (h : τ.restrictScalars K ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L).ker), φ ⟨τ.restrictScalars K, h⟩ = χ τ) → GlobalTheory.NT.heckeIdeal N χ (𝔭.asIdeal.map (algebraMap (𝓞 K) (𝓞 L))) = ((MonoidHom.transfer φ σ : ℂˣ) : ℂ) := by
  intro K L N _ _ _ _ _ _ _ _ _ _ _ _ _ 𝔭 hu σ ⟨Q, hQ, hQo, h⟩ χ φ hφ
  classical
  have huL : UnramIn L 𝔭 := GlobalTheory.RayMaximal.unramIn_of_tower hu
  let r := AlgEquiv.restrictNormalHom (F := K) (K₁ := N) L
  have hL : ∀ x : 𝓞 L, r σ • x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q.under (𝓞 L) := fun x => by
    rw [Ideal.mem_under, map_sub, map_pow, algebraMap_restrict_smul]
    exact h _
  have hst := stabilizer_eq huL hL
  have hord := orderOf_eq_inertiaDeg huL hL
  let := Fintype.ofFinite (Quotient (MulAction.orbitRel (Subgroup.zpowers σ) ((N ≃ₐ[K] N) ⧸ r.ker)))
  let e : Quotient (MulAction.orbitRel (Subgroup.zpowers σ) ((N ≃ₐ[K] N) ⧸ r.ker)) → 𝔭.asIdeal.primesOver (𝓞 L) :=
    fun q => ⟨(q.out.out⁻¹ • Q).under (𝓞 L), inferInstance, inferInstance⟩
  have key : ∀ s t : N ≃ₐ[K] N, (s⁻¹ • Q).under (𝓞 L) = (t⁻¹ • Q).under (𝓞 L) ↔
      MulAction.orbitRel (Subgroup.zpowers σ) ((N ≃ₐ[K] N) ⧸ r.ker) (s : (N ≃ₐ[K] N) ⧸ r.ker) t := fun s t => by
    rw [under_inv_smul, under_inv_smul, inv_smul_eq_iff, ← mul_smul, eq_comm, ← MulAction.mem_stabilizer_iff, ← hst,
      MulAction.orbitRel_apply, MulAction.mem_orbit_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨⟨σ ^ k, k, rfl⟩, ?_⟩
      change ((σ ^ k * t : N ≃ₐ[K] N) : (N ≃ₐ[K] N) ⧸ r.ker) = s
      rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_zpow, hk, inv_mul_cancel_right,
        inv_mul_cancel]
    · rintro ⟨⟨_, k, rfl⟩, hk⟩
      change ((σ ^ k * t : N ≃ₐ[K] N) : (N ≃ₐ[K] N) ⧸ r.ker) = s at hk
      rw [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_zpow, inv_mul_eq_one] at hk
      exact ⟨k, by rw [← hk, mul_inv_cancel_right]⟩
  have he : Function.Bijective e := by
    constructor
    · intro q q' hq
      have := (key _ _).1 (congrArg Subtype.val hq)
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
      exact Quotient.out_equiv_out.1 this
    · rintro ⟨P, hP, hPo⟩
      obtain ⟨γ, hγ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝔭.asIdeal (Q.under (𝓞 L)) P (L ≃ₐ[K] L)
      obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) N γ⁻¹
      refine ⟨Quotient.mk _ (g : (N ≃ₐ[K] N) ⧸ r.ker), Subtype.ext ?_⟩
      refine ((key _ g).2 ?_).trans (by rw [under_inv_smul, hg, inv_inv, hγ])
      rw [QuotientGroup.out_eq']
      exact Quotient.mk_out _
  rw [map_eq_prod huL, heckeIdeal_prod χ _ _ fun P => ?_, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    Units.coe_prod]
  · refine (Fintype.prod_bijective e he _ _ fun q => ?_).symm
    obtain ⟨τ, hτ⟩ := exists_restrictScalars (L := L) _ (QuotientGroup.out_conj_pow_minimalPeriod_mem r.ker σ q.out)
    rw [heckeIdeal_under hu h χ q.out.out τ (by rw [hτ, minimalPeriod_eq, hord]),
      ← hφ τ (hτ ▸ QuotientGroup.out_conj_pow_minimalPeriod_mem r.ker σ q.out)]
    exact congrArg (fun x => ((φ x : ℂˣ) : ℂ)) (Subtype.ext hτ.symm)
  · have := P.2.2
    exact Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _

end GlobalTheory.FrobTransfer
