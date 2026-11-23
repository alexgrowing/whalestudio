import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.RayPrincipalIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRayPrincipalIdealsInfOfUnitsPmOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassNumberBounds

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.RayCompositum

open GlobalTheory.NT GlobalTheory.FieldSize GlobalTheory.IndefiniteRowSideFullHecke.RayPrincipalIdeals GlobalTheory.RayFieldCompare GlobalTheory.RayMaximal

variable {K : Type} [Field K] [NumberField K]

set_option autoImplicit false in
open NumberField IsDedekindDomain in
variable {K : Type} [Field K] [NumberField K] in
private theorem heckeIdeal_comp_restrictNormalHom {L M : Type} [Field L]
    [NumberField L] [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] [IsGalois K L] [IsGalois K M] {𝔪 : Ideal (𝓞 K)}
    (hM : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔪 → _root_.GlobalTheory.NT.UnramIn M 𝔭)
    (χ : Gal(L/K) →* ℂˣ) {I : Ideal (𝓞 K)} (hI0 : I ≠ ⊥) (hI : IsCoprime I 𝔪) :
    _root_.GlobalTheory.NT.heckeIdeal M (χ.comp (AlgEquiv.restrictNormalHom L)) I =
      _root_.GlobalTheory.NT.heckeIdeal L χ I := by
  unfold _root_.GlobalTheory.NT.heckeIdeal
  refine finprod_congr fun 𝔭 => ?_
  by_cases hc : (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors = 0
  · simp [hc]
  · have hdvd : 𝔭.asIdeal ∣ I := (Associates.count_ne_zero_iff_dvd hI0 𝔭.irreducible).1 hc
    have hnd : ¬ 𝔭.asIdeal ∣ 𝔪 := by
      intro h
      rw [Ideal.dvd_iff_le] at hdvd h
      exact 𝔭.isPrime.ne_top (top_unique ((Ideal.isCoprime_iff_sup_eq.1 hI).ge.trans (sup_le hdvd h)))
    obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.NT.exists_isFrob M 𝔭
    have hu := hM 𝔭 hnd
    rw [_root_.GlobalTheory.NT.heckeVal_of_unramIn M _ hu hσ,
      _root_.GlobalTheory.NT.heckeVal_of_unramIn L χ (_root_.GlobalTheory.RayMaximal.unramIn_of_tower hu)
        (_root_.GlobalTheory.RayMaximal.isFrob_restrictNormal hσ)]
    rfl

set_option autoImplicit false in
open NumberField IsDedekindDomain in
variable {K : Type} [Field K] [NumberField K] in
private theorem not_isUnit_natCast_of_prime' {F : Type} [Field F] [NumberField F] {q : ℕ}
    (hq : q.Prime) : ¬ IsUnit ((q : 𝓞 F)) := by
  intro h
  have h' := h.map (Algebra.norm ℤ)
  rw [show ((q : ℕ) : 𝓞 F) = algebraMap ℤ (𝓞 F) (q : ℤ) by simp, Algebra.norm_algebraMap] at h'
  have hn : Module.finrank ℤ (𝓞 F) ≠ 0 := Module.finrank_pos.ne'
  rw [isUnit_pow_iff hn, Int.isUnit_iff] at h'
  have := hq.two_le
  omega

set_option autoImplicit false in
open NumberField IsDedekindDomain in
variable {K : Type} [Field K] [NumberField K] in
private theorem isCoprime_of_le_right {R : Type} [CommRing R] {I J J' : Ideal R}
    (h : IsCoprime I J) (hJ : J ≤ J') : IsCoprime I J' := by
  rw [Ideal.isCoprime_iff_sup_eq] at h ⊢
  exact top_unique (h.ge.trans (sup_le_sup_left hJ _))

set_option autoImplicit false in
open NumberField IsDedekindDomain in
variable {K : Type} [Field K] [NumberField K] in
private theorem mem_of_mul_mem_of_isCoprime_span {R : Type} [CommRing R] {J : Ideal R} {y z : R}
    (h : IsCoprime (Ideal.span {y}) J) (hyz : y * z ∈ J) : z ∈ J := by
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.1 h
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hi
  have : z = c * (y * z) + z * j := by linear_combination (-z) * hij
  rw [this]
  exact J.add_mem (J.mul_mem_left _ hyz) (J.mul_mem_left _ hj)

set_option autoImplicit false in
open NumberField IsDedekindDomain in
variable {K : Type} [Field K] [NumberField K] in
private theorem exists_rayPair_inf_of_rayPair (hu : ∀ u : (𝓞 K)ˣ, u = 1 ∨ u = -1)
    {𝔞 𝔟 : Ideal (𝓞 K)} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (ha : 𝔞 ≤ Ideal.span {(q : 𝓞 K)}) (hb : 𝔟 ≤ Ideal.span {(q : 𝓞 K)}) {I : Ideal (𝓞 K)}
    {α β α' β' : 𝓞 K} (h₁ : _root_.GlobalTheory.NT.RayPair 𝔞 α β) (e₁ : I * Ideal.span {β} = Ideal.span {α})
    (h₂ : _root_.GlobalTheory.NT.RayPair 𝔟 α' β') (e₂ : I * Ideal.span {β'} = Ideal.span {α'}) :
    ∃ γ δ, _root_.GlobalTheory.NT.RayPair (𝔞 ⊓ 𝔟) γ δ ∧ I * Ideal.span {δ} = Ideal.span {γ} := by
  obtain ⟨hα0, hβ0, hαc, hβc, hd, hpos⟩ := h₁
  obtain ⟨hα0', hβ0', hαc', hβc', hd', hpos'⟩ := h₂
  have hqtop : Ideal.span {(q : 𝓞 K)} ≠ ⊤ := fun h =>
    not_isUnit_natCast_of_prime' hq (Ideal.span_singleton_eq_top.1 h)
  have hspan : Ideal.span {α * β'} = Ideal.span {α' * β} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
      ← e₁, ← e₂]
    ring
  obtain ⟨u, hu'⟩ := Ideal.span_singleton_eq_span_singleton.1 hspan
  have key : α * β' = α' * β := by
    rcases hu u with rfl | rfl
    · simpa using hu'
    · exfalso
      have hneg : α' * β = -(α * β') := by rw [← hu']; simp
      have h2mem : 2 * α * β' ∈ Ideal.span {(q : 𝓞 K)} := by
        have : 2 * α * β' = β' * (α - β) - β * (α' - β') := by linear_combination hneg
        rw [this]
        exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (ha hd)) (Ideal.mul_mem_left _ _ (hb hd'))
      have h2 : IsCoprime (Ideal.span {(2 : 𝓞 K)}) (Ideal.span {(q : 𝓞 K)}) := by
        rw [Ideal.isCoprime_span_singleton_iff]
        have hz : IsCoprime ((2 : ℕ) : ℤ) (q : ℤ) :=
          Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
        simpa using hz.map (Int.castRingHom (𝓞 K))
      have hc : IsCoprime (Ideal.span {2 * α * β'}) (Ideal.span {(q : 𝓞 K)}) := by
        rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton]
        exact (h2.mul_left (isCoprime_of_le_right hαc ha)).mul_left (isCoprime_of_le_right hβc' hb)
      apply hqtop
      rw [Ideal.isCoprime_iff_sup_eq] at hc
      rwa [sup_eq_right.2 ((Ideal.span_singleton_le_iff_mem _).2 h2mem)] at hc
  have hdb : α - β ∈ 𝔟 := by
    refine mem_of_mul_mem_of_isCoprime_span hβc' ?_
    have : β' * (α - β) = β * (α' - β') := by linear_combination key
    rw [this]
    exact 𝔟.mul_mem_left _ hd'
  have hda : α' - β' ∈ 𝔞 := by
    refine mem_of_mul_mem_of_isCoprime_span hβc ?_
    have : β * (α' - β') = β' * (α - β) := by linear_combination -key
    rw [this]
    exact 𝔞.mul_mem_left _ hd
  obtain ⟨i, hi, a₀, ha₀, hia⟩ := Ideal.isCoprime_iff_exists.1 hβc
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.1 hi
  obtain ⟨i', hi', b₀, hb₀, hib⟩ := Ideal.isCoprime_iff_exists.1 hβc'
  obtain ⟨r', rfl⟩ := Ideal.mem_span_singleton.1 hi'
  set δ : 𝓞 K := β * r + a₀ * (β' * r') with hδdef
  set γ : 𝓞 K := α * r + a₀ * (α' * r') with hγdef
  have hδ1 : δ - 1 ∈ 𝔞 ⊓ 𝔟 := by
    have : δ - 1 = -(a₀ * b₀) := by linear_combination hia + a₀ * hib
    rw [this]
    exact (Ideal.neg_mem_iff _).2 ⟨𝔞.mul_mem_right _ ha₀, 𝔟.mul_mem_left _ hb₀⟩
  have hγδ : γ - δ ∈ 𝔞 ⊓ 𝔟 := by
    have : γ - δ = r * (α - β) + a₀ * r' * (α' - β') := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ⟨hd, hdb⟩) (Ideal.mul_mem_left _ _ ⟨hda, hd'⟩)
  have hγ1 : γ - 1 ∈ 𝔞 ⊓ 𝔟 := by
    have : γ - 1 = (γ - δ) + (δ - 1) := by ring
    rw [this]
    exact Ideal.add_mem _ hγδ hδ1
  have hne : ∀ x : 𝓞 K, x - 1 ∈ 𝔞 ⊓ 𝔟 → x ≠ 0 := by
    rintro x hx rfl
    apply hqtop
    rw [Ideal.eq_top_iff_one]
    have h1 := hx.1
    rw [zero_sub] at h1
    exact ha ((Ideal.neg_mem_iff _).1 h1)
  have hδ0 := hne δ hδ1
  have hγ0 := hne γ hγ1
  have hmul : γ * β = α * δ := by
    simp only [hγdef, hδdef]
    linear_combination (-(a₀ * r')) * key
  refine ⟨γ, δ, ⟨hγ0, hδ0, _root_.GlobalTheory.Mem.RayNo.isCoprime_span hγ1, _root_.GlobalTheory.Mem.RayNo.isCoprime_span hδ1,
    hγδ, fun φ => ?_⟩, ?_⟩
  · have hφ : φ (γ : K) * φ (β : K) = φ (α : K) * φ (δ : K) := by
      have := congrArg (fun z : 𝓞 K => φ (z : K)) hmul
      simpa using this
    have hδφ : φ (δ : K) ≠ 0 := (map_ne_zero φ).2 (by exact_mod_cast hδ0)
    have hβφ : φ (β : K) ≠ 0 := (map_ne_zero φ).2 (by exact_mod_cast hβ0)
    have hδ2 : 0 < φ (δ : K) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hδφ))
    have hβ2 : 0 < φ (β : K) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hβφ))
    have h1 : 0 < (φ (γ : K) * φ (δ : K)) * φ (β : K) ^ 2 := by
      rw [show (φ (γ : K) * φ (δ : K)) * φ (β : K) ^ 2 = (φ (α : K) * φ (β : K)) * φ (δ : K) ^ 2 by
        linear_combination (φ (δ : K) * φ (β : K)) * hφ]
      exact mul_pos (hpos φ) hδ2
    nlinarith
  · have hβI : Ideal.span {β} ≠ 0 := by
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact hβ0
    apply mul_right_cancel₀ hβI
    rw [mul_assoc, mul_comm (Ideal.span {δ}), ← mul_assoc, e₁, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_span_singleton, hmul]

set_option autoImplicit false in
open NumberField IsDedekindDomain in
variable {K : Type} [Field K] [NumberField K] in

theorem _root_.GlobalTheory.RayCompositum.fieldRange_sup_eq_top : ∀ {K H H₁ H₂ : Type} [Field K] [NumberField K] [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] [Field H₁] [NumberField H₁] [Algebra K H₁] [IsAbelianGalois K H₁]
    [Field H₂] [NumberField H₂] [Algebra K H₂] [IsAbelianGalois K H₂], (∀ u : (𝓞 K)ˣ, u = 1 ∨ u = -1) →
    ∀ {𝔞 𝔟 : Ideal (𝓞 K)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → ∀ {q : ℕ}, q.Prime → q ≠ 2 → 𝔞 ≤ Ideal.span {(q : 𝓞 K)} →
    𝔟 ≤ Ideal.span {(q : 𝓞 K)} → _root_.GlobalTheory.FieldSize.IsRay H (𝔞 ⊓ 𝔟) → _root_.GlobalTheory.FieldSize.IsRay H₁ 𝔞 →
    _root_.GlobalTheory.FieldSize.IsRay H₂ 𝔟 → ∀ (f₁ : H₁ →ₐ[K] H) (f₂ : H₂ →ₐ[K] H), f₁.fieldRange ⊔ f₂.fieldRange = ⊤ := by
  intro K H H₁ H₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu 𝔞 𝔟 _ _ q hq hq2 haq hbq hH hH₁ hH₂ f₁ f₂
  letI : Algebra H₁ H := f₁.toRingHom.toAlgebra
  haveI : IsScalarTower K H₁ H := IsScalarTower.of_algebraMap_eq fun x => (f₁.commutes x).symm
  letI : Algebra H₂ H := f₂.toRingHom.toAlgebra
  haveI : IsScalarTower K H₂ H := IsScalarTower.of_algebraMap_eq fun x => (f₂.commutes x).symm
  have hres : ∀ {E : Type} [Field E] [Algebra K E] [Algebra E H] [IsScalarTower K E H] [Normal K E]
      (f : E →ₐ[K] H), (∀ y, algebraMap E H y = f y) → ∀ σ : Gal(H/K),
      (∀ x ∈ f.fieldRange, σ x = x) → AlgEquiv.restrictNormalHom E σ = 1 := by
    intro E _ _ _ _ _ f hf σ hσ
    ext y
    rw [AlgEquiv.one_apply]
    apply f.injective
    have h := AlgEquiv.restrictNormal_commutes σ E y
    rw [hf, hf] at h
    change f (σ.restrictNormal E y) = f y
    rw [h]
    exact hσ _ ⟨y, rfl⟩
  have hfix : ∀ σ : Gal(H/K), (∀ x ∈ f₁.fieldRange ⊔ f₂.fieldRange, σ x = x) → σ = 1 := by
    intro σ hσ
    have r₁ := hres f₁ (fun _ => rfl) σ fun x hx => hσ x (le_sup_left (a := f₁.fieldRange) hx)
    have r₂ := hres f₂ (fun _ => rfl) σ fun x hx => hσ x (le_sup_right (b := f₂.fieldRange) hx)
    obtain ⟨I, hI0, hIc, hχ⟩ := _root_.GlobalTheory.FieldSize.RayDegree.exists_ideal hH σ
    unfold _root_.GlobalTheory.FieldSize.IsRay at hH hH₁ hH₂
    have hIa : IsCoprime I 𝔞 := by
      rw [Ideal.isCoprime_iff_sup_eq] at hIc ⊢
      exact top_unique (hIc.ge.trans (sup_le_sup_left inf_le_left _))
    have hIb : IsCoprime I 𝔟 := by
      rw [Ideal.isCoprime_iff_sup_eq] at hIc ⊢
      exact top_unique (hIc.ge.trans (sup_le_sup_left inf_le_right _))
    have t₁ : ∀ χ : Gal(H₁/K) →* ℂˣ, _root_.GlobalTheory.NT.heckeIdeal H₁ χ I = 1 := by
      intro χ
      rw [← heckeIdeal_comp_restrictNormalHom hH.1 χ hI0 hIc, hχ]
      simp [r₁]
    have t₂ : ∀ χ : Gal(H₂/K) →* ℂˣ, _root_.GlobalTheory.NT.heckeIdeal H₂ χ I = 1 := by
      intro χ
      rw [← heckeIdeal_comp_restrictNormalHom hH.1 χ hI0 hIc, hχ]
      simp [r₂]
    obtain ⟨α, β, hp₁, he₁⟩ := (hH₁.2.2 I hI0 hIa).1 t₁
    obtain ⟨α', β', hp₂, he₂⟩ := (hH₂.2.2 I hI0 hIb).1 t₂
    obtain ⟨γ, δ, hp, he⟩ := exists_rayPair_inf_of_rayPair hu hq hq2 haq hbq hp₁ he₁ hp₂ he₂
    have hall := (hH.2.2 I hI0 hIc).2 ⟨γ, δ, hp, he⟩
    apply _root_.GlobalTheory.RayMaximal.eq_of_forall_char
    intro χ
    have h := hall χ
    rw [hχ χ] at h
    rw [map_one]
    exact Units.val_eq_one.1 h
  have hbot : (f₁.fieldRange ⊔ f₂.fieldRange).fixingSubgroup = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    exact hfix σ fun x hx => hσ ⟨x, hx⟩
  rw [← IsGalois.fixedField_fixingSubgroup (f₁.fieldRange ⊔ f₂.fieldRange), hbot,
    IntermediateField.fixedField_bot]

end GlobalTheory.RayCompositum

end
