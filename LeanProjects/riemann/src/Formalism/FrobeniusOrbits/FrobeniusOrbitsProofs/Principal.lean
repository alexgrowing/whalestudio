import Mathlib
import Formalism.FrobeniusOrbits.HostDiffSupport
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp

open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Principal

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem bE_mem_KinE (ζ a b : L) : bE ζ a b ∈ KinE ζ a b := by
  first
  | exact IntermediateField.mem_adjoin_simple_self ℚ (bE ζ a b)
  | (unfold KinE; exact IntermediateField.mem_adjoin_simple_self ℚ _)

theorem galE_restrict_mem_Psi (σ : hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b) :
    galE e ζ a b (σ.restrictScalars ℚ) ∈ Psi e := by
  have h1 : (σ.restrictScalars ℚ) (bE ζ a b) = bE ζ a b := by
    first
    | exact σ.commutes ⟨bE ζ a b, bE_mem_KinE ζ a b⟩
    | simpa using σ.commutes ⟨bE ζ a b, bE_mem_KinE ζ a b⟩
  rw [Psi, MonoidHom.mem_ker]
  simp [chD, galE, sgn, h1]

theorem inertia_trivial (hH : HostHyp q d) (h : IsLayer (e + 2) q d ζ a b)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] (hP0 : P ≠ ⊥)
    (h2 : ((2 : ℤ) : 𝓞 (hostE ζ a b)) ∉ P) (hq : ((q : ℤ) : 𝓞 (hostE ζ a b)) ∉ P)
    (σ : hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b)
    (hσ : ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) : σ = 1 := by
  have hqd := hH.toHypOdd
  set σ' : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b := σ.restrictScalars ℚ with hσ'
  have hin : ∀ x : 𝓞 (hostE ζ a b), σ' • x - x ∈ P := hσ
  suffices hs : σ' = 1 from AlgEquiv.ext fun x => DFunLike.congr_fun hs x
  obtain ⟨p, hp, hPp⟩ :=
    (Ideal.isPrime_int_iff.mp (Ideal.IsPrime.under ℤ P)).resolve_left (Ideal.under_ne_bot ℤ hP0)
  have hlo : P.LiesOver (span {(p : ℤ)}) := ⟨hPp.symm⟩
  have hpmem : ((p : ℤ) : 𝓞 (hostE ζ a b)) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := by rw [hPp]; exact mem_span_singleton_self _
    simpa [Ideal.under_def] using this
  have hp2 : p ≠ 2 := by rintro rfl; exact h2 (by exact_mod_cast hpmem)
  have hpq : p ≠ q := by rintro rfl; exact hq hpmem
  by_cases hpd : p = d
  · subst hpd
    rcases ((hostInertia e q p hH L ζ a b h σ').2.2 P).mp hin with h1 | h1
    · exact (galE_eq_one_iff hqd h σ').mp h1
    · exfalso
      have hm := galE_restrict_mem_Psi (e := e) σ
      rw [mem_Psi_iff] at hm
      rw [← hσ', h1] at hm
      exact Inertia.neg_one_ne_one' hm
  · have : Fact p.Prime := ⟨hp⟩
    exact ((hostFrob_of hostGalois hostGalSpec e q d hqd L ζ a b h p hp2 hpq hpd P).2.2 σ').mp hin

end Principal

open Principal

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem hostDiffSupport : HostDiffSupport := by
  intro e q d hH L _ _ ζ a b h P hP hdvd
  have hqd := hH.toHypOdd
  by_contra hcon
  push Not at hcon
  obtain ⟨h2, hq⟩ := hcon
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    have := differentIdeal_ne_bot (A := 𝓞 (KinE ζ a b)) (B := 𝓞 (hostE ζ a b))
    exact this (by rwa [← Ideal.zero_eq_bot, zero_dvd_iff] at hdvd)
  have hEgal : IsGalois ℚ (hostE ζ a b) := hostE_isGalois hqd h
  have hKgal : IsGalois (KinE ζ a b) (hostE ζ a b) := IsGalois.tower_top_of_isGalois ℚ _ _
  have : IsGaloisGroup (hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b) (𝓞 (KinE ζ a b))
      (𝓞 (hostE ζ a b)) := IsGaloisGroup.of_isFractionRing _ _ _ (KinE ζ a b) (hostE ζ a b)
  have hpr : (P.under (𝓞 (KinE ζ a b))).IsPrime := Ideal.IsPrime.under _ P
  have hcard := card_inertia_eq_ramificationIdxIn (G := hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b)
    (P.under (𝓞 (KinE ζ a b))) P
  rw [ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 (KinE ζ a b))) P
    (hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b)] at hcard
  have h1 : Nat.card (P.inertia (hostE ζ a b ≃ₐ[KinE ζ a b] hostE ζ a b)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, one_mem _⟩⟩⟩
    rw [inertia_trivial hH h P hP0 h2 hq x.1 (AddSubgroup.mem_inertia.mp x.2),
      inertia_trivial hH h P hP0 h2 hq y.1 (AddSubgroup.mem_inertia.mp y.2)]
  rw [h1] at hcard
  exact (dvd_differentIdeal_iff.mp hdvd) ((Ideal.ramificationIdx_eq_one_iff).mp hcard.symm)

namespace Principal

section Invariance

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem comm_of (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (σ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b))
    (τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b)) (x : (hostE ζ a b)) : σ (τ x) = τ (σ x) := by
  have hc : σ * τ.restrictScalars ℚ = τ.restrictScalars ℚ * σ := by
    apply galE_injective hqd h
    rw [galE_mul hqd h, galE_mul hqd h, mul_comm]
  have h1 := congrArg (fun φ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b) => φ x) hc
  first
  | exact h1
  | simpa using h1

theorem comm_symm (σ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b))
    (hc : ∀ (τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b)) (x : (hostE ζ a b)), σ (τ x) = τ (σ x))
    (τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b)) (x : (hostE ζ a b)) : σ.symm (τ x) = τ (σ.symm x) := by
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, hc, AlgEquiv.apply_symm_apply]

theorem sum_comm (σ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b))
    (hc : ∀ (τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b)) (x : (hostE ζ a b)), σ (τ x) = τ (σ x)) (w : (hostE ζ a b)) :
    σ (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ w) = ∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ (σ w) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun τ _ => hc τ w

theorem one_ne (ζ a b : L) : (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0 := one_ne_zero

theorem mem_dual_iff (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (y : (hostE ζ a b)) :
    y ∈ FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b) (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ↔
      ∀ x : 𝓞 (hostE ζ a b), IsIntegral ℤ (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ (y * x)) := by
  haveI := hostE_isGalois hqd h
  haveI : IsGalois (KinE ζ a b) (hostE ζ a b) :=
    IsGalois.tower_top_of_isGalois ℚ (KinE ζ a b) (hostE ζ a b)
  have htr : ∀ w : hostE ζ a b, algebraMap (KinE ζ a b) (hostE ζ a b)
      (Algebra.trace (KinE ζ a b) (hostE ζ a b) w) =
      ∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ w :=
    fun w => by
      first
      | exact trace_eq_sum_automorphisms w
      | exact Algebra.trace_eq_sum_automorphisms w
      | exact IsGalois.trace_eq_sum_automorphisms w
  have hint : ∀ t : KinE ζ a b, IsIntegral ℤ (algebraMap (KinE ζ a b) (hostE ζ a b) t) ↔
      t ∈ (algebraMap (𝓞 (KinE ζ a b)) (KinE ζ a b)).range := by
    intro t
    rw [isIntegral_algebraMap_iff (algebraMap (KinE ζ a b) (hostE ζ a b)).injective]
    constructor
    · intro ht
      exact ⟨⟨t, ht⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact s.isIntegral_coe
  rw [FractionalIdeal.mem_dual (one_ne ζ a b)]
  constructor
  · intro hy x
    have hx : ((x : hostE ζ a b)) ∈ (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) := by
      rw [FractionalIdeal.mem_one_iff]
      exact ⟨x, rfl⟩
    have h2 := hy _ hx
    rw [Algebra.traceForm_apply, ← hint, htr] at h2
    exact h2
  · intro hy w hw
    rw [FractionalIdeal.mem_one_iff] at hw
    obtain ⟨x, rfl⟩ := hw
    rw [Algebra.traceForm_apply, ← hint, htr]
    exact hy x

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

theorem mem_diff_iff (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (z : 𝓞 (hostE ζ a b)) :
    z ∈ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) ↔
      ∀ y : (hostE ζ a b), (∀ x : 𝓞 (hostE ζ a b), IsIntegral ℤ (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ (y * x))) →
        IsIntegral ℤ ((z : (hostE ζ a b)) * y) := by
  have key : ∀ w : hostE ζ a b,
      w ∈ (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ↔ IsIntegral ℤ w := by
    intro w
    rw [FractionalIdeal.mem_one_iff]
    constructor
    · rintro ⟨w', rfl⟩
      exact w'.isIntegral_coe
    · intro hw
      exact ⟨⟨w, hw⟩, rfl⟩
  have hz : z ∈ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) ↔
      (z : hostE ζ a b) ∈ ((differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) :
        FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b))) := by
    rw [FractionalIdeal.mem_coeIdeal]
    constructor
    · intro hz
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z', hz', he⟩
      have he' : z' = z := IsFractionRing.injective (𝓞 (hostE ζ a b)) (hostE ζ a b) he
      rwa [he'] at hz'
  have hd0 : FractionalIdeal.dual (𝓞 (KinE ζ a b)) (KinE ζ a b)
      (1 : FractionalIdeal (𝓞 (hostE ζ a b))⁰ (hostE ζ a b)) ≠ 0 := by
    first
    | exact FractionalIdeal.dual_ne_zero (one_ne ζ a b)
    | exact FractionalIdeal.dual_ne_zero _ _ (one_ne ζ a b)
  rw [hz]
  first
  | rw [coeIdeal_differentIdeal (𝓞 (KinE ζ a b)) (KinE ζ a b) (hostE ζ a b) (𝓞 (hostE ζ a b))]
  | rw [coeIdeal_differentIdeal (𝓞 (KinE ζ a b)) (KinE ζ a b)]
  | rw [coeIdeal_differentIdeal]
  rw [FractionalIdeal.mem_inv_iff hd0]
  constructor
  · intro hmem y hy
    exact (key _).mp (hmem y ((mem_dual_iff hqd h y).mpr hy))
  · intro hmem y hy
    exact (key _).mpr (hmem y ((mem_dual_iff hqd h y).mp hy))

private theorem coe_powerSeries_smul_eq_smul (σ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b)) (z : 𝓞 (hostE ζ a b)) :
    ((σ • z : 𝓞 (hostE ζ a b)) : hostE ζ a b) = σ (z : hostE ζ a b) := by
  first
  | rfl
  | simp

theorem dual_smul (σ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b))
    (hc : ∀ (τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b)) (x : (hostE ζ a b)), σ (τ x) = τ (σ x)) (y : (hostE ζ a b))
    (hy : ∀ x : 𝓞 (hostE ζ a b), IsIntegral ℤ (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ (y * x))) :
    ∀ x : 𝓞 (hostE ζ a b), IsIntegral ℤ (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ (σ y * x)) := by
  intro x
  have key : (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b), τ (σ y * x)) =
      σ (∑ τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b),
        τ (y * ((σ⁻¹ • x : 𝓞 (hostE ζ a b)) : hostE ζ a b))) := by
    rw [sum_comm σ hc, map_mul, coe_powerSeries_smul_eq_smul, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  rw [key]
  exact (hy (σ⁻¹ • x)).map ((σ : (hostE ζ a b) →+* (hostE ζ a b)).toIntAlgHom)

theorem diff_smul_mem (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (σ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b))
    (hc : ∀ (τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b)) (x : (hostE ζ a b)), σ (τ x) = τ (σ x)) (z : 𝓞 (hostE ζ a b))
    (hz : z ∈ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) : σ • z ∈ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) := by
  rw [mem_diff_iff hqd h] at hz ⊢
  intro y hy
  have h1 := (hz _ (dual_smul σ.symm (comm_symm σ hc) y hy)).map
    ((σ : (hostE ζ a b) →+* (hostE ζ a b)).toIntAlgHom)
  have e : σ (z : hostE ζ a b) * y = σ ((z : hostE ζ a b) * σ.symm y) := by
    rw [map_mul, AlgEquiv.apply_symm_apply]
  rw [coe_powerSeries_smul_eq_smul, e]
  exact h1

theorem diff_smul_le (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (σ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b))
    (hc : ∀ (τ : (hostE ζ a b) ≃ₐ[KinE ζ a b] (hostE ζ a b)) (x : (hostE ζ a b)), σ (τ x) = τ (σ x)) :
    σ • differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) ≤ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) := by
  rw [Ideal.pointwise_smul_def]
  exact Ideal.map_le_of_le_comap fun z hz => diff_smul_mem hqd h σ hc z hz

theorem diff_smul_eq (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (σ : (hostE ζ a b) ≃ₐ[ℚ] (hostE ζ a b)) :
    σ • differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) := by
  refine le_antisymm (diff_smul_le hqd h σ (comm_of hqd h σ)) ?_
  intro z hz
  have h2 := Ideal.smul_mem_pointwise_smul σ _ _
    (diff_smul_mem hqd h σ⁻¹ (comm_of hqd h σ⁻¹) z hz)
  rwa [smul_inv_smul] at h2

end Invariance

theorem pairing {S : Type*} [CommRing S] [IsDedekindDomain S] (D : Ideal S) (hD0 : D ≠ ⊥)
    (f : Ideal S ≃* Ideal S) (hfD : f D = D) (hff : ∀ I, f (f I) = I)
    (hfix : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors D, f P ≠ P) :
    ∃ B : Ideal S, D = B * f B ∧ B ⊔ f B = ⊤ := by
  classical
  let r : Ideal S → Ideal S → Prop := WellOrderingRel
  set F := UniqueFactorizationMonoid.normalizedFactors D with hF
  have hprime : ∀ P ∈ F, Prime P := fun P hP =>
    UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hprod : F.prod = D :=
    associated_iff_eq.mp (UniqueFactorizationMonoid.prod_normalizedFactors hD0)
  have hprimeMap : ∀ P ∈ F.map f, Prime P := by
    intro P hP
    obtain ⟨P', hP', rfl⟩ := Multiset.mem_map.mp hP
    first
    | exact (MulEquiv.prime_iff f).mpr (hprime P' hP')
    | exact (hprime P' hP').map_mulEquiv f
  have hmapF : F.map f = F := by
    have h1 : (F.map f).prod = D := by rw [← map_multiset_prod, hprod, hfD]
    have h2 := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hprimeMap
    rw [h1] at h2
    exact h2.symm
  let p : Ideal S → Prop := fun P => r P (f P)
  let G := F.filter p
  have hq : F.filter (fun Q => r (f Q) Q) = G.map f := by
    calc F.filter (fun Q => r (f Q) Q) = (F.map f).filter (fun Q => r (f Q) Q) := by rw [hmapF]
      _ = (F.filter ((fun Q => r (f Q) Q) ∘ f)).map f := Multiset.filter_map _ _ _
      _ = G.map f := by
        congr 1
        apply Multiset.filter_congr
        intro P _
        simp only [Function.comp_apply, hff, p]
  have hnot : F.filter (fun Q => r (f Q) Q) = F.filter (fun P => ¬ p P) := by
    apply Multiset.filter_congr
    intro P hP
    have hne : P ≠ f P := fun h => hfix P hP h.symm
    constructor
    · intro h1 h2
      exact asymm h1 h2
    · intro h1
      rcases trichotomous_of r P (f P) with h | h | h
      · exact absurd h h1
      · exact absurd h hne
      · exact h
  have hsplit : F = G + G.map f := by
    rw [← hq, hnot]
    exact (Multiset.filter_add_not p F).symm
  refine ⟨G.prod, ?_, ?_⟩
  · rw [map_multiset_prod, ← Multiset.prod_add, ← hsplit, hprod]
  · by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hB : G.prod ≤ M := le_trans le_sup_left hle
    have hfB : (G.map f).prod ≤ M := by
      rw [← map_multiset_prod]
      exact le_trans le_sup_right hle
    have hmaxOf : ∀ P ∈ F, P ≤ M → P = M := by
      intro P hPF hPM
      have hP := hprime P hPF
      have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
      exact (hPp.isMaximal hP.ne_zero).eq_of_le hM.ne_top hPM
    obtain ⟨P, hPG, hPM⟩ := (Ideal.IsPrime.multiset_prod_le hM.isPrime).mp hB
    obtain ⟨Q, hQG, hQM⟩ := (Ideal.IsPrime.multiset_prod_le hM.isPrime).mp hfB
    obtain ⟨P', hP'G, rfl⟩ := Multiset.mem_map.mp hQG
    have hPF := (Multiset.mem_filter.mp hPG).1
    have hpP : p P := (Multiset.mem_filter.mp hPG).2
    have hP'F := (Multiset.mem_filter.mp hP'G).1
    have hpP' : p P' := (Multiset.mem_filter.mp hP'G).2
    have hfP'F : f P' ∈ F := by
      rw [← hmapF]
      exact Multiset.mem_map_of_mem f hP'F
    have e : f P' = P := (hmaxOf _ hfP'F hQM).trans (hmaxOf P hPF hPM).symm
    have h1 : r P' P := by
      have := hpP'
      simp only [p, e] at this
      exact this
    have h2 : r P P' := by
      have := hpP
      simp only [p, ← e, hff] at this
      rw [← e]
      exact this
    exact asymm h1 h2

end Principal

theorem liesOver_span_of_natCast_mem_frobenius_orbits {M : Type} [Field M] [NumberField M] (P : Ideal (𝓞 M)) [P.IsPrime]
    (p : ℕ) (hp : p.Prime) (hm : ((p : ℤ) : 𝓞 M) ∈ P) : P.LiesOver (span {(p : ℤ)}) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : span {(p : ℤ)} ≤ P.under ℤ := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_comap.mpr (by simpa using hm)
  exact ⟨(Int.ideal_span_isMaximal_of_prime p).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle⟩

theorem hostPrincipal : HostPrincipal := by
  intro e q d hH L _ _ ζ a b h σ hσ
  have hqd := hH.toHypOdd
  let f := MulSemiringAction.toRingEquiv (hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (Ideal (𝓞 (hostE ζ a b))) σ
  have hf : ∀ I, f I = σ • I := fun I => rfl
  have hσσ : σ * σ = 1 := by
    apply galE_injective (e := e) hqd h
    rw [galE_mul hqd h, hσ, galE_one hqd h]
    exact Prod.ext (show c0 * c0 = (1 : G0) by decide) (mul_one _)
  have hD0 : differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) ≠ ⊥ := by
    have := differentIdeal_ne_bot (A := 𝓞 (KinE ζ a b)) (B := 𝓞 (hostE ζ a b))
    exact this
  obtain ⟨B, hB1, hB2⟩ := Principal.pairing _ hD0 f.toMulEquiv
    (by show f _ = _; rw [hf]; exact Principal.diff_smul_eq hqd h σ)
    (fun I => by show f (f I) = I; rw [hf, hf, smul_smul, hσσ, one_smul])
    (by
      intro P hP
      show f P ≠ P
      rw [hf]
      rw [Ideal.mem_normalizedFactors_iff hD0] at hP
      obtain ⟨hPp, hle⟩ := hP
      have hdvd : P ∣ differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) := Ideal.dvd_iff_le.mpr hle
      intro hfix
      have hst : σ ∈ MulAction.stabilizer _ P := hfix
      rcases hostDiffSupport e q d hH L ζ a b h P hPp hdvd with h2 | hq
      · have : P.LiesOver (span {((2 : ℕ) : ℤ)}) :=
          liesOver_span_of_natCast_mem_frobenius_orbits P 2 Nat.prime_two (by exact_mod_cast h2)
        exact hostDecompConj e q d hH L ζ a b h σ hσ 2 (Or.inl rfl) P hst
      · have : P.LiesOver (span {(q : ℤ)}) := liesOver_span_of_natCast_mem_frobenius_orbits P q hH.1 hq
        exact hostDecompConj e q d hH L ζ a b h σ hσ q (Or.inr (Or.inl rfl)) P hst)
  exact ⟨B, hB1, hB2⟩

theorem hostPrincipalBoth : HostDiffSupport ∧ HostPrincipal := ⟨hostDiffSupport, hostPrincipal⟩

end Formalism.FrobeniusOrbits
