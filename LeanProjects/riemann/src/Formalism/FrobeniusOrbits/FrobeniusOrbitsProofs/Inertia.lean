import Mathlib
import Formalism.FrobeniusOrbits.Statement
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia
import Formalism.TameInertiaTowers.TowerFieldFoundations

open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois

namespace Inertia

theorem two_mem_of_pow {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) :
    ∀ (i : ℕ) (η : R), η ^ (2 ^ i) = 1 → η ≠ 1 → η - 1 ∈ Q → (2 : R) ∈ Q := by
  intro i
  induction i with
  | zero =>
    intro η h1 hne _
    simp at h1
    exact absurd h1 hne
  | succ i ih =>
    intro η h1 hne hQ
    by_cases h2 : η ^ 2 = 1
    · have h3 : (η - 1) * (η + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd (sub_eq_zero.1 h) hne
      · have hη : η = -1 := eq_neg_of_add_eq_zero_left h
        have h4 : (2 : R) = -(η - 1) := by rw [hη]; ring
        rw [h4]
        exact Q.neg_mem hQ
    · refine ih (η ^ 2) ?_ h2 ?_
      · rw [← pow_mul, ← pow_succ']
        exact h1
      · have h5 : η ^ 2 - 1 = (η + 1) * (η - 1) := by ring
        rw [h5]
        exact Q.mul_mem_left _ hQ

theorem omega_integral {F : Type} [Field F] [NumberField F] {r : ℕ} (hr4 : r % 4 = 3) {X : F}
    (hX : X ^ 2 = -(r : F)) : IsIntegral ℤ ((1 + X) / 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = 4 * k + 3 := ⟨r / 4, by omega⟩
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((k : ℤ) + 1), by monicity!, ?_⟩
  push_cast at hX
  rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C]
  simp only [algebraMap_int_eq, eq_intCast]
  push_cast
  linear_combination (1 / 4 : F) * hX

theorem sqrt_fixed {F : Type} [Field F] [NumberField F] {r p : ℕ} (hr : r.Prime) (hr4 : r % 4 = 3)
    (hp : p.Prime) (hpr : p ≠ r) (P : Ideal (𝓞 F)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ : F ≃ₐ[ℚ] F) {X : F} (hX : X ^ 2 = -(r : F)) (hσX : σ X = -X) :
    ¬ ∀ y : 𝓞 F, σ • y - y ∈ P := by
  intro hall
  set ω : 𝓞 F := ⟨(1 + X) / 2, omega_integral hr4 hX⟩ with hωdef
  have hmem := hall ω
  have hval : algebraMap (𝓞 F) F (σ • ω - ω) = -X := by
    show σ ((1 + X) / 2) - (1 + X) / 2 = -X
    rw [map_div₀, map_add, map_one, hσX, map_ofNat]
    ring
  have hy2 : (σ • ω - ω) * (σ • ω - ω) = -((r : ℤ) : 𝓞 F) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 F) F
    rw [map_mul, hval, map_neg, map_intCast]
    push_cast
    linear_combination hX
  have hrP : ((r : ℤ) : 𝓞 F) ∈ P := by
    have h1 := P.mul_mem_left (σ • ω - ω) hmem
    rw [hy2] at h1
    simpa using P.neg_mem h1
  have hr' : (r : ℤ) ∈ Ideal.span {(p : ℤ)} := by
    rw [Ideal.over_def P (Ideal.span {(p : ℤ)})]
    show algebraMap ℤ (𝓞 F) (r : ℤ) ∈ P
    simpa using hrP
  rw [Ideal.mem_span_singleton] at hr'
  have hpr' : p ∣ r := by exact_mod_cast hr'
  exact hpr ((Nat.prime_dvd_prime_iff_eq hp hr).1 hpr')

theorem hcl_one (e : ℕ) : hcl e 1 = 1 := by simp [hcl]

theorem neg_one_ne_one' : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have h' := congrArg Units.val h
  simp at h'

section Host

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem algebraMap_smul (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (τ : Gal(L/ℚ))
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) (x : 𝓞 (hostE ζ a b)) :
    algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (σ • x) = τ • algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) x := by
  apply NumberField.RingOfIntegers.ext
  show (((σ ((x : hostE ζ a b)) : hostE ζ a b)) : L) = τ (((x : hostE ζ a b)) : L)
  exact hστ _

theorem mem_of_restrict (P : Ideal (𝓞 (hostE ζ a b))) (Q : Ideal (𝓞 L)) [Q.LiesOver P]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (τ : Gal(L/ℚ))
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x)
    (hτ : ∀ y : 𝓞 L, τ • y - y ∈ Q) : ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P := by
  intro x
  rw [Ideal.over_def Q P]
  show algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) (σ • x - x) ∈ Q
  rw [map_sub, algebraMap_smul σ τ hστ x]
  exact hτ _

theorem mem_of_lift (P : Ideal (𝓞 (hostE ζ a b))) (Q : Ideal (𝓞 L)) [Q.LiesOver P]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (τ : Gal(L/ℚ))
    (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x)
    (hσ : ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) (y : 𝓞 (hostE ζ a b)) :
    τ • algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) y - algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) y ∈ Q := by
  rw [← algebraMap_smul σ τ hστ y, ← map_sub]
  have h := hσ y
  rw [Ideal.over_def Q P] at h
  exact h

theorem hcl_eq_one (h : IsLayer (e + 2) q d ζ a b) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] (τ : Gal(L/ℚ)) (Θ : 𝓞 L)
    (hΘ : (Θ : L) = ζ + ζ⁻¹) (hmem : τ • Θ - Θ ∈ Q) : hcl e (h.1.autToPow ℚ τ) = 1 := by
  have hn : 0 < 2 ^ (e + 2) := by positivity
  have hζ0 : ζ ≠ 0 := h.1.ne_zero hn.ne'
  have h2Q : (2 : 𝓞 L) ∉ Q := by
    intro h2
    have h2' : (2 : ℤ) ∈ Ideal.span {(p : ℤ)} := by
      rw [Ideal.over_def Q (Ideal.span {(p : ℤ)})]
      show algebraMap ℤ (𝓞 L) 2 ∈ Q
      simpa using h2
    rw [Ideal.mem_span_singleton] at h2'
    have hp2' : p ∣ 2 := by exact_mod_cast h2'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2')
  set u := h.1.autToPow ℚ τ with hu
  set v := (u : ZMod (2 ^ (e + 2))).val with hv
  have hvlt : v < 2 ^ (e + 2) := ZMod.val_lt _
  have huv : ((v : ℕ) : ZMod (2 ^ (e + 2))) = (u : ZMod (2 ^ (e + 2))) := ZMod.natCast_zmod_val _
  have hτζ : τ ζ = ζ ^ v := (h.1.autToPow_spec ℚ τ).symm
  have hτζi : τ ζ⁻¹ = ζ⁻¹ ^ v := by rw [map_inv₀, hτζ, inv_pow]
  set Z : 𝓞 L := ⟨ζ, h.1.isIntegral hn⟩ with hZ
  set Zi : 𝓞 L := ⟨ζ⁻¹, h.1.inv.isIntegral hn⟩ with hZi
  have eZ : algebraMap (𝓞 L) L Z = ζ := rfl
  have eZi : algebraMap (𝓞 L) L Zi = ζ⁻¹ := rfl
  have hZZi : Z * Zi = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_mul, eZ, eZi, map_one, mul_inv_cancel₀ hζ0]
  have hZn : Z ^ (2 ^ (e + 2)) = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, eZ, map_one]
    exact h.1.pow_eq_one
  have hZin : Zi ^ (2 ^ (e + 2)) = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    rw [map_pow, eZi, map_one]
    exact h.1.inv.pow_eq_one
  have hdiff : τ • Θ - Θ = Zi ^ v * (Z ^ (v + 1) - 1) * (Z ^ v * Zi - 1) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 L) L
    have e1 : algebraMap (𝓞 L) L (τ • Θ) = τ ζ + τ ζ⁻¹ := by
      show τ (Θ : L) = _
      rw [hΘ, map_add]
    have e2 : algebraMap (𝓞 L) L Θ = ζ + ζ⁻¹ := hΘ
    simp only [map_sub, map_mul, map_pow, map_one, e1, e2, eZ, eZi, hτζ, hτζi, inv_pow]
    field_simp
    ring
  rw [hdiff] at hmem
  have hQ : Q.IsPrime := inferInstance
  have key : u = 1 ∨ u = -1 := by
    by_contra hne
    push_neg at hne
    apply h2Q
    rcases hQ.mem_or_mem hmem with h12 | h3
    · rcases hQ.mem_or_mem h12 with h1 | h2
      · exfalso
        have h1' := Q.mul_mem_left (Z ^ v) h1
        rw [← mul_pow, hZZi, one_pow] at h1'
        exact hQ.ne_top ((Ideal.eq_top_iff_one Q).2 h1')
      · refine two_mem_of_pow Q (e + 2) (Z ^ (v + 1)) ?_ ?_ h2
        · rw [← pow_mul, mul_comm, pow_mul, hZn, one_pow]
        · intro h1
          apply hne.2
          have h1' : ζ ^ (v + 1) = 1 := by
            have := congrArg (algebraMap (𝓞 L) L) h1
            rwa [map_pow, eZ, map_one] at this
          have hdvd := (h.1.pow_eq_one_iff_dvd (v + 1)).1 h1'
          have hv1 : v + 1 = 2 ^ (e + 2) :=
            le_antisymm (by omega) (Nat.le_of_dvd (by omega) hdvd)
          apply Units.ext
          rw [Units.val_neg, Units.val_one, ← huv]
          have h0 : ((v + 1 : ℕ) : ZMod (2 ^ (e + 2))) = 0 := by
            rw [hv1]; exact ZMod.natCast_self _
          push_cast at h0
          linear_combination h0
    · refine two_mem_of_pow Q (e + 2) (Z ^ v * Zi) ?_ ?_ h3
      · rw [mul_pow, ← pow_mul, mul_comm v, pow_mul, hZn, one_pow, hZin, one_mul]
      · intro h1
        apply hne.1
        have h1' : ζ ^ v = ζ ^ 1 := by
          have := congrArg (algebraMap (𝓞 L) L) h1
          rw [map_mul, map_pow, eZ, eZi, map_one] at this
          rw [pow_one]
          field_simp at this
          exact this
        have hv1 : v = 1 := h.1.pow_inj hvlt (by
          have : 1 < 2 ^ (e + 2) := Nat.one_lt_two_pow (by omega)
          exact this) h1'
        apply Units.ext
        rw [Units.val_one, ← huv, hv1, Nat.cast_one]
  rcases key with h1 | h1
  · rw [h1]
    exact hcl_one e
  · rw [h1]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)

theorem sub_h (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hσ : ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) :
    (galE e ζ a b σ).2 = 1 := by
  haveI := (layer_galois hqd h).1
  have hinj : Function.Injective (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L)) := by
    intro x y hxy
    have h1 := congrArg (fun z : 𝓞 L => (z : L)) hxy
    apply NumberField.RingOfIntegers.ext
    apply Subtype.ext
    exact h1
  obtain ⟨Q, -, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 L))
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  haveI := hQp
  haveI : Q.LiesOver P := ⟨hQc.symm⟩
  haveI : Q.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans Q P _
  set τ : Gal(L/ℚ) := σ.liftNormal L with hτ
  have hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x :=
    fun x => (σ.liftNormal_commutes L x).symm
  have hint : IsIntegral ℤ (thE ζ a b) := by
    have h0 : 0 < 2 ^ (e + 2) := by positivity
    have hL : IsIntegral ℤ (ζ + ζ⁻¹) := (h.1.isIntegral h0).add (h.1.inv.isIntegral h0)
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (hostE ζ a b) L)
      (algebraMap (hostE ζ a b) L).injective).1 hL
  set θ : 𝓞 (hostE ζ a b) := ⟨thE ζ a b, hint⟩ with hθ
  rw [galE_lift h hστ]
  exact hcl_eq_one h p hp hp2 Q τ (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L) θ) rfl
    (mem_of_lift P Q σ τ hστ hσ θ)

theorem sign_one (X : hostE ζ a b) (s : ℤˣ) (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b)
    (hXs : ((σ X : hostE ζ a b) : L) = ((s : ℤ) : L) * (X : L)) {r : ℕ} (hr : r.Prime)
    (hr4 : r % 4 = 3) (hX : (X : L) ^ 2 = -(r : L)) {p : ℕ} (hp : p.Prime) (hpr : p ≠ r)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (hσ : ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P) : s = 1 := by
  rcases Int.units_eq_one_or s with hs | hs
  · exact hs
  · exfalso
    have hX' : X ^ 2 = -(r : hostE ζ a b) := by
      apply (algebraMap (hostE ζ a b) L).injective
      simpa using hX
    have hσX : σ X = -X := by
      apply Subtype.ext
      rw [hXs, hs]
      simp
    exact sqrt_fixed hr hr4 hp hpr P σ hX' hσX hσ

theorem sup (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ)
    (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (g : GalL (e + 2))
    (hg : galE e ζ a b σ = ((g.2.1, g.2.2), hcl e g.1))
    (hI : ∀ τ : Gal(L/ℚ), galMap h.1 a b τ = g → ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime]
      [Q.LiesOver (span {(p : ℤ)})], ∀ y : 𝓞 L, τ • y - y ∈ Q) :
    ∀ x : 𝓞 (hostE ζ a b), σ • x - x ∈ P := by
  haveI := (layer_galois hqd h).1
  have hinj : Function.Injective (algebraMap (𝓞 (hostE ζ a b)) (𝓞 L)) := by
    intro x y hxy
    have h1 := congrArg (fun z : 𝓞 L => (z : L)) hxy
    apply NumberField.RingOfIntegers.ext
    apply Subtype.ext
    exact h1
  obtain ⟨Q, -, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 L))
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  haveI := hQp
  haveI : Q.LiesOver P := ⟨hQc.symm⟩
  haveI : Q.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.trans Q P _
  set τ1 : Gal(L/ℚ) := σ.liftNormal L with hτ1
  have hστ1 : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ1 x :=
    fun x => (σ.liftNormal_commutes L x).symm
  have h1 := galE_lift h hστ1
  rw [hg] at h1
  have hs1 : g.2.1 = (galMap h.1 a b τ1).2.1 := congrArg (fun z : GG e => z.1.1) h1
  have hs2 : g.2.2 = (galMap h.1 a b τ1).2.2 := congrArg (fun z : GG e => z.1.2) h1
  have hh : hcl e g.1 = hcl e (galMap h.1 a b τ1).1 := congrArg Prod.snd h1
  have hpm : g.1 = (galMap h.1 a b τ1).1 ∨ g.1 = -(galMap h.1 a b τ1).1 := by
    unfold hcl at hh
    rw [QuotientGroup.eq, Subgroup.mem_zpowers_iff] at hh
    obtain ⟨k, hk⟩ := hh
    rcases Int.even_or_odd k with hk2 | hk2
    · left
      rw [hk2.neg_one_zpow] at hk
      exact inv_mul_eq_one.1 hk.symm
    · right
      rw [hk2.neg_one_zpow] at hk
      have h3 : (galMap h.1 a b τ1).1 = g.1 * -1 := by rw [hk, mul_inv_cancel_left]
      rw [h3, mul_neg_one, neg_neg]
  obtain ⟨τ, hτg, hστ⟩ : ∃ τ : Gal(L/ℚ), galMap h.1 a b τ = g ∧
      ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x := by
    rcases hpm with hpm | hpm
    · exact ⟨τ1, Prod.ext hpm.symm (Prod.ext hs1.symm hs2.symm), hστ1⟩
    · refine ⟨τ1 * tau0 hqd h, ?_, ?_⟩
      · rw [(layer_galois hqd h).2.2.1, galMap_zeta_inversion]
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · simp [hpm]
        · simp [hs1]
        · simp [hs2]
      · intro x
        rw [hστ1 x, AlgEquiv.mul_apply]
        congr 1
        exact (((hostFixed e q d hqd L ζ a b h).2 x).1 x.2 _ (galMap_zeta_inversion hqd h)).symm
  exact mem_of_restrict P Q σ τ hστ (fun y => hI τ hτg Q y)

end Host

end Inertia

open Inertia

theorem hostInertia : HostInertia := by
  intro e q d hH L _ _ ζ a b h σ
  have hqd := hH.toHypOdd
  have hq4 : q % 4 = 3 := by have := hH.2.2.1; omega
  have hd4 : d % 4 = 3 := by have := hH.2.2.2.1; omega
  have hQD : HypQD q d := ⟨hH.1, hH.2.1, hH.2.2.1, by have := hH.2.2.2.1; omega⟩
  have hspec := hostGalSpec e q d hqd L ζ a b h σ
  have hsa := hspec.1
  have hsb := hspec.2.1
  have hn : 1 ≤ e + 2 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro P _ _
    haveI : P.LiesOver (span {((2 : ℕ) : ℤ)}) := by simpa using ‹P.LiesOver (span {(2 : ℤ)})›
    constructor
    · intro hall
      have h1 := sign_one (aE ζ a b) ((galE e ζ a b σ).1.1) σ hsa hqd.1 hq4 h.2.1 Nat.prime_two
        (Ne.symm hqd.2.2.2.1) P hall
      have h2 := sign_one (bE ζ a b) ((galE e ζ a b σ).1.2) σ hsb hqd.2.1 hd4 h.2.2.1 Nat.prime_two
        (Ne.symm hqd.2.2.2.2) P hall
      exact Prod.ext h1 h2
    · intro h1
      obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (galE e ζ a b σ).2
      refine sup hqd h 2 P σ (m, 1, 1) ?_ ?_
      · exact Prod.ext h1 hm.symm
      · intro τ hτ Q _ _
        refine ((layerInertiaTwo (e + 2) q d hn hQD L ζ a b h Q τ).2 ?_)
        show (galMap h.1 a b τ).2 = 1
        rw [hτ]
        rfl
  · intro P _ _
    constructor
    · intro hall
      have hh := sub_h hqd h q hqd.1 hqd.2.2.2.1 P σ hall
      have h2 := sign_one (bE ζ a b) ((galE e ζ a b σ).1.2) σ hsb hqd.2.1 hd4 h.2.2.1 hqd.1
        hqd.2.2.1 P hall
      rcases Int.units_eq_one_or (galE e ζ a b σ).1.1 with h1 | h1
      · left
        exact Prod.ext (Prod.ext h1 h2) hh
      · right
        exact Prod.ext (Prod.ext h1 h2) hh
    · intro hg
      rcases hg with hg | hg
      · refine sup hqd h q P σ 1 ?_ ?_
        · rw [hg]
          exact Prod.ext rfl (hcl_one e).symm
        · intro τ hτ Q _ _
          refine ((layerInertiaTame (e + 2) q d hn hqd L ζ a b h).1 Q τ).2 ?_
          rw [hτ]
          exact Subgroup.one_mem _
      · refine sup hqd h q P σ (1, -1, 1) ?_ ?_
        · rw [hg]
          exact Prod.ext rfl (hcl_one e).symm
        · intro τ hτ Q _ _
          refine ((layerInertiaTame (e + 2) q d hn hqd L ζ a b h).1 Q τ).2 ?_
          rw [hτ]
          exact Subgroup.mem_zpowers _
  · intro P _ _
    constructor
    · intro hall
      have hh := sub_h hqd h d hqd.2.1 hqd.2.2.2.2 P σ hall
      have h1 := sign_one (aE ζ a b) ((galE e ζ a b σ).1.1) σ hsa hqd.1 hq4 h.2.1 hqd.2.1
        (Ne.symm hqd.2.2.1) P hall
      rcases Int.units_eq_one_or (galE e ζ a b σ).1.2 with h2 | h2
      · left
        exact Prod.ext (Prod.ext h1 h2) hh
      · right
        exact Prod.ext (Prod.ext h1 h2) hh
    · intro hg
      rcases hg with hg | hg
      · refine sup hqd h d P σ 1 ?_ ?_
        · rw [hg]
          exact Prod.ext rfl (hcl_one e).symm
        · intro τ hτ Q _ _
          refine ((layerInertiaTame (e + 2) q d hn hqd L ζ a b h).2 Q τ).2 ?_
          rw [hτ]
          exact Subgroup.one_mem _
      · refine sup hqd h d P σ (1, 1, -1) ?_ ?_
        · rw [hg]
          exact Prod.ext rfl (hcl_one e).symm
        · intro τ hτ Q _ _
          refine ((layerInertiaTame (e + 2) q d hn hqd L ζ a b h).2 Q τ).2 ?_
          rw [hτ]
          exact Subgroup.mem_zpowers _

theorem hostUnramEF : HostUnramEF := by
  intro e q d hH L _ _ ζ a b h P hP hP0 σ hσ hall
  have hqd := hH.toHypOdd
  have hq4 : q % 4 = 3 := by have := hH.2.2.1; omega
  have hd4 : d % 4 = 3 := by have := hH.2.2.2.1; omega
  have hspec := hostGalSpec e q d hqd L ζ a b h σ
  have hI0 : P.under ℤ ≠ ⊥ := fun h0 => hP0 (Ideal.eq_bot_of_comap_eq_bot h0)
  haveI : (P.under ℤ).IsPrime := by haveI := hP; exact Ideal.comap_isPrime _ _
  haveI := hP
  set g := Submodule.IsPrincipal.generator (P.under ℤ) with hgdef
  have hgspan : Ideal.span {g} = P.under ℤ := Submodule.IsPrincipal.span_singleton_generator _
  have hg0 : g ≠ 0 := by
    intro h0
    apply hI0
    rw [← hgspan, h0, Ideal.span_singleton_eq_bot.2 rfl]
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).1 (by rw [hgspan]; infer_instance)
  have hp : g.natAbs.Prime := Int.prime_iff_natAbs_prime.1 hgp
  haveI : P.LiesOver (span {((g.natAbs : ℕ) : ℤ)}) :=
    ⟨(Ideal.span_singleton_eq_span_singleton.2 (Int.associated_natAbs g).symm).trans hgspan⟩
  by_cases hpq : g.natAbs = q
  · have hs := sign_one (bE ζ a b) ((galE e ζ a b σ).1.2) σ hspec.2.1 hqd.2.1 hd4 h.2.2.1 hp
      (by rw [hpq]; exact hqd.2.2.1) P hall
    rw [hσ] at hs
    exact neg_one_ne_one' hs
  · have hs := sign_one (aE ζ a b) ((galE e ζ a b σ).1.1) σ hspec.1 hqd.1 hq4 h.2.1 hp hpq P hall
    rw [hσ] at hs
    exact neg_one_ne_one' hs

end Formalism.FrobeniusOrbits
