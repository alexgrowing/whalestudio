import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RangeLeRangeOfIsUnramifiedAt
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApplyEqOfNormal
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RayClassFieldInfModulusEqSupStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedAtOfIsUnramifiedInGaloisExtensionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootInRayClassFieldNatModulusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaloisRatComplexImageRayClassFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostImagQuadraticIsGaloisUnitsPmOneStatement

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.SeriesTie GlobalTheory.FieldSize
open Formalism.L2.Host (embLL0)

namespace GlobalTheory.RayInFrac

theorem isUnramifiedAt_of_unramIn {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)} (h : GlobalTheory.NT.UnramIn L 𝔭) (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver 𝔭.asIdeal] : Algebra.IsUnramifiedAt (𝓞 K) P :=
  GlobalTheory.T.isUnramifiedAt_of_isUnramifiedInGaloisExtension h P

theorem exists_isPrimitiveRoot_of_isRay {K H : Type} [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H]
    [IsAbelianGalois K H] {n : ℕ} (hn : n ≠ 0) (h : IsRay H (Ideal.span {(n : 𝓞 K)})) : ∃ ζ : H, IsPrimitiveRoot ζ n :=
  GlobalTheory.T.exists_primitiveRoot_in_rayClassField_natModulus hn h

theorem isGalois_fieldRange_of_isRay {K H : Type} [Field K] [NumberField K] [IsGalois ℚ K] [Field H] [NumberField H]
    [Algebra K H] [IsAbelianGalois K H] {n : ℕ} (hn : n ≠ 0) (h : IsRay H (Ideal.span {(n : 𝓞 K)})) (j : H →+* ℂ) :
    IsGalois ℚ j.toRatAlgHom.fieldRange :=
  GlobalTheory.T.isGalois_rat_complexImage_rayClassField hn h j

theorem sup_fieldRange_eq_top {K H H₁ H₂ : Type} [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H]
    [IsAbelianGalois K H] [Field H₁] [NumberField H₁] [Algebra K H₁] [IsAbelianGalois K H₁] [Field H₂] [NumberField H₂]
    [Algebra K H₂] [IsAbelianGalois K H₂] (hU : ∀ u : (𝓞 K)ˣ, u = 1 ∨ u = -1) {𝔞 𝔟 : Ideal (𝓞 K)} (ha : 𝔞 ≠ ⊥)
    (hb : 𝔟 ≠ ⊥) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqa : 𝔞 ≤ Ideal.span {(q : 𝓞 K)})
    (hqb : 𝔟 ≤ Ideal.span {(q : 𝓞 K)}) (h : IsRay H (𝔞 ⊓ 𝔟)) (h₁ : IsRay H₁ 𝔞) (h₂ : IsRay H₂ 𝔟)
    (f₁ : H₁ →ₐ[K] H) (f₂ : H₂ →ₐ[K] H) : f₁.fieldRange ⊔ f₂.fieldRange = ⊤ :=
  GlobalTheory.T.rayClassField_inf_modulus_eq_sup hU ha hb hq hq2 hqa hqb h h₁ h₂ f₁ f₂

theorem hostK_facts (D : D7) : IsGalois ℚ D.host.K ∧ ∀ u : (𝓞 D.host.K)ˣ, u = 1 ∨ u = -1 :=
  GlobalTheory.T.host_imagQuadratic_isGalois_units_pm_one D

abbrev phiK (D : D7) : ↥D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)

def eLL0 (D : D7) : D.host.E →+* ↥D.LL0 := D.embE.codRestrict D.LL0 fun x => D.hostField_le_fixedField x

theorem smallCoeffField_embedding_comp_host_map (D : D7) (x : D.host.E) : embLL0 D (eLL0 D x) = D.host.φ₀ x := by
  rw [← D.embE_φ₀]; rfl

theorem span_inf_span {R : Type} [CommRing R] (c u v : ℕ) (h : u.Coprime v) :
    Ideal.span {((c * u : ℕ) : R)} ⊓ Ideal.span {((c * v : ℕ) : R)} = Ideal.span {((c * u * v : ℕ) : R)} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hx.1
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hx.2
    obtain ⟨A, B, hAB⟩ := Nat.isCoprime_iff_coprime.2 h
    have hAB' : (A : R) * u + (B : R) * v = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → R) hAB
    refine Ideal.mem_span_singleton'.2 ⟨(A : R) * t + (B : R) * s, ?_⟩
    push_cast at hs ht ⊢
    linear_combination ((A : R) * u) * ht + ((B : R) * v) * hs + x * hAB'
  · refine le_inf ?_ ?_ <;> rw [Ideal.span_singleton_le_span_singleton]
    · exact ⟨(v : R), by push_cast; ring⟩
    · exact ⟨(u : R), by push_cast; ring⟩

theorem embLL0_le (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (b : Bool) :
    (embLL0 D).fieldRange ≤ (ρ.e i b).fieldRange := by
  rintro _ ⟨x, rfl⟩
  exact ⟨sideEmb D.ntw i b x, hρ.e_LL0 i b x⟩

theorem exists_field (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (b : Bool)
    (hRF : GlobalTheory.NT.RayField)
    (hray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (m N : ℕ) (hm : D.host.g 0 * D.host.g 1 ∣ m) (hm' : m ∣ D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde')
    (hN : N ≠ 0) (hNl : N.Coprime (D.ntw.l i)) :
    ∃ L : IntermediateField ℚ ℂ, FiniteDimensional ℚ L ∧ (IsGalois ℚ D.LL0 → IsGalois ℚ L) ∧
      (embLL0 D).fieldRange ≤ L.toSubfield ∧ L.toSubfield ≤ (ρ.e i b).fieldRange ∧
      GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (m * N) L.toSubfield ∧ ∀ z : ℂ, z ^ (m * N) = 1 → z ∈ L := by
  classical
  obtain ⟨hKgal, hU⟩ := hostK_facts D
  letI : Algebra D.host.K ℂ := (phiK D).toAlgebra
  have hlp : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  have hm₀0 : D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' ≠ 0 := by
    have := (D.host.g_prime 0).ne_zero; have := (D.host.g_prime 1).ne_zero
    have := D.host.pde_prime.ne_zero; have := D.host.pde'_prime.ne_zero
    positivity
  have hm0 : m ≠ 0 := fun h => hm₀0 (Nat.eq_zero_of_zero_dvd (h ▸ hm'))
  obtain ⟨m'', a, hmm, hm''⟩ : ∃ m'' a : ℕ, m = m'' * D.ntw.l i ^ a ∧ (D.ntw.l i).Coprime m'' :=
    ⟨m / D.ntw.l i ^ m.factorization (D.ntw.l i), m.factorization (D.ntw.l i),
      (Nat.div_mul_cancel (Nat.ordProj_dvd m _)).symm, Nat.coprime_ordCompl hlp hm0⟩
  have hcop : (D.ntw.l i ^ a).Coprime N := Nat.Coprime.pow_left _ hNl.symm
  obtain ⟨q, hq, hq2, hqm⟩ : ∃ q, q.Prime ∧ q ≠ 2 ∧ q ∣ m'' := by
    obtain ⟨k, hk⟩ : ∃ k : Fin 2, D.host.g k ≠ D.ntw.l i := by
      by_contra h
      push_neg at h
      exact D.host.g_ne (by rw [h 0, h 1])
    refine ⟨D.host.g k, D.host.g_prime k, Formalism.L2.Pj.g_ne_two D k, ?_⟩
    have h1 : D.host.g k ∣ m := (show D.host.g k ∣ D.host.g 0 * D.host.g 1 by fin_cases k <;> simp).trans hm
    rw [hmm] at h1
    exact Nat.Coprime.dvd_of_dvd_mul_right
      (Nat.Coprime.pow_right _ ((Nat.coprime_primes (D.host.g_prime k) hlp).2 hk)) h1

  have hspan : ∀ n : ℕ, n ≠ 0 → Ideal.span {((n : ℕ) : 𝓞 D.host.K)} ≠ ⊥ := fun n hn => by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hn
  have hdiv : ∀ u v : ℕ, u ∣ v → Ideal.span {((u : ℕ) : 𝓞 D.host.K)} ∣ Ideal.span {((v : ℕ) : 𝓞 D.host.K)} :=
    fun u v h => Ideal.dvd_iff_le.2 (Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast h))
  have hmN : m * N ≠ 0 := mul_ne_zero hm0 hN
  have hm''0 : m'' * N ≠ 0 := mul_ne_zero (fun h => hm0 (by rw [hmm, h, zero_mul])) hN
  have hm''m : m'' ∣ m := ⟨_, hmm⟩
  obtain ⟨H, _, _, _, _, hH⟩ := hRF D.host.K _ (hspan (m * N) hmN)
  obtain ⟨H₁, _, _, _, _, hH₁⟩ := hRF D.host.K _ (hspan m hm0)
  obtain ⟨H₂, _, _, _, _, hH₂⟩ := hRF D.host.K _ (hspan (m'' * N) hm''0)
  obtain ⟨H₀, _, _, _, _, hH₀, j₀, hj₀, hj₀v⟩ := hray
  have hH' : IsRay H (Ideal.span {((m * N : ℕ) : 𝓞 D.host.K)}) := hH
  have hH₁' : IsRay H₁ (Ideal.span {((m : ℕ) : 𝓞 D.host.K)}) := hH₁
  have hH₂' : IsRay H₂ (Ideal.span {((m'' * N : ℕ) : 𝓞 D.host.K)}) := hH₂
  have f₁ : H₁ →ₐ[D.host.K] H :=
    (GlobalTheory.Published.nonempty_algHom_of_isRay_of_dvd (hspan _ hmN) (hdiv _ _ (dvd_mul_right m N)) hH' hH₁').some
  have f₂ : H₂ →ₐ[D.host.K] H :=
    (GlobalTheory.Published.nonempty_algHom_of_isRay_of_dvd (hspan _ hmN) (hdiv _ _ (mul_dvd_mul_right hm''m N)) hH' hH₂').some
  have g₁ : H₁ →ₐ[D.host.K] H₀ :=
    (GlobalTheory.Published.nonempty_algHom_of_isRay_of_dvd (hspan _ hm₀0) (hdiv _ _ hm') hH₀ hH₁').some
  let j : H →ₐ[D.host.K] ℂ := IsAlgClosed.lift
  have hinf : Ideal.span {((m : ℕ) : 𝓞 D.host.K)} ⊓ Ideal.span {((m'' * N : ℕ) : 𝓞 D.host.K)} =
      Ideal.span {((m * N : ℕ) : 𝓞 D.host.K)} := by
    have := span_inf_span (R := 𝓞 D.host.K) m'' (D.ntw.l i ^ a) N hcop
    rwa [← hmm] at this
  have hsup := sup_fieldRange_eq_top hU (hspan _ hm0) (hspan _ hm''0) hq hq2
    (Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (hqm.trans hm''m)))
    (Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (hqm.trans (dvd_mul_right _ _))))
    (hinf ▸ hH') hH₁' hH₂' f₁ f₂

  have hphi : ∀ x : D.host.K, algebraMap D.host.K ℂ x = embLL0 D (eLL0 D (algebraMap D.host.K D.host.E x)) :=
    fun x => (smallCoeffField_embedding_comp_host_map D _).symm
  have hLe := embLL0_le D ρ hρ i b
  have h1 : ∀ x : H₁, j (f₁ x) ∈ (ρ.e i b).fieldRange := by
    intro x
    let j₀' : H₀ →ₐ[D.host.K] ℂ := { j₀ with commutes' := fun y => RingHom.congr_fun hj₀ y }
    obtain ⟨y, hy⟩ := GlobalTheory.Mem.RayMono.exists_apply_eq_of_normal (j.comp f₁) (j₀'.comp g₁) x
    have : j (f₁ x) = j₀ (g₁ y) := hy.symm
    rw [this]
    exact hLe (hj₀v (g₁ y))
  have h2 : ∀ x : H₂, j (f₂ x) ∈ (ρ.e i b).fieldRange := by
    haveI := D.ntw.O_complete i
    haveI := D.ntw.resO_ac i
    let ι : D.host.K →+* FractionRing (D.ntw.O i) :=
      (sideEmb D.ntw i b).comp ((eLL0 D).comp (algebraMap D.host.K D.host.E))
    have hσ : ((j.comp f₂ : H₂ →ₐ[D.host.K] ℂ) : H₂ →+* ℂ).comp (algebraMap D.host.K H₂) = (ρ.e i b).comp ι := by
      ext x
      change j (f₂ (algebraMap D.host.K H₂ x)) = ρ.e i b (sideEmb D.ntw i b (eLL0 D (algebraMap D.host.K D.host.E x)))
      rw [f₂.commutes, j.commutes, hρ.e_LL0, hphi]
    have hur : ∀ (P : Ideal (𝓞 H₂)) [P.IsPrime], ((D.ntw.l i : ℕ) : 𝓞 H₂) ∈ P →
        Algebra.IsUnramifiedAt (𝓞 D.host.K) P := by
      intro P _ hlP
      have hlK : ((D.ntw.l i : ℕ) : 𝓞 D.host.K) ∈ P.under (𝓞 D.host.K) := by
        rw [Ideal.under, Ideal.mem_comap, map_natCast]; exact hlP
      have hne : P.under (𝓞 D.host.K) ≠ ⊥ := fun h0 => by
        rw [h0, Ideal.mem_bot] at hlK
        exact hlp.ne_zero (by exact_mod_cast hlK)
      let 𝔭 : HeightOneSpectrum (𝓞 D.host.K) := ⟨P.under (𝓞 D.host.K), inferInstance, hne⟩
      haveI : P.LiesOver 𝔭.asIdeal := ⟨rfl⟩
      refine isUnramifiedAt_of_unramIn (hH₂'.1 𝔭 fun hd => ?_) P
      have h3 : ((m'' * N : ℕ) : 𝓞 D.host.K) ∈ 𝔭.asIdeal := Ideal.dvd_iff_le.1 hd (Ideal.mem_span_singleton_self _)
      have hc : (D.ntw.l i).Coprime (m'' * N) := Nat.Coprime.mul_right hm'' hNl.symm
      obtain ⟨A, B, hAB⟩ := Nat.isCoprime_iff_coprime.2 hc
      have h5 := 𝔭.asIdeal.add_mem (𝔭.asIdeal.mul_mem_left (A : 𝓞 D.host.K) hlK)
        (𝔭.asIdeal.mul_mem_left (B : 𝓞 D.host.K) h3)
      rw [show (A : 𝓞 D.host.K) * ((D.ntw.l i : ℕ) : 𝓞 D.host.K) + (B : 𝓞 D.host.K) * ((m'' * N : ℕ) : 𝓞 D.host.K) = 1 by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.K) hAB] at h5
      exact 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h5)
    intro x
    obtain ⟨y, hy⟩ := GlobalTheory.UnramifiedEmbedding.range_le_range_of_isUnramifiedAt (D.ntw.O i) (D.ntw.l i) (D.ntw.O_l i)
      (ρ.e i b) D.host.K H₂ ι _ hσ hur ⟨x, rfl⟩
    exact ⟨y, hy⟩
  have hall : ∀ x : H, j x ∈ (ρ.e i b).fieldRange := by
    let T : IntermediateField D.host.K ℂ :=
      Subfield.toIntermediateField (ρ.e i b).fieldRange fun x => by rw [hphi]; exact hLe ⟨_, rfl⟩
    have hT : f₁.fieldRange ⊔ f₂.fieldRange ≤ T.comap j :=
      sup_le (by rintro _ ⟨y, rfl⟩; exact h1 y) (by rintro _ ⟨y, rfl⟩; exact h2 y)
    rw [hsup] at hT
    intro x
    exact hT (IntermediateField.mem_top (x := x))

  let A : IntermediateField ℚ ℂ := (embLL0 D).toRatAlgHom.fieldRange
  let B : IntermediateField ℚ ℂ := (j : H →+* ℂ).toRatAlgHom.fieldRange
  haveI : FiniteDimensional ℚ A := (AlgEquiv.ofInjectiveField (embLL0 D).toRatAlgHom).toLinearEquiv.finiteDimensional
  haveI : FiniteDimensional ℚ B :=
    (AlgEquiv.ofInjectiveField (j : H →+* ℂ).toRatAlgHom).toLinearEquiv.finiteDimensional
  have hA : ∀ x, embLL0 D x ∈ A ⊔ B := fun x => (le_sup_left : A ≤ A ⊔ B) ⟨x, rfl⟩
  have hB : ∀ x, j x ∈ A ⊔ B := fun x => (le_sup_right : B ≤ A ⊔ B) ⟨x, rfl⟩
  refine ⟨A ⊔ B, inferInstance, fun hG => ?_, ?_, ?_, ?_, ?_⟩
  · have gA : IsGalois ℚ A := IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField (embLL0 D).toRatAlgHom)
    have gB : IsGalois ℚ B := isGalois_fieldRange_of_isRay hmN hH' (j : H →+* ℂ)
    haveI : Normal ℚ ↥(A ⊔ B) := @IntermediateField.normal_sup ℚ ℂ _ _ _ A B gA.to_normal gB.to_normal
    exact ⟨⟩
  · rintro _ ⟨x, rfl⟩
    exact hA x
  · intro z hz
    let S : IntermediateField ℚ ℂ := Subfield.toIntermediateField (ρ.e i b).fieldRange fun r => by
      simpa using SubfieldClass.ratCast_mem (ρ.e i b).fieldRange r
    have hS : A ⊔ B ≤ S := sup_le (by rintro _ ⟨x, rfl⟩; exact hLe ⟨x, rfl⟩) (by rintro _ ⟨x, rfl⟩; exact hall x)
    exact hS hz
  · refine ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, hH', (j : H →+* ℂ), ?_, fun x => hB x⟩
    ext x
    exact j.commutes x
  · obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_isRay hmN hH'
    intro z hz
    haveI : NeZero (m * N) := ⟨hmN⟩
    have hζ' := hζ.map_of_injective (j : H →+* ℂ).injective
    obtain ⟨k, -, rfl⟩ := hζ'.eq_pow_of_pow_eq_one hz
    exact pow_mem (hB ζ) k

theorem range_e_le_ek (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (b : Bool) (k : ℕ) :
    (ρ.e i b).fieldRange ≤ (ρ.ek i b k).fieldRange := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, c, -, rfl⟩ := IsFractionRing.div_surjective (A := D.ntw.O i) y
  rw [map_div₀]
  have ha : ρ.e i b (algebraMap (D.ntw.O i) _ a) = ρ.eOk i b k (algebraMap (D.ntw.O i) (D.ntw.Ok i k) a) :=
    (hρ.ek_e i b k a).symm
  have hc : ρ.e i b (algebraMap (D.ntw.O i) _ c) = ρ.eOk i b k (algebraMap (D.ntw.O i) (D.ntw.Ok i k) c) :=
    (hρ.ek_e i b k c).symm
  rw [ha, hc]
  exact div_mem ⟨_, rfl⟩ ⟨_, rfl⟩

theorem exists_field_k (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (b : Bool)
    (hRF : GlobalTheory.NT.RayField)
    (hray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (m N : ℕ) (hm : D.host.g 0 * D.host.g 1 ∣ m) (hm' : m ∣ D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde')
    (hN : N ≠ 0) (hNl : N.Coprime (D.ntw.l i)) (k : ℕ) :
    ∃ L : IntermediateField ℚ ℂ, FiniteDimensional ℚ L ∧ (IsGalois ℚ D.LL0 → IsGalois ℚ L) ∧
      (embLL0 D).fieldRange ≤ L.toSubfield ∧ L.toSubfield ≤ (ρ.ek i b k).fieldRange ∧
      GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (m * N) L.toSubfield ∧ (∀ z : ℂ, z ^ (m * N) = 1 → z ∈ L) ∧
      ∀ z : ℂ, z ^ (D.ntw.l i ^ k) = 1 → z ∈ L := by
  obtain ⟨L, hfin, hgal, h1, h2, ⟨H, i1, i2, i3, i4, hH, jj, hjj, hv⟩, hroot⟩ :=
    exists_field D ρ hρ i b hRF hray m N hm hm' hN hNl
  have hlp : (D.ntw.l i).Prime := (D.ntw.lPrime i).out
  haveI : NeZero (D.ntw.l i ^ k) := ⟨pow_ne_zero _ hlp.ne_zero⟩
  set ζ : ℂ := ρ.eOk i b k (D.ntw.zk i k : D.ntw.Ok i k) with hζdef
  have hζ : IsPrimitiveRoot ζ (D.ntw.l i ^ k) := (D.ntw.zk_prim i k).map_of_injective (ρ.eOk_injective i b k)
  let p : Polynomial ℚ := Polynomial.X ^ (D.ntw.l i ^ k) - 1
  have hp0 : p ≠ 0 := by
    simpa [p] using Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero (NeZero.ne (D.ntw.l i ^ k))) (1 : ℚ)
  have hroots : ∀ z : ℂ, z ∈ p.rootSet ℂ ↔ z ^ (D.ntw.l i ^ k) = 1 := fun z => by
    rw [Polynomial.mem_rootSet, and_iff_right hp0]
    simp [p, sub_eq_zero]
  let C : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (p.rootSet ℂ)
  haveI hCs : Polynomial.IsSplittingField ℚ C p :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI : FiniteDimensional ℚ C := Polynomial.IsSplittingField.finiteDimensional C p
  refine ⟨L ⊔ C, inferInstance, fun hG => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have gL : IsGalois ℚ L := hgal hG
    haveI : Normal ℚ C := Normal.of_isSplittingField p
    have gC : IsGalois ℚ C := ⟨⟩
    haveI : Normal ℚ ↥(L ⊔ C) := @IntermediateField.normal_sup ℚ ℂ _ _ _ L C gL.to_normal gC.to_normal
    exact ⟨⟩
  · exact fun z hz => (le_sup_left : L ≤ L ⊔ C) (h1 hz)
  · intro z hz
    let S : IntermediateField ℚ ℂ := Subfield.toIntermediateField (ρ.ek i b k).fieldRange fun r => by
      simpa using SubfieldClass.ratCast_mem (ρ.ek i b k).fieldRange r
    have hS : L ⊔ C ≤ S := by
      refine sup_le (fun x hx => range_e_le_ek D ρ hρ i b k (h2 hx)) ?_
      rw [IntermediateField.adjoin_le_iff]
      intro z hz
      obtain ⟨t, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one ((hroots z).1 hz)
      exact pow_mem (⟨_, rfl⟩ : ζ ∈ (ρ.ek i b k).fieldRange) t
    exact hS hz
  · exact ⟨H, i1, i2, i3, i4, hH, jj, hjj, fun x => (le_sup_left : L ≤ L ⊔ C) (hv x)⟩
  · exact fun z hz => (le_sup_left : L ≤ L ⊔ C) (hroot z hz)
  · intro z hz
    exact (le_sup_right : C ≤ L ⊔ C) (IntermediateField.subset_adjoin ℚ _ ((hroots z).2 hz))

theorem exists_rayField_le (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (b : Bool)
    (hRF : GlobalTheory.NT.RayField)
    (hray : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (m N : ℕ) (hm : D.host.g 0 * D.host.g 1 ∣ m) (hm' : m ∣ D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde')
    (hN : N ≠ 0) (hNl : N.Coprime (D.ntw.l i)) :
    (∃ L : IntermediateField ℚ ℂ, FiniteDimensional ℚ L ∧ (IsGalois ℚ D.LL0 → IsGalois ℚ L) ∧
      (embLL0 D).fieldRange ≤ L.toSubfield ∧ L.toSubfield ≤ (ρ.e i b).fieldRange ∧
      GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (m * N) L.toSubfield ∧ ∀ z : ℂ, z ^ (m * N) = 1 → z ∈ L) ∧
    ∀ k : ℕ, ∃ L : IntermediateField ℚ ℂ, FiniteDimensional ℚ L ∧ (IsGalois ℚ D.LL0 → IsGalois ℚ L) ∧
      (embLL0 D).fieldRange ≤ L.toSubfield ∧ L.toSubfield ≤ (ρ.ek i b k).fieldRange ∧
      GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.RayIn D (m * N) L.toSubfield ∧ (∀ z : ℂ, z ^ (m * N) = 1 → z ∈ L) ∧
      ∀ z : ℂ, z ^ (D.ntw.l i ^ k) = 1 → z ∈ L :=
  ⟨exists_field D ρ hρ i b hRF hray m N hm hm' hN hNl, exists_field_k D ρ hρ i b hRF hray m N hm hm' hN hNl⟩

end GlobalTheory.RayInFrac
