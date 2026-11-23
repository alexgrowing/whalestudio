import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DedekindZetaEqSumRealEisenstein
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverEqFinrankOfAbsNormEqOfNotMemSq
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mem.RaySplit

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem.Fld

section General

theorem not_dvd_discr_iff_ramificationIdx (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ¬ (p : ℤ) ∣ discr E ↔ ∀ P : Ideal (𝓞 E), P.IsPrime → (p : 𝓞 E) ∈ P → P.ramificationIdx ℤ = 1 := by
  rw [NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) (Nat.prime_iff_prime_int.mp hp)]
  refine forall_congr' fun P => forall_congr' fun hP => ?_
  rw [Int.cast_natCast]
  refine forall_congr' fun hlP => ?_
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hp.ne_zero (by simpa using hlP)
  have := hP.isMaximal hP0
  have : (P.under ℤ).IsMaximal := inferInstance
  have hne : P.under ℤ ≠ ⊥ := by
    intro h0
    have h1 : (p : ℤ) ∈ P.under ℤ := by rw [Ideal.under_def, Ideal.mem_comap]; simpa using hlP
    rw [h0] at h1
    exact hp.ne_zero (by simpa using h1)
  have : Finite (ℤ ⧸ P.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have : Finite (P.under ℤ).ResidueField := inferInstance
  exact Ideal.ramificationIdx_eq_one_iff.symm

theorem not_mem_sq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 E)} [hP : P.IsPrime]
    (hv : (p : 𝓞 E) ∈ P) (he : P.ramificationIdx ℤ = 1) : (p : 𝓞 E) ∉ P ^ 2 := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hb] at he
  intro h2
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h2

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem exists_under {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 L)) [P.IsPrime] (h : (p : 𝓞 L) ∈ P) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 K), P.LiesOver 𝔭.asIdeal ∧ (p : 𝓞 K) ∈ 𝔭.asIdeal := by
  have h1 : (p : 𝓞 K) ∈ P.under (𝓞 K) := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]; exact h
  refine ⟨⟨P.under (𝓞 K), inferInstance, fun h0 => ?_⟩, ⟨rfl⟩, h1⟩
  rw [h0] at h1
  exact hp.ne_zero (by simpa using h1)

theorem not_dvd_discr_of_unramIn [IsGalois K L] {p : ℕ} (hp : p.Prime) (hK : ¬ (p : ℤ) ∣ discr K)
    (hu : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal → UnramIn L 𝔭) : ¬ (p : ℤ) ∣ discr L := by
  rw [not_dvd_discr_iff_ramificationIdx _ hp] at hK ⊢
  intro P hP h
  obtain ⟨𝔭, hPo, h𝔭⟩ := exists_under (K := K) hp P h
  have := 𝔭.isMaximal
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have : P.IsMaximal := hP.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P)
  have h1 : P.inertia (L ≃ₐ[K] L) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 fun τ hτ => hu 𝔭 h𝔭 τ ⟨P, hP, hPo, hτ⟩
  have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) 𝔭.asIdeal P
  rw [h1, Subgroup.card_bot, Ideal.ramificationIdxIn_eq_ramificationIdx _ P (L ≃ₐ[K] L)] at h2
  rw [Ideal.ramificationIdx_tower (R := ℤ) 𝔭.asIdeal P, hK _ 𝔭.isPrime h𝔭, ← h2]

theorem heckeIdeal_asIdeal (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔮 : HeightOneSpectrum (𝓞 K)) :
    heckeIdeal L χ 𝔮.asIdeal = heckeVal L χ 𝔮 := by
  classical
  unfold heckeIdeal
  rw [finprod_eq_single _ 𝔮]
  · rw [Associates.count_self 𝔮.associates_irreducible, pow_one]
  · intro 𝔭 hne
    rw [Associates.count_eq_zero_of_ne 𝔭.associates_irreducible 𝔮.associates_irreducible, pow_zero]
    intro h
    exact hne (HeightOneSpectrum.ext (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 h)))

theorem not_dvd_span {p c : ℕ} (hp : p.Prime) (hc : ¬ p ∣ c) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : (p : 𝓞 K) ∈ 𝔭.asIdeal) : ¬ 𝔭.asIdeal ∣ Ideal.span {(c : 𝓞 K)} := by
  rw [Ideal.dvd_span_singleton]
  intro h'
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hc)
  have h1 := congrArg (Int.cast : ℤ → 𝓞 K) hab
  push_cast at h1
  exact 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (h1 ▸ add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h')))

theorem absNorm_eq_of_span {𝔮 : Ideal (𝓞 K)} (hR : IsRayField K L 𝔮) (hK : IsEmpty (K →+* ℝ))
    (𝔭 : HeightOneSpectrum (𝓞 K)) {π : 𝓞 K} (hπ : 𝔭.asIdeal = Ideal.span {π}) (h1 : π - 1 ∈ 𝔮)
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] [hPo : P.LiesOver 𝔭.asIdeal] :
    Ideal.absNorm P = Ideal.absNorm 𝔭.asIdeal := by
  have := hR.1
  have hcop : IsCoprime 𝔭.asIdeal 𝔮 := by
    rw [hπ]
    exact Ideal.isCoprime_iff_exists.2 ⟨π, Ideal.mem_span_singleton_self _, -(π - 1), neg_mem h1, by ring⟩
  have hnd : ¬ 𝔭.asIdeal ∣ 𝔮 := fun h => 𝔭.prime.not_unit (hcop.isUnit_of_dvd' dvd_rfl h)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact 𝔭.ne_bot (by simpa using hπ)
  have hχ := (hR.2.2.2 𝔭.asIdeal 𝔭.ne_bot hcop).2 ⟨π, 1,
    ⟨hπ0, one_ne_zero, hπ ▸ hcop, by rw [Ideal.span_singleton_one, ← Ideal.one_eq_top]; exact isCoprime_one_left,
      h1, fun φ => hK.elim φ⟩, by simp [hπ]⟩
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hfP : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have hfv : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have := 𝔭.isPrime
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (L ≃ₐ[K] L) P
  have hσ1 : σ = 1 := GlobalTheory.RayMaximal.eq_of_forall_char fun χ => Units.ext (by
    rw [← heckeVal_of_unramIn L χ (hR.2.1 𝔭 hnd) ((isFrob_iff L 𝔭 σ).2 ⟨P, hP, hPo, hσ⟩), ← heckeIdeal_asIdeal,
      hχ χ, map_one, Units.val_one])
  have hle : Nat.card (𝓞 L ⧸ P) ≤ Nat.card (𝓞 K ⧸ 𝔭.asIdeal) := by
    refine card_le_of_pow_eq_self Finite.one_lt_card fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h2 := hσ x
    rw [hσ1, ← hPo.over] at h2
    rw [← map_pow]
    refine (Ideal.Quotient.eq.2 ?_).symm
    simpa using h2
  have hinj : Function.Injective (algebraMap (𝓞 K ⧸ 𝔭.asIdeal) (𝓞 L ⧸ P)) := FaithfulSMul.algebraMap_injective _ _
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_eq_of_bijective _ (hinj.bijective_of_nat_card_le hle)).symm

theorem dvd_of_dvd_discr {c : ℕ} (hR : IsRayField K L (Ideal.span {(c : 𝓞 K)})) {p : ℕ} (hp : p.Prime)
    (h : (p : ℤ) ∣ discr L) : p ∣ c ∨ (p : ℤ) ∣ discr K := by
  have := hR.1
  by_contra hc
  rw [not_or] at hc
  exact not_dvd_discr_of_unramIn hp hc.2 (fun 𝔭 h𝔭 => hR.2.1 𝔭 (not_dvd_span hp hc.1 𝔭 h𝔭)) h

theorem absNorm_eq_of_mul (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) {π π' : 𝓞 K} (h : π * π' = p)
    (hu : ¬ IsUnit π) (hu' : ¬ IsUnit π') : Ideal.absNorm (Ideal.span {π}) = p := by
  have h1 : Ideal.absNorm (Ideal.span {π}) * Ideal.absNorm (Ideal.span {π'}) = p ^ 2 := by
    rw [← map_mul, Ideal.span_singleton_mul_span_singleton, h, Ideal.absNorm_span_singleton,
      ← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap, RingOfIntegers.rank, h2]
    simp
  obtain ⟨i, hi, e⟩ := (Nat.dvd_prime_pow hp).1 ⟨_, h1.symm⟩
  interval_cases i
  · exact absurd (Ideal.span_singleton_eq_top.1 (Ideal.absNorm_eq_one_iff.1 (by simpa using e))) hu
  · simpa using e
  · rw [e] at h1
    have h3 := (Nat.mul_eq_left (pow_ne_zero 2 hp.ne_zero)).1 h1
    exact absurd (Ideal.span_singleton_eq_top.1 (Ideal.absNorm_eq_one_iff.1 h3)) hu'

theorem ncard_primesOver_eq {c : ℕ} (hR : IsRayField K L (Ideal.span {(c : 𝓞 K)})) (hK : IsEmpty (K →+* ℝ))
    (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr L) {π π' : 𝓞 K} (h : π * π' = p)
    (hu : ¬ IsUnit π) (hu' : ¬ IsUnit π') (hc : (c : 𝓞 K) ∣ π - 1) (hc' : (c : 𝓞 K) ∣ π' - 1) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L)).ncard = Module.finrank ℚ L := by
  refine GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq L p hp fun P hP hpP => ?_
  refine ⟨?_, not_mem_sq hp hpP ((not_dvd_discr_iff_ramificationIdx L hp).1 hd P hP.isPrime hpP)⟩
  obtain ⟨𝔭, hPo, h𝔭⟩ := exists_under (K := K) hp P hpP
  have key : ∀ a : 𝓞 K, Ideal.absNorm (Ideal.span {a}) = p → (c : 𝓞 K) ∣ a - 1 → a ∈ 𝔭.asIdeal →
      Ideal.absNorm P = p := fun a hN ha hm => by
    have hpr : (Ideal.span {a}).IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hp)
    have hb : Ideal.span {a} ≠ ⊥ := fun h0 => hp.ne_zero (by rw [← hN, h0, Ideal.absNorm_bot])
    have e : Ideal.span {a} = 𝔭.asIdeal :=
      (hpr.isMaximal hb).eq_of_le 𝔭.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hm)
    rw [absNorm_eq_of_span hR hK 𝔭 e.symm (Ideal.mem_span_singleton.2 ha) P, ← e, hN]
  rcases 𝔭.isPrime.mem_or_mem (h ▸ h𝔭) with hm | hm
  · exact key π (absNorm_eq_of_mul h2 hp h hu hu') hc hm
  · exact key π' (absNorm_eq_of_mul h2 hp ((mul_comm _ _).trans h) hu' hu) hc' hm

end General

section Host

variable {R : Ranks} (H : Host R)

abbrev condIdeal : Ideal (𝓞 H.K) := Ideal.span {((H.QS * H.q * H.d : ℕ) : 𝓞 H.K)}

theorem cond_ne_zero : H.QS * H.q * H.d ≠ 0 := by
  have h1 := H.hyp.1.ne_zero
  have h2 := H.hyp.2.1.ne_zero
  have h3 := H.QS_pos.ne'
  positivity

theorem condIdeal_ne_bot : condIdeal H ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast cond_ne_zero H

theorem finrank_K : Module.finrank ℚ H.K = 2 :=
  Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos (H.sqd_sq)

theorem discr_K : NumberField.discr H.K = -(H.d : ℤ) :=
  discr_eq_neg_of_sq_eq (finrank_K H) H.hyp.2.1.squarefree (by have := H.hyp.2.2.2.1; omega)
    (Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq))

theorem isEmpty_real : IsEmpty (H.K →+* ℝ) := ⟨fun φ => by
  obtain ⟨x, hx⟩ : ∃ x : H.K, x ^ 2 = -(H.d : H.K) := ⟨_, Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq)⟩
  have h := congrArg φ hx
  rw [map_pow, map_neg, map_natCast] at h
  have h5 : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  nlinarith [sq_nonneg (φ x)]⟩

variable {H} {M : Type} [Field M] [NumberField M] [Algebra H.K M]

theorem isGalois_of_ray (hM : IsRayField H.K M (condIdeal H)) : IsGalois H.K M :=
  have := hM.1
  inferInstance

theorem comm_of_ray (hM : IsRayField H.K M (condIdeal H)) (σ τ : M ≃ₐ[H.K] M) : σ * τ = τ * σ :=
  have := hM.1
  mul_comm' σ τ

theorem unr_of_ray (hM : IsRayField H.K M (condIdeal H)) (p : ℕ) (hp : p.Prime) (h : (p : ℤ) ∣ discr M) :
    p ∣ H.QS * H.q * H.d := by
  rcases dvd_of_dvd_discr hM hp h with h | h
  · exact h
  · rw [discr_K, dvd_neg] at h
    exact Dvd.dvd.mul_left (by exact_mod_cast h) _

end Host

end GlobalTheory.Mem.RaySplit

end
