import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsLocalCoeffRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

private theorem length_self_eq_of_ringEquiv {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) :
    Module.length S S = Module.length T T := by
  rw [Module.length_eq_coheight, Module.length_eq_coheight]
  have := Ideal.coheight_comap_of_surjective (e : S →+* T) e.surjective ⊥
  have hb : Ideal.comap (e : S →+* T) ⊥ = ⊥ := Ideal.comap_bot_of_injective _ e.injective
  rw [hb] at this
  exact this

private theorem length_localizedModule_quot {R : Type*} [CommRing R] (J W : Ideal R) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J)) =
      Module.length (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
        (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  let S := Localization.AtPrime W
  have hJ : (J : Submodule R R).localized' S W.primeCompl (Algebra.linearMap R S) =
      J.map (algebraMap R S) := by
    rw [Submodule.localized'_eq_span, Ideal.map]
    rfl
  let e := (IsLocalizedModule.linearEquiv W.primeCompl
    ((J : Submodule R R).toLocalizedQuotient' S W.primeCompl (Algebra.linearMap R S))
    (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J))).extendScalarsOfIsLocalization W.primeCompl S
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]
  exact Module.length_eq_of_surjective Ideal.Quotient.mk_surjective

theorem LocCycleLocalQuot.proof (h₂ : LocalQuotPrimes.Statement.{u}) : LocCycleLocalQuot.Statement.{u} := by
  intro R _ P U _ J W hPJ hW hPW hWU
  obtain ⟨hup, hdown⟩ := h₂ R P U (hPW.trans hWU)
  obtain ⟨hpW, hcW⟩ := hup W hW hPW hWU

  have hmin : W ∈ J.minimalPrimes ↔ W.map (localQuotMap P U) ∈ (J.map (localQuotMap P U)).minimalPrimes := by
    constructor
    · rintro ⟨⟨-, hJW⟩, hm⟩
      refine ⟨⟨hpW, Ideal.map_mono hJW⟩, fun q hq hqW => ?_⟩
      have := hq.1
      obtain ⟨hPq, hqU, hqe⟩ := hdown q hq.1
      have h := hm ⟨Ideal.comap_isPrime _ q, Ideal.le_comap_map.trans (Ideal.comap_mono hq.2)⟩
        ((Ideal.comap_mono hqW).trans hcW.le)
      rw [← hqe]
      exact Ideal.map_mono h
    · rintro ⟨⟨-, hJW⟩, hm⟩
      refine ⟨⟨hW, Ideal.le_comap_map.trans ((Ideal.comap_mono hJW).trans hcW.le)⟩, fun Q hQ hQW => ?_⟩
      obtain ⟨hQp, hQc⟩ := hup Q hQ.1 (hPJ.trans hQ.2) (hQW.trans hWU)
      have h := hm ⟨hQp, Ideal.map_mono hQ.2⟩ (Ideal.map_mono hQW)
      rw [← hcW, ← hQc]
      exact Ideal.comap_mono h
  unfold locCycle
  by_cases h : W ∈ J.minimalPrimes
  swap
  · rw [dif_neg h, dif_neg (mt hmin.2 h)]
  rw [dif_pos h, dif_pos (hmin.1 h)]
  have := hW
  have := hpW
  set φ := localQuotMap P U with hφ
  obtain ⟨p, hp⟩ : ∃ p, W.map φ = p := ⟨_, rfl⟩
  rw [hp] at hpW hcW
  have := hpW
  have hφp : ∀ x : R, φ x ∈ p ↔ x ∈ W := fun x => by rw [← Ideal.mem_comap, hcW]

  have hrep : ∀ a : localQuot P U, ∃ r u : R, u ∉ U ∧ a * φ u = φ r := by
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨⟨r, u⟩, rfl⟩ := IsLocalization.mk'_surjective U.primeCompl b
    refine ⟨r, u, u.2, ?_⟩
    simp only [hφ, localQuotMap, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
  have hnum : ∀ (t : localQuot P U) (r' u' : R), t ∉ p → u' ∉ U → t * φ u' = φ r' → r' ∉ W := by
    intro t r' u' ht hu' hr' hmem
    rw [← hφp, ← hr'] at hmem
    rcases hpW.mem_or_mem hmem with h | h
    · exact ht h
    · exact hu' (hWU ((hφp u').1 h))
  let ψ : (Localization.AtPrime W) →+* (Localization.AtPrime p) := Localization.localRingHom W p φ hcW.symm
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    obtain ⟨r, u, hu, hr⟩ := hrep a
    obtain ⟨r', u', hu', hr'⟩ := hrep t
    have hs : r' * u ∈ W.primeCompl :=
      W.primeCompl.mul_mem (hnum t r' u' t.2 hu' hr') fun h => hu (hWU h)
    refine ⟨IsLocalization.mk' _ (r * u') ⟨r' * u, hs⟩, ?_⟩
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq]
    congr 1
    simp only [map_mul]
    linear_combination (φ r) * hr' - (φ r') * hr

  have hker : Ideal.comap ψ ⊥ ≤ J.map (algebraMap R (Localization.AtPrime W)) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective W.primeCompl x
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨t, ht⟩, htr⟩ := hx
    obtain ⟨r', u', hu', hr'⟩ := hrep t
    have hr'W := hnum t r' u' ht hu' hr'
    have h0 : φ (r' * r) = 0 := by
      rw [map_mul, ← hr', mul_right_comm, htr, zero_mul]
    rw [hφ, localQuotMap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      IsLocalization.mem_map_algebraMap_iff U.primeCompl] at h0
    obtain ⟨⟨⟨i, hi⟩, v⟩, hv⟩ := h0
    rw [← map_mul, IsLocalization.eq_iff_exists U.primeCompl] at hv
    obtain ⟨c, hc⟩ := hv
    have hcW : (c : R) * r' * v ∈ W.primeCompl :=
      W.primeCompl.mul_mem (W.primeCompl.mul_mem (fun h => c.2 (hWU h)) hr'W) fun h => v.2 (hWU h)
    have hmemP : (c : R) * r' * v * r ∈ P := by
      have : (c : R) * (r' * r * v) = c * r' * v * r := by ring
      rw [← this, hc]
      exact P.mul_mem_left _ hi
    have hrJ : algebraMap R (Localization.AtPrime W) r ∈ J.map (algebraMap R (Localization.AtPrime W)) := by
      rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units (Localization.AtPrime W) ⟨_, hcW⟩), ← map_mul]
      exact Ideal.mem_map_of_mem _ (hPJ hmemP)
    show IsLocalization.mk' (Localization.AtPrime W) r s ∈ _
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ hrJ

  let : CommRing (Localization.AtPrime p) := inferInstance
  have hcomp : ψ.comp (algebraMap R (Localization.AtPrime W)) = (algebraMap (localQuot P U) (Localization.AtPrime p)).comp φ :=
    RingHom.ext fun x => Localization.localRingHom_to_map W p φ hcW.symm x
  have hI : (J.map φ).map (algebraMap (localQuot P U) (Localization.AtPrime p)) = (J.map (algebraMap R (Localization.AtPrime W))).map ψ := by
    rw [Ideal.map_map, Ideal.map_map, hcomp]
  let g := (Ideal.Quotient.mk ((J.map φ).map (algebraMap (localQuot P U) (Localization.AtPrime p)))).comp ψ
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hψ
  have hgk : J.map (algebraMap R (Localization.AtPrime W)) = RingHom.ker g := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, hI, Ideal.comap_map_of_surjective _ hψ, sup_eq_left.mpr hker]
  have key := length_self_eq_of_ringEquiv ((Ideal.quotEquivOfEq hgk).trans (RingHom.quotientKerEquivOfSurjective hg))
  rw [← length_localizedModule_quot, ← length_localizedModule_quot] at key
  subst hp
  exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ)) key

end GroundTheory.Heights₂.Heights.NumbersDVR
