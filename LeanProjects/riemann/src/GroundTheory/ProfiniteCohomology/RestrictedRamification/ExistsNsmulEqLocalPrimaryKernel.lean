import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteSetOfNsmulEqZeroQZ
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.RealPlaces
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem QZ.nsmul_mk (j : ℕ) (r : ℚ) : j • QZ.mk r = QZ.mk (j * r) := by
  have h := map_nsmul QZ.mkHom j r
  rw [nsmul_eq_mul] at h
  exact h.symm

open Classical in

def qzDiv (ℓ : ℕ) (q : QZ) : QZ :=
  if q = 0 then 0 else QZ.mk ((QZ.mk_surjective q).choose / ℓ)

theorem qzDiv_zero (ℓ : ℕ) : qzDiv ℓ 0 = 0 := by
  simp [qzDiv]

theorem nsmul_qzDiv {ℓ : ℕ} (hℓ : ℓ ≠ 0) (q : QZ) : ℓ • qzDiv ℓ q = q := by
  by_cases hq : q = 0
  · rw [hq, qzDiv_zero, smul_zero]
  · rw [qzDiv, if_neg hq, QZ.nsmul_mk]
    have hℓq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ
    rw [mul_div_cancel₀ _ hℓq]
    exact (QZ.mk_surjective q).choose_spec

variable {K : FiniteSubfield}

theorem eq_zero_inl_of_pow_nsmul_eq_zero {ℓ : ℕ} (hℓ : ℓ.Prime) (v : InfinitePlace K.1)
    (hv : ℓ ≠ 2 ∨ v.IsComplex) (t : localGaloisCohomology K 2 (.inl v)) (k : ℕ) (ht : ℓ ^ k • t = 0) :
    t = 0 := by
  rcases hv with h2 | hc
  · have h2t : 2 • t = 0 := by
      apply placeInv_injective (.inl v)
      rw [map_nsmul, map_zero]
      rcases placeInv_inl_eq_zero_or_eq_half v t with h | h
      · rw [h, smul_zero]
      · rw [h, two_nsmul, QZ.mk_half_add_mk_half]
    exact eq_zero_of_coprime_nsmul_eq_zero ((Nat.coprime_primes Nat.prime_two hℓ).2 (Ne.symm h2)) h2t ht
  · have := subsingleton_cohomology_two_of_isComplex v hc
    exact Subsingleton.elim (α := cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) _ _

variable (K) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include hℓ hS in

theorem exists_nsmul_eq_localPrimaryKernel (hK : ℓ ≠ 2 ∨ IsTotallyComplex K.1)
    (t : localPrimaryKernel K S ℓ) : ∃ s : localPrimaryKernel K S ℓ, ℓ • s = t := by
  classical
  obtain ⟨⟨k, hk⟩, hout, hsum⟩ := t.2
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have hinf : ∀ v : InfinitePlace K.1, (t : ⨁ v : Place K.1, localGaloisCohomology K 2 v) (.inl v) = 0 :=
    fun v => eq_zero_inl_of_pow_nsmul_eq_zero hℓ v (hK.imp id fun h => h.isComplex v) _ k (by
      have := congrArg (fun x : ⨁ v : Place K.1, localGaloisCohomology K 2 v => x (.inl v)) hk
      rwa [DFinsupp.smul_apply] at this)
  let e : ∀ v : HeightOneSpectrum (𝓞 K.1), localGaloisCohomology K 2 (.inr v) ≃+ QZ := fun v =>
    AddEquiv.ofBijective (placeInv (.inr v)) (placeInv_bijective_inr v)
  let f : ∀ v : Place K.1, localGaloisCohomology K 2 v → localGaloisCohomology K 2 v
    | .inl _ => fun _ => 0
    | .inr v => fun x => (e v).symm (qzDiv ℓ (e v x))
  have hf : ∀ v, f v 0 = 0 := by
    rintro (v | v)
    · rfl
    · change (e v).symm (qzDiv ℓ (e v 0)) = 0
      rw [map_zero, qzDiv_zero, map_zero]
  let s₀ : ⨁ v : Place K.1, localGaloisCohomology K 2 v := DFinsupp.mapRange f hf t.1
  have hs₀ : ℓ • s₀ = t := by
    refine DFinsupp.ext fun v => ?_
    rw [DFinsupp.smul_apply, DFinsupp.mapRange_apply]
    rcases v with v | v
    · change ℓ • (0 : localGaloisCohomology K 2 (.inl v)) = _
      rw [smul_zero, hinf v]
    · change ℓ • (e v).symm (qzDiv ℓ (e v _)) = _
      rw [← map_nsmul, nsmul_qzDiv hℓ0, AddEquiv.symm_apply_apply]
  obtain ⟨v₀, hv₀⟩ := exists_place_above K ℓ hℓ
  let c := sumPlaceInv K s₀
  let o : ⨁ v : Place K.1, localGaloisCohomology K 2 v :=
    DirectSum.of (fun v : Place K.1 => localGaloisCohomology K 2 v) (Sum.inr v₀) ((e v₀).symm c)
  let s : ⨁ v : Place K.1, localGaloisCohomology K 2 v := s₀ - o
  have hc : ℓ • c = 0 := by
    change ℓ • sumPlaceInv K s₀ = 0
    rw [← map_nsmul, hs₀, hsum]
  have hs : ℓ • s = t := by
    rw [smul_sub, hs₀, ← map_nsmul, ← map_nsmul, hc, map_zero, map_zero, sub_zero]
  refine ⟨⟨s, ⟨k + 1, ?_⟩, fun v hv => ?_, ?_⟩, Subtype.ext hs⟩
  · rw [pow_succ, mul_smul, hs, hk]
  · have hne : (.inr v : Place K.1) ≠ .inr v₀ := fun h => hv (by cases h; exact hS v₀ hv₀)
    change s₀ (.inr v) - o (.inr v) = 0
    rw [show o (.inr v) = 0 from DirectSum.of_eq_of_ne _ _ _ hne, sub_zero]
    change (e v).symm (qzDiv ℓ (e v (t.1 (.inr v)))) = 0
    rw [hout v hv, map_zero, qzDiv_zero, map_zero]
  · change sumPlaceInv K (s₀ - o) = 0
    rw [map_sub, sumPlaceInv_of]
    change c - e v₀ ((e v₀).symm c) = 0
    rw [AddEquiv.apply_symm_apply, sub_self]

set_option maxHeartbeats 1000000 in
include hℓ hS in

theorem exists_nsmul_eq_h2SUnits (hK : ℓ ≠ 2 ∨ IsTotallyComplex K.1)
    (y : AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) 2) ℓ) :
    ∃ z : AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) 2) ℓ, ℓ • z = y := by
  obtain ⟨ιs⟩ := nonempty_localEmbeddings K
  let E := sUnitsH2PrimaryEquiv K S ℓ hℓ hS ιs
  obtain ⟨s, hs⟩ := exists_nsmul_eq_localPrimaryKernel K S ℓ hℓ hS hK (E y)
  refine ⟨E.symm s, ?_⟩
  rw [← E.symm_apply_apply y, ← hs]
  exact (map_nsmul E.symm ℓ s).symm

end

end GroundTheory.ProfCoh
