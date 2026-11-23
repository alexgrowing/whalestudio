import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RayCharacterExtendsToIdeals

open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)

namespace GlobalTheory

theorem exists_ideal_character_of_unitary_hchar : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), χ.IsUnitary → ∃ (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ), m ≠ ⊥ ∧ X ⊥ = 0 ∧ X ⊤ = 1 ∧ (∀ I J, X (I * J) = X I * X J) ∧ (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) ∧ (∀ I, I ⊔ m ≠ ⊤ → X I = 0) ∧ (∀ P : HeightOneSpectrum (𝓞 K), X P.asIdeal = if χ.UnrAt P then ((χ.val P : ℂˣ) : ℂ) else 0) ∧ ∀ (β : 𝓞 K) (k : Kˣ), (k : K) = β → β - 1 ∈ m → X (Ideal.span {β}) = (((χ.inf k : ℂˣ) : ℂ))⁻¹ := by
  intro K _ _ χ hχ
  have hfin := GlobalTheory.Mem.UnrAe.finite_ramified χ
  choose n hn using GlobalTheory.Mem.UnrAe.exists_levelLe χ
  let S : Finset (HeightOneSpectrum (𝓞 K)) := hfin.toFinset
  have hS : ∀ P, P ∈ S ↔ ¬ χ.UnrAt P := fun P => by simp [S]
  let m : Ideal (𝓞 K) := ∏ P ∈ S, P.asIdeal ^ (n P + 1)
  have hdvd : ∀ P ∈ S, P.asIdeal ^ (n P + 1) ∣ m := fun P hP =>
    Finset.dvd_prod_of_mem (fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal ^ (n P + 1)) hP
  have hm : ∀ P : HeightOneSpectrum (𝓞 K), m ≤ P.asIdeal ↔ P ∈ S := by
    intro P
    constructor
    · intro h
      obtain ⟨Q, hQ, hQP⟩ := (P.prime.dvd_finset_prod_iff _).1 (Ideal.dvd_iff_le.2 h)
      have h1 : Q.asIdeal ≤ P.asIdeal := Ideal.le_of_dvd (P.prime.dvd_of_dvd_pow hQP)
      have h2 : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h1)
      exact h2 ▸ hQ
    · intro h
      exact Ideal.le_of_dvd ((dvd_pow_self _ (Nat.succ_ne_zero _)).trans (hdvd P h))
  have hm0 : m ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun P _ => pow_ne_zero _ P.ne_bot
  obtain ⟨X, h0, h1, hmul, hnorm, hz, hP⟩ := GlobalTheory.exists_multiplicative_ideal_extension K m
    (fun P => ((χ.val P : ℂˣ) : ℂ)) (fun P _ => hχ _)
  refine ⟨m, X, hm0, h0, h1, hmul, hnorm, hz, ?_, ?_⟩
  · intro P
    split_ifs with h
    · exact hP P fun h' => (hS P).1 ((hm P).1 h') h
    · apply hz
      rw [sup_eq_left.2 ((hm P).2 ((hS P).2 h))]
      exact P.isPrime.ne_top
  · intro β k hk hβ1
    have hβ : β ≠ 0 := by
      rintro rfl
      exact k.ne_zero (by simpa using hk)
    have hne : (Ideal.span {β} : Ideal (𝓞 K)) ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hβ
    have hval : ∀ (P : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K),
        Valued.v (algebraMap K (P.adicCompletion K) (r : K)) = P.intValuation r := by
      intro P r
      rw [← HeightOneSpectrum.valuation_of_algebraMap (K := K)]
      exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (r : K)
    have hnot : ∀ P ∈ S, β ∉ P.asIdeal := by
      intro P hPS h
      apply P.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have := P.asIdeal.sub_mem h ((hm P).2 hPS hβ1)
      simpa using this
    have hloc : ∀ P ∈ S, χ.locK P k = 1 := by
      intro P hPS
      have e : ((Formalism.L2.Host.atFin P k : (P.adicCompletion K)ˣ) : P.adicCompletion K)
          = algebraMap K (P.adicCompletion K) (β : K) := by
        rw [← hk]; rfl
      refine hn P _ ?_ ?_
      · unfold Formalism.L2.Host.IsUnitAt
        rw [e, hval]
        exact HeightOneSpectrum.intValuation_eq_one_iff.2 (hnot P hPS)
      · have e2 : algebraMap K (P.adicCompletion K) (β : K) - 1
            = algebraMap K (P.adicCompletion K) ((β - 1 : 𝓞 K) : K) := by simp
        rw [e, e2, hval, HeightOneSpectrum.intValuation_le_pow_iff_mem]
        exact Ideal.le_of_dvd ((pow_dvd_pow _ (Nat.le_succ _)).trans (hdvd P hPS)) hβ1
    have hpr := GlobalTheory.HeckeProduct.hchar_productRule K χ S
      (fun v hv => not_not.1 fun h => hv ((hS v).2 h)) k
    rw [Finset.prod_eq_one hloc, mul_one] at hpr
    let φ : Ideal (𝓞 K) →* ℂ :=
      { toFun := X, map_one' := by rw [Ideal.one_eq_top, h1], map_mul' := hmul }
    have hφ : ∀ I, φ I = X I := fun _ => rfl
    have hord : ∀ v : HeightOneSpectrum (𝓞 K), Formalism.L2.Host.ordF v k =
        ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {β} : Ideal (𝓞 K))).factors : ℕ) := by
      intro v
      unfold Formalism.L2.Host.ordF
      rw [hk]
      have : v.valuation K (β : K) = v.intValuation β := HeightOneSpectrum.valuation_of_algebraMap v β
      rw [this, HeightOneSpectrum.intValuation_if_neg _ hβ, WithZero.log_exp, neg_neg]
    have hfs : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
        ∏ᶠ (_ : v ∉ S), χ.val v ^ Formalism.L2.Host.ordF v k).Finite := by
      refine (GlobalTheory.HeckeProduct.finite_ordF k).subset fun v hv h => hv ?_
      simp only [h, zpow_zero, finprod_one]
    have key : X (Ideal.span {β}) = ((∏ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : v ∉ S),
        χ.val v ^ Formalism.L2.Host.ordF v k : ℂˣ) : ℂ) := by
      have e1 := (Units.coeHom ℂ).map_finprod hfs
      rw [Units.coeHom_apply] at e1
      rw [e1, ← hφ, ← Ideal.finprod_heightOneSpectrum_factorization hne,
        φ.map_finprod (Ideal.finite_mulSupport hne)]
      refine finprod_congr fun v => ?_
      rw [HeightOneSpectrum.maxPowDividing, map_pow, hφ, hord, Units.coeHom_apply]
      by_cases hv : v ∈ S
      · have hc : (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {β} : Ideal (𝓞 K))).factors = 0 := by
          by_contra hc
          have := (Associates.count_ne_zero_iff_dvd hne v.irreducible).1 hc
          exact hnot v hv (Ideal.dvd_span_singleton.1 this)
        simp [hc]
      · rw [hP v fun h => hv ((hm v).1 h)]
        simp [hv]
    rw [key, ← Units.val_inv_eq_inv_val, (inv_eq_of_mul_eq_one_right hpr)]

end GlobalTheory
