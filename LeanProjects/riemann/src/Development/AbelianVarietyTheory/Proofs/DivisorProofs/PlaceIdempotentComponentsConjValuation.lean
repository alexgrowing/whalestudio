import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalRingCardinality.SpanPowerMembership.Places
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjVal

open GlobalTheory.IdemSupport

theorem valuation_cP {D : D7} (Q : HeightOneSpectrum (𝓞 D.host.E)) (x : D.host.E) :
    (cP Q).valuation D.host.E (star x) = Q.valuation D.host.E x := by
  have : cP Q = Formalism.BasicNotions.Examples₂.PlacesToy.conjW Q := by
    ext r
    have := Formalism.BasicNotions.Examples₂.PlacesToy.mem_conjW_pow Q r 1
    rw [pow_one, pow_one] at this
    rw [this, mem_cP]
    rfl
  rw [this, Formalism.BasicNotions.Examples₂.PlacesToy.valuation_conjW, star_star]

theorem eq_of_le_iff {a b : WithZero (Multiplicative ℤ)}
    (h : ∀ c, c ≠ 0 → (a ≤ c ↔ b ≤ c)) : a = b := by
  have key : ∀ {a b : WithZero (Multiplicative ℤ)}, (∀ c, c ≠ 0 → a ≤ c → b ≤ c) → b ≤ a := by
    intro a b h
    by_cases ha : a = 0
    · by_contra hb
      have hb0 : b ≠ 0 := fun e => hb (by rw [e]; exact zero_le)
      have h1 := h (WithZero.exp (WithZero.log b - 1)) WithZero.exp_ne_zero (by rw [ha]; exact zero_le)
      rw [← WithZero.exp_log hb0, WithZero.exp_le_exp, WithZero.log_exp] at h1
      omega
    · exact h a ha le_rfl
  exact le_antisymm (key fun c hc => (h c hc).2) (key fun c hc => (h c hc).1)

theorem int_iff {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {e : FiniteAdeleRing (𝓞 E) E}
    (h1 : e P = 1) (h0 : ∀ R, R ≠ P → e R = 0) (y : FiniteAdeleRing (𝓞 E) E) {k : E} (hk : k ≠ 0) :
    (∀ R : HeightOneSpectrum (𝓞 E), Valued.v ((e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) R) ≤ 1) ↔
      Valued.v (y P) ≤ P.valuation E k := by
  have e1 : ∀ R, (e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) R =
      e R * (y R * algebraMap E (R.adicCompletion E) k⁻¹) := fun R => rfl
  have hv : 0 < P.valuation E k := zero_lt_iff.2 (by simpa using hk)
  have e2 : Valued.v ((e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) P) ≤ 1 ↔
      Valued.v (y P) ≤ P.valuation E k := by
    rw [e1, h1, one_mul, map_mul, Formalism.UG.P.levelaf_valued_algebraMap, map_inv₀, mul_inv_le_iff₀ hv, one_mul]
  rw [← e2]
  refine ⟨fun h => h P, fun h R => ?_⟩
  by_cases hR : R = P
  · rw [hR]; exact h
  · rw [e1, h0 R hR, zero_mul, map_zero]
    exact zero_le

theorem map_three {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B ≃+* C) (a b c : A) :
    g (f (a * (b * c))) = g (f a) * (g (f b) * g (f c)) := by
  simp only [map_mul]

theorem conj_mem_iff {D : D7} (e z : AE D) (k : D.host.E) :
    finPart D (cA D e * (cA D z * incA D (star k)⁻¹)) ∈ intAE D ↔ finPart D (e * (z * incA D k⁻¹)) ∈ intAE D := by
  rw [← star_inv₀, ← cA_incA, ← RingHom.map_mul, ← RingHom.map_mul]
  refine ⟨fun h => ?_, finPart_cA_mem⟩
  have := finPart_cA_mem h
  rwa [cA_cA] at this

set_option maxHeartbeats 800000 in

theorem components_and_conj_valuation : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → (∀ (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) ∧ ∀ (z : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (ι (finPart D (cA D z)) (GlobalTheory.IdemSupport.cP Q)) = Valued.v (ι (finPart D z) Q) := by
  intro D ι hinc hint hid
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  choose ε hε using hid
  have hd : ∀ P, IsDelta Φ P (ε P) := fun P => (tie_iff hΦ (hε P).1.1 (hε P).2.1 P).1 (hε P).1.2.2
  refine ⟨fun e P h => ?_, fun z Q => ?_⟩
  · rw [delta_unique hΦ (delta_of_isIdemAt hΦ h) (hd P)]
    exact (hε P).2
  have hc : cA D (ε Q) = ε (cP Q) := delta_unique hΦ (delta_conj hΦ (hd Q)) (hd _)
  have key : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (y : AE D) (k : D.host.E), k ≠ 0 →
      (finPart D (ε P * (y * incA D k⁻¹)) ∈ intAE D ↔ Valued.v (ι (finPart D y) P) ≤ P.valuation D.host.E k) := by
    intro P y k hk
    have : ι (finPart D (incA D k⁻¹)) = algebraMap D.host.E _ k⁻¹ := hinc k⁻¹
    rw [hint, map_three, this]
    exact int_iff (hε P).2.2.1 (hε P).2.2.2 _ hk
  refine eq_of_le_iff fun c hc0 => ?_
  obtain ⟨k, rfl⟩ := Q.valuation_surjective D.host.E c
  have hk : k ≠ 0 := fun e => hc0 (by rw [e, Valuation.map_zero])
  have h1 := key (cP Q) (cA D z) (star k) (star_ne_zero.2 hk)
  rw [valuation_cP, ← hc, conj_mem_iff] at h1
  exact h1.symm.trans (key Q z k hk)

end GlobalTheory.ConjVal
