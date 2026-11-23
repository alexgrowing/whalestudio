import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdxEqRelIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterTrivialAtInertPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NoRatInert
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormCmPrimeInertPrimeSign

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

namespace GlobalTheory.InertValue

open GlobalTheory.InertTrivial

variable {D : D7}

theorem val_of_real_neg {N : ℕ} (χ : HeckeU D N) (a : D.host.Eˣ)
    (ha : D.host.conj (a : D.host.E) = a) (hneg : (∏ τ, embT D τ (a : D.host.E)).re < 0) :
    ((χ.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) = (-1) ^ N := by
  have h := χ.aut a
  have hsq : ∀ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ 2 = 1 := by
    intro τ
    have h2 : embT D τ (D.host.conj a) = starRingEnd ℂ (embT D τ a) :=
      D.host.conjE_apply (embT D τ) a
    rw [ha] at h2
    have h0 : embT D τ (a : D.host.E) ≠ 0 := (map_ne_zero _).2 a.ne_zero
    rw [div_pow, ← Complex.mul_conj', ← h2, pow_two, div_self (mul_ne_zero h0 h0)]
  have hp : ∀ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ (χ.n τ) =
      (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ)) ^ N := by
    intro τ
    obtain ⟨c, hc⟩ := χ.par τ
    have h0 : embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ) ≠ 0 := by
      intro h0
      have := hsq τ
      rw [h0] at this
      norm_num at this
    rw [show χ.n τ = 2 * c + N by omega, zpow_add₀ h0, zpow_mul, zpow_natCast, zpow_two, ← pow_two, hsq,
      one_zpow, one_mul]
  rw [Finset.prod_congr rfl (fun τ _ => hp τ), Finset.prod_pow] at h
  have hS : (∏ τ, (embT D τ (a : D.host.E) / (‖embT D τ (a : D.host.E)‖ : ℂ))) ^ 2 = 1 := by
    rw [← Finset.prod_pow]; exact Finset.prod_eq_one fun τ _ => hsq τ
  rcases (mul_self_eq_one_iff.1 (by rwa [pow_two] at hS)) with h1 | h1
  · exfalso
    rw [Finset.prod_div_distrib, ← Complex.ofReal_prod] at h1
    have h2 := eq_of_div_eq_one h1
    rw [h2, Complex.ofReal_re] at hneg
    exact absurd (Finset.prod_nonneg fun τ _ => norm_nonneg _) (not_le.2 hneg)
  · rw [h1] at h
    have h3 : ((-1 : ℂ) ^ N) * (-1) ^ N = 1 := by rw [← mul_pow]; simp
    linear_combination (-1 : ℂ) ^ N * h - ((χ.f (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) * h3

theorem hom_gen (N : ℕ) (ψ : (AE D)ˣ →* ℂˣ) (h1 : ∀ u, IntU D u → ψ u = 1)
    (h2 : ∀ y, ψ (y * sgU D y) = 1)
    (h3 : ∀ a : D.host.Eˣ, D.host.conj (a : D.host.E) = a → (∏ τ, embT D τ (a : D.host.E)).re < 0 →
      ((ψ (Units.map (inc D).toMonoidHom a) : ℂˣ) : ℂ) = (-1) ^ N)
    (h4 : ∀ (q : ℕ) (y : (AE D)ˣ), q.Prime → ¬ InertQ D q → (y : AE D) ∈ OhE D →
      (q : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D) ∈ OhE D → ψ y = 1) (B : Ideal (𝓞 D.host.E)) :
    B ≠ ⊥ → Ev D (Ideal.absNorm B) ∧ ∀ y, Gen D B y → ((ψ y : ℂˣ) : ℂ) = sgn D (Ideal.absNorm B) ^ N := by
  have huniq : ∀ {B y z}, Gen D B y → Gen D B z → ψ y = ψ z := fun hy hz => by
    have := h1 _ (hy.intU hz)
    rwa [map_mul, map_inv, mul_inv_eq_one] at this
  have hprime : ∀ P : Ideal (𝓞 D.host.E), Prime P →
      Ev D (Ideal.absNorm P) ∧ ∀ y, Gen D P y → ((ψ y : ℂˣ) : ℂ) = sgn D (Ideal.absNorm P) ^ N := by
    intro P hP
    have hP0 : P ≠ ⊥ := hP.ne_zero
    have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
    have hPm : P.IsMaximal := hPp.isMaximal hP0
    obtain ⟨hev, hfix, hmov⟩ := GlobalTheory.InertResidue.norm_prime D P hPm
    refine ⟨hev, fun y hy => ?_⟩
    by_cases hi : D.host.conj • P = P
    · obtain ⟨t, B, ht0, htc, e⟩ := GlobalTheory.T.exists_real_span_eq_conjFixedPrime_mul_relNorm D P hPp hP0 hi
      have hneg := GlobalTheory.NormSignInert.norm_neg D t P B ht0 htc hPm hi e
      have hB : B ≠ ⊥ := by
        rintro rfl
        exact ht0 (by simpa using e)
      obtain ⟨z, hz⟩ := exists_gen D B hB
      have htE : (t : D.host.E) ≠ 0 := by simpa using ht0
      have g1 := gen_span t (Units.mk0 _ htE) rfl
      have g2 := (hy.mul hz).mul hz.conj
      rw [← e] at g2
      have := huniq g1 g2
      rw [mul_assoc, map_mul, h2, mul_one] at this
      rw [← this, h3 _ htc hneg, (hfix hi).1]
    · obtain ⟨q, hq, hqP⟩ : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 D.host.E) ∈ P :=
        exists_prime_mem P hPp _ (by simpa [Ideal.absNorm_eq_zero_iff] using hP0) (Ideal.absNorm_mem P)
      rw [h4 q y hq ((hmov hi).2 q hq hqP) hy.1 (hy.inv_mul hqP), (hmov hi).1]
      simp
  induction B using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ B hB =>
    intro _
    rw [Ideal.isUnit_iff.1 hB, Ideal.absNorm_top]
    refine ⟨Ev.one, fun y hy => ?_⟩
    rw [h1 y ⟨hy.1, by simpa using hy.inv_mul (q := 1) Submodule.mem_top⟩, sgn_one]
    simp
  | h₃ C P hC hP ih =>
    intro _
    obtain ⟨e1, v1⟩ := hprime P hP
    obtain ⟨e2, v2⟩ := ih hC
    have n1 : Ideal.absNorm P ≠ 0 := fun h => hP.ne_zero (Ideal.absNorm_eq_zero_iff.1 h)
    have n2 : Ideal.absNorm C ≠ 0 := fun h => hC (Ideal.absNorm_eq_zero_iff.1 h)
    rw [map_mul]
    refine ⟨e1.mul e2 n1 n2, fun y hy => ?_⟩
    obtain ⟨a, ha⟩ := exists_gen D P hP.ne_zero
    obtain ⟨c, hc⟩ := exists_gen D C hC
    rw [huniq hy (ha.mul hc), map_mul, Units.val_mul, v1 a ha, v2 c hc, sgn_mul e1 e2 n1 n2, mul_pow]

set_option maxHeartbeats 800000 in

theorem character_at_inert_component : ∀ (D : D7) (N : ℕ) (χ : HeckeU D N) (y : 𝓞 D.host.E) (x : (AE D)ˣ), y ≠ 0 → (∀ q : ℕ, q.Prime → (InertQ D q → ZeroAt D q ((x : AE D) - inc D (y : D.host.E))) ∧ (¬ InertQ D q → ZeroAt D q ((x : AE D) - 1))) → ((χ.f x : ℂˣ) : ℂ) = sgn D (Ideal.absNorm (Ideal.span {y})) ^ N := by
  intro D N χ y x hy0 hx
  obtain ⟨hinv, ε, hε, h1, h2, h3⟩ := GlobalTheory.NormSum.HalfIdempotent.conj_involutive_and_exists_half_idempotent D
  have h1' : sgA D ε * sgA D ε = sgA D ε := by rw [← map_mul, h1]
  have he : (1 - (ε + sgA D ε)) * (1 - (ε + sgA D ε)) = 1 - (ε + sgA D ε) := by
    linear_combination h1 + h1' + 2 * h2
  have heO : 1 - (ε + sgA D ε) ∈ OhE D := sub_mem (one_mem _) (add_mem hε (VacMove.sgA_mem D hε))
  have hse : sgA D (1 - (ε + sgA D ε)) = 1 - (ε + sgA D ε) := by
    rw [map_sub, map_add, map_one, hinv, add_comm]
  have hunr : ∀ y : (AE D)ˣ, (y : AE D) ∈ OhE D →
      (1 - (ε + sgA D ε)) * ((y⁻¹ : (AE D)ˣ) : AE D) ∈ OhE D → χ.f (proj _ he y) = 1 := by
    intro y hy hy'
    refine χ.unr _ ⟨?_, ?_⟩ fun q hq hi => ?_
    · rw [proj_val]; exact add_mem (mul_mem heO hy) (sub_mem (one_mem _) heO)
    · rw [proj_inv]; exact add_mem hy' (sub_mem (one_mem _) heO)
    · convert VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) ((y : AE D) - 1) using 1
      rw [proj_val]; ring
  have hyE : (y : D.host.E) ≠ 0 := by simpa using hy0
  have key := (hom_gen N (χ.f.comp (proj _ he)) (fun u hu => hunr u hu.1 (mul_mem heO hu.2))
    (fun y => ?_) (fun a ha hneg => ?_) (fun q y hq hi hy hy' => hunr y hy ?_) (Ideal.span {y})
    (by simpa using hy0)).2 _ (gen_span y (Units.mk0 _ hyE) rfl)
  · have h0 : (ε + sgA D ε) * ((x : AE D) - 1) +
        (1 - (ε + sgA D ε)) * ((x : AE D) - inc D (y : D.host.E)) = 0 := by
      have z1 : (ε + sgA D ε) * ((x : AE D) - 1) = 0 := by
        refine (GlobalTheory.IntAdeleComplete.integral_separated_complete D).1 _
          (dvd_of_forall_prime (OhE D) _ fun q hq => ?_)
        by_cases hi : InertQ D q
        · exact VacMove.zeroAt_mul D hq ((h3 q hq).1 hi) _
        · rw [mul_comm]; exact VacMove.zeroAt_mul D hq ((hx q hq).2 hi) _
      have z2 : (1 - (ε + sgA D ε)) * ((x : AE D) - inc D (y : D.host.E)) = 0 := by
        refine (GlobalTheory.IntAdeleComplete.integral_separated_complete D).1 _
          (dvd_of_forall_prime (OhE D) _ fun q hq => ?_)
        by_cases hi : InertQ D q
        · rw [mul_comm]; exact VacMove.zeroAt_mul D hq ((hx q hq).1 hi) _
        · exact VacMove.zeroAt_mul D hq ((h3 q hq).2 hi) _
      rw [z1, z2, add_zero]
    have : proj _ he (Units.map (inc D).toMonoidHom (Units.mk0 _ hyE)) = x := by
      ext; rw [proj_val]
      change _ * inc D (y : D.host.E) + _ = _
      linear_combination -h0
    rwa [MonoidHom.comp_apply, this] at key
  · have : proj _ he (sgU D y) = sgU D (proj _ he y) := by
      ext
      change _ * sgA D y + _ = sgA D (_ * y + _)
      rw [map_add, map_mul, hse, map_sub, map_one, hse]
    rw [MonoidHom.comp_apply, map_mul, this, χ.norm]
  · have h4 := val_of_real_neg χ a ha hneg
    set t := Units.map (inc D).toMonoidHom a with ht
    have hst : sgA D (t : AE D) = t := by
      change sgA D (inc D a) = inc D a
      rw [GlobalTheory.NormSum.PtsMem.sgA_inc, ha]
    have : t = proj _ he t * (proj ε h1 t * sgU D (proj ε h1 t)) := by
      ext
      change (t : AE D) = (_ * t + _) * ((ε * t + _) * sgA D (ε * t + _))
      rw [map_add, map_mul, map_sub, map_one, hst]
      linear_combination ((t : AE D) - 1) ^ 2 * he -
        ((t : AE D) - 1) ^ 2 * (1 + (1 - (ε + sgA D ε)) * (t - 1)) * h2
    rw [this, map_mul, χ.norm, mul_one] at h4
    exact h4
  · obtain ⟨m, -, hm, s, hs, e⟩ := (h3 q hq).2 hi 1
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hm
    have hab' := congrArg (Int.cast : ℤ → AE D) hab
    push_cast at hab'
    rw [show (1 - (ε + sgA D ε)) * ((y⁻¹ : (AE D)ˣ) : AE D) =
      (a * s + b * (1 - (ε + sgA D ε))) * ((q : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D)) by
        linear_combination (-(1 - (ε + sgA D ε)) * ((y⁻¹ : (AE D)ˣ) : AE D)) * hab' +
          a * ((y⁻¹ : (AE D)ˣ) : AE D) * e]
    exact mul_mem (add_mem (mul_mem (intCast_mem _ _) hs) (mul_mem (intCast_mem _ _) heO)) hy'

end GlobalTheory.InertValue
