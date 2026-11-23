import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.CompAdd

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

namespace Pre

open GlobalTheory.PDA.Model TensorProduct

theorem conv_mul {B : Type} [CommRing B] (c c' : ℕ → B) (h0 : c 0 = 1)
    (hm : ∀ m n, c m * c n = ((m + n).choose m : B) * c (m + n)) (h0' : c' 0 = 1)
    (hm' : ∀ m n, c' m * c' n = ((m + n).choose m : B) * c' (m + n)) (m n : ℕ) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, c p.1 * c' p.2) *
      (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, c p.1 * c' p.2) =
      ((m + n).choose m : B) * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (m + n), c p.1 * c' p.2 := by
  obtain ⟨iL, hiL⟩ : ∃ f : ↥L →ₐ[ℤ] ↥L ⊗[ℤ] ↥L, f = Algebra.TensorProduct.includeLeft (S := ℤ) :=
    ⟨_, rfl⟩
  obtain ⟨iR, hiR⟩ : ∃ f : ↥L →ₐ[ℤ] ↥L ⊗[ℤ] ↥L, f = Algebra.TensorProduct.includeRight :=
    ⟨_, rfl⟩
  have hu0 : iL (bL 0) = 1 := by rw [bL_zero, map_one]
  have hv0 : iR (bL 0) = 1 := by rw [bL_zero, map_one]
  have hum : ∀ a b : ℕ, iL (bL a) * iL (bL b) =
      ((a + b).choose a : ↥L ⊗[ℤ] ↥L) * iL (bL (a + b)) := by
    intro a b
    rw [← map_mul, bL_mul, map_mul, map_natCast]
  have hvm : ∀ a b : ℕ, iR (bL a) * iR (bL b) =
      ((a + b).choose a : ↥L ⊗[ℤ] ↥L) * iR (bL (a + b)) := by
    intro a b
    rw [← map_mul, bL_mul, map_mul, map_natCast]
  have fu := fact_mul _ hu0 hum
  have fv := fact_mul _ hv0 hvm
  have fs := fact_sum _ _ _ _ fu fv
  have key : ∀ a b : ℕ,
      (∑ p ∈ Finset.HasAntidiagonal.antidiagonal a, iL (bL p.1) * iR (bL p.2)) *
        (∑ p ∈ Finset.HasAntidiagonal.antidiagonal b, iL (bL p.1) * iR (bL p.2)) =
        ((a + b).choose a : ↥L ⊗[ℤ] ↥L) *
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (a + b), iL (bL p.1) * iR (bL p.2) := by
    intro a b
    have hC : (a + b).choose a * a.factorial * b.factorial = (a + b).factorial := by
      have := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
      simpa using this
    apply cancel (n := a.factorial * b.factorial) (by positivity)
    calc _ = ((a.factorial : ↥L ⊗[ℤ] ↥L) *
              ∑ p ∈ Finset.HasAntidiagonal.antidiagonal a, iL (bL p.1) * iR (bL p.2)) *
            ((b.factorial : ↥L ⊗[ℤ] ↥L) *
              ∑ p ∈ Finset.HasAntidiagonal.antidiagonal b, iL (bL p.1) * iR (bL p.2)) := by
            push_cast
            ring
      _ = (((a + b).choose a * a.factorial * b.factorial : ℕ) : ↥L ⊗[ℤ] ↥L) *
            ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (a + b), iL (bL p.1) * iR (bL p.2) := by
            rw [fs a, fs b, ← pow_add, hC, fs (a + b)]
      _ = _ := by
            push_cast
            ring
  have := congrArg (Algebra.TensorProduct.productMap (liftL c h0 hm) (liftL c' h0' hm')) (key m n)
  subst hiL hiR
  simpa [map_sum, map_mul, map_natCast, liftL_bL] using this

end Pre

theorem dp_split' : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (P : Type) [CommRing P] [Algebra B P] (ε : P →ₐ[B] B) (𝔞 : Ideal P) (η : DividedPowers 𝔞), (∀ p, p ∈ 𝔞 ↔ ε p = 0) → ∃ θ : DividedPowers (J.map (algebraMap B P) ⊔ 𝔞), IsDPMorphism δ θ (algebraMap B P) ∧ ∀ n, ∀ p ∈ 𝔞, θ.dpow n p = η.dpow n p := by
  intro B _ J δ P _ _ ε 𝔞 η hε
  classical
  have hεf : ∀ b : B, ε (algebraMap B P b) = b := fun b => ε.commutes b
  have hεa : ∀ a ∈ 𝔞, ε a = 0 := fun a ha => (hε a).1 ha
  have hK : ∀ p : P, p ∈ J.map (algebraMap B P) ⊔ 𝔞 ↔ ε p ∈ J := by
    intro p
    constructor
    · intro hp
      have hle : J.map (algebraMap B P) ⊔ 𝔞 ≤ J.comap ε := by
        refine sup_le ?_ ?_
        · rw [Ideal.map_le_iff_le_comap]
          intro b hb
          rw [Ideal.mem_comap, Ideal.mem_comap]
          simpa [hεf b] using hb
        · intro a ha
          rw [Ideal.mem_comap, hεa a ha]
          exact J.zero_mem
      have := hle hp
      rwa [Ideal.mem_comap] at this
    · intro hp
      rw [show p = algebraMap B P (ε p) + (p - algebraMap B P (ε p)) by ring]
      refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp)) (Ideal.mem_sup_right ?_)
      rw [hε, map_sub, hεf, sub_self]
  have hdec : ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞, ∃ b ∈ J, ∃ a ∈ 𝔞, p = algebraMap B P b + a := by
    intro p hp
    refine ⟨ε p, (hK p).1 hp, p - algebraMap B P (ε p), ?_, by ring⟩
    rw [hε, map_sub, hεf, sub_self]
  have hfK : ∀ b ∈ J, algebraMap B P b ∈ J.map (algebraMap B P) ⊔ 𝔞 :=
    fun b hb => Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hb)
  have haK : ∀ a ∈ 𝔞, a ∈ J.map (algebraMap B P) ⊔ 𝔞 := fun a ha => Ideal.mem_sup_right ha
  obtain ⟨γ, hγ⟩ : ∃ γ : ℕ → P → P, ∀ n p, γ n p = if ε p ∈ J then
      ∑ k ∈ Finset.HasAntidiagonal.antidiagonal n,
        algebraMap B P (δ.dpow k.1 (ε p)) * η.dpow k.2 (p - algebraMap B P (ε p)) else 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hS : ∀ n, ∀ b ∈ J, ∀ a ∈ 𝔞, γ n (algebraMap B P b + a) =
      ∑ k ∈ Finset.HasAntidiagonal.antidiagonal n, algebraMap B P (δ.dpow k.1 b) * η.dpow k.2 a := by
    intro n b hb a ha
    have h1 : ε (algebraMap B P b + a) = b := by rw [map_add, hεf, hεa a ha, add_zero]
    rw [hγ, h1, if_pos hb, add_sub_cancel_left]
  have hB : ∀ n, ∀ b ∈ J, γ n (algebraMap B P b) = algebraMap B P (δ.dpow n b) := by
    intro n b hb
    have h := hS n b hb 0 𝔞.zero_mem
    rw [add_zero] at h
    rw [h, Finset.sum_eq_single (n, 0)]
    · rw [η.dpow_zero 𝔞.zero_mem, mul_one]
    · intro k hk hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
      have h2 : k.2 ≠ 0 := fun h2 => hne (Prod.ext (by omega) h2)
      rw [η.dpow_eval_zero h2, mul_zero]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h
  have hA : ∀ n, ∀ a ∈ 𝔞, γ n a = η.dpow n a := by
    intro n a ha
    have h := hS n 0 J.zero_mem a ha
    rw [map_zero, zero_add] at h
    rw [h, Finset.sum_eq_single (0, n)]
    · rw [δ.dpow_zero J.zero_mem, map_one, one_mul]
    · intro k hk hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
      have h1 : k.1 ≠ 0 := fun h1 => hne (Prod.ext h1 (by omega))
      rw [δ.dpow_eval_zero h1, map_zero, zero_mul]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h
  have hc0 : ∀ b ∈ J, algebraMap B P (δ.dpow 0 b) = 1 := fun b hb => by
    rw [δ.dpow_zero hb, map_one]
  have hcm : ∀ b ∈ J, ∀ m n, algebraMap B P (δ.dpow m b) * algebraMap B P (δ.dpow n b) =
      ((m + n).choose m : P) * algebraMap B P (δ.dpow (m + n) b) := fun b hb m n => by
    rw [← map_mul, δ.mul_dpow hb, map_mul, map_natCast]
  have hmd : ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞, ∀ m n,
      γ m p * γ n p = ((m + n).choose m : P) * γ (m + n) p := by
    intro p hp m n
    obtain ⟨b, hb, a, ha, rfl⟩ := hdec p hp
    rw [hS m b hb a ha, hS n b hb a ha, hS (m + n) b hb a ha]
    exact Pre.conv_mul (fun i => algebraMap B P (δ.dpow i b)) (fun j => η.dpow j a)
      (hc0 b hb) (hcm b hb) (η.dpow_zero ha) (fun m n => η.mul_dpow ha) m n
  have hzero : ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞, γ 0 p = 1 := by
    intro p hp
    obtain ⟨b, hb, a, ha, rfl⟩ := hdec p hp
    rw [hS 0 b hb a ha]
    simp [δ.dpow_zero hb, η.dpow_zero ha]
  have hone : ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞, γ 1 p = p := by
    intro p hp
    obtain ⟨b, hb, a, ha, rfl⟩ := hdec p hp
    rw [hS 1 b hb a ha, Finset.Nat.sum_antidiagonal_succ]
    simp [δ.dpow_zero hb, η.dpow_zero ha, δ.dpow_one hb, η.dpow_one ha, add_comm]
  have hmem : ∀ n, n ≠ 0 → ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞, γ n p ∈ J.map (algebraMap B P) ⊔ 𝔞 := by
    intro n hn p hp
    obtain ⟨b, hb, a, ha, rfl⟩ := hdec p hp
    rw [hS n b hb a ha]
    refine Ideal.sum_mem _ fun k hk => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
    by_cases h1 : k.1 = 0
    · exact Ideal.mul_mem_left _ _ (haK _ (η.dpow_mem (by omega) ha))
    · exact Ideal.mul_mem_right _ _ (hfK _ (δ.dpow_mem h1 hb))
  have hadd : ∀ n, ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞, ∀ q ∈ J.map (algebraMap B P) ⊔ 𝔞,
      γ n (p + q) = ∑ k ∈ Finset.HasAntidiagonal.antidiagonal n, γ k.1 p * γ k.2 q := by
    intro n p hp q hq
    obtain ⟨b, hb, a, ha, rfl⟩ := hdec p hp
    obtain ⟨b', hb', a', ha', rfl⟩ := hdec q hq
    have e : algebraMap B P b + a + (algebraMap B P b' + a') =
        algebraMap B P (b + b') + (a + a') := by
      rw [map_add]
      ring
    have ser : ∀ (c : B) (d : P) (k : ℕ),
        ∑ i ∈ Finset.HasAntidiagonal.antidiagonal k, algebraMap B P (δ.dpow i.1 c) * η.dpow i.2 d =
          PowerSeries.coeff k ((PowerSeries.mk fun i => algebraMap B P (δ.dpow i c)) *
            PowerSeries.mk fun j => η.dpow j d) := by
      intro c d k
      rw [PowerSeries.coeff_mul]
      simp only [PowerSeries.coeff_mk]
    have hX : (PowerSeries.mk fun i => algebraMap B P (δ.dpow i (b + b'))) =
        (PowerSeries.mk fun i => algebraMap B P (δ.dpow i b)) *
          PowerSeries.mk fun i => algebraMap B P (δ.dpow i b') := by
      ext k
      rw [PowerSeries.coeff_mul]
      simp only [PowerSeries.coeff_mk]
      rw [δ.dpow_add hb hb', map_sum]
      simp only [map_mul]
    have hY : (PowerSeries.mk fun j => η.dpow j (a + a')) =
        (PowerSeries.mk fun j => η.dpow j a) * PowerSeries.mk fun j => η.dpow j a' :=
      DividedPowers.exp_add' _ (fun _ => η.dpow_add ha ha')
    rw [e, hS n _ (J.add_mem hb hb') _ (𝔞.add_mem ha ha'), ser, hX, hY, mul_mul_mul_comm,
      PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hS k.1 b hb a ha, hS k.2 b' hb' a' ha', ser, ser]
  have hfact : ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞, ∀ j : ℕ, p ^ j = (j.factorial : P) * γ j p := by
    intro p hp j
    rw [Pre.fact_mul (fun k => γ k p) (hzero p hp) (hmd p hp) j, hone p hp]
  have hmul : ∀ (n : ℕ) (c x : P), x ∈ J.map (algebraMap B P) ⊔ 𝔞 → γ n (c * x) = c ^ n * γ n x := by
    intro n c x hx
    have ha' : c - algebraMap B P (ε c) ∈ 𝔞 := by rw [hε, map_sub, hεf, sub_self]
    have hfs : ∀ i, γ i (algebraMap B P (ε c) * x) = algebraMap B P (ε c) ^ i * γ i x := by
      intro i
      obtain ⟨b, hb, a, ha, hxe⟩ := hdec x hx
      rw [hxe, show algebraMap B P (ε c) * (algebraMap B P b + a) =
          algebraMap B P (ε c * b) + algebraMap B P (ε c) * a by rw [map_mul]; ring,
        hS i _ (J.mul_mem_left _ hb) _ (𝔞.mul_mem_left _ ha), hS i b hb a ha, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
      rw [δ.dpow_mul hb, η.dpow_mul ha, map_mul, map_pow, ← hk, pow_add]
      ring
    have hax : ∀ j, γ j ((c - algebraMap B P (ε c)) * x) =
        η.dpow j (c - algebraMap B P (ε c)) * x ^ j := by
      intro j
      rw [hA j _ (𝔞.mul_mem_right x ha'), η.dpow_mul_right ha']
    have hcx : c * x = algebraMap B P (ε c) * x + (c - algebraMap B P (ε c)) * x := by ring
    rw [hcx, hadd n _ (Ideal.mul_mem_left _ _ hx) _ (haK _ (𝔞.mul_mem_right x ha'))]
    conv_rhs => rw [show c = algebraMap B P (ε c) + (c - algebraMap B P (ε c)) by ring]
    rw [(Commute.all _ _).add_pow', Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
    have hm := hmd x hx k.1 k.2
    rw [hk] at hm
    rw [hfs, hax, hfact x hx k.2, ← η.factorial_mul_dpow_eq_pow ha', nsmul_eq_mul]
    calc algebraMap B P (ε c) ^ k.1 * γ k.1 x *
          (η.dpow k.2 (c - algebraMap B P (ε c)) * ((k.2.factorial : P) * γ k.2 x))
        = algebraMap B P (ε c) ^ k.1 * η.dpow k.2 (c - algebraMap B P (ε c)) *
            (k.2.factorial : P) * (γ k.1 x * γ k.2 x) := by ring
      _ = _ := by
        rw [hm]
        ring
  have hpre : IsPreDP (J.map (algebraMap B P) ⊔ 𝔞) γ :=
    ⟨fun n x hx => by rw [hγ, if_neg (fun h => hx ((hK x).2 h))], hzero, hone, hmem, hadd, hmul,
      fun m n x hx => hmd x hx m n⟩
  have hcomp : ∀ m n, n ≠ 0 → ∀ p ∈ J.map (algebraMap B P) ⊔ 𝔞,
      γ m (γ n p) = (m.uniformBell n : P) * γ (m * n) p := by
    intro m n hn p hp
    obtain ⟨b, hb, a, ha, rfl⟩ := hdec p hp
    refine Pre.comp_add hpre (hfK b hb) (haK a ha) ?_ ?_ m n hn
    · intro m n hn
      rw [hB n b hb, hB m _ (δ.dpow_mem hn hb), hB (m * n) b hb, δ.dpow_comp hn hb, map_mul,
        map_natCast]
    · intro m n hn
      rw [hA n a ha, hA m _ (η.dpow_mem hn ha), hA (m * n) a ha, η.dpow_comp hn ha]
  obtain ⟨θ, hθ⟩ : ∃ θ : DividedPowers (J.map (algebraMap B P) ⊔ 𝔞), θ.dpow = γ :=
    ⟨{ dpow := γ
       dpow_null := fun {n x} hx => hpre.null n x hx
       dpow_zero := fun {x} hx => hzero x hx
       dpow_one := fun {x} hx => hone x hx
       dpow_mem := fun {n x} hn hx => hmem n hn x hx
       dpow_add := fun {n x y} hx hy => hadd n x hx y hy
       dpow_mul := fun {n a x} hx => hmul n a x hx
       mul_dpow := fun {m n x} hx => hmd x hx m n
       dpow_comp := fun {m n x} hn hx => hcomp m n hn x hx }, rfl⟩
  refine ⟨θ, ⟨le_sup_left, fun {n} b hb => ?_⟩, fun n p hp => ?_⟩
  · rw [hθ, hB n b hb]
  · rw [hθ, hA n p hp]

end FubiniStudyChowHeightFormula₂.Adr
