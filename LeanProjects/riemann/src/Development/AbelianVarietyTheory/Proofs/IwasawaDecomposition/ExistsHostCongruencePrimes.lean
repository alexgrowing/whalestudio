import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModulusBbDisjoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelevelCoprimeOfModOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormNonnegOfImagQuadratic
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsHost

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem

theorem exists_relevel_primes_one_mod (R : Ranks) (H₀ : Host R) (N : ℕ) : ∃ H : Host R, H.toHostAx = H₀.toHostAx ∧ H.splitBound = H₀.splitBound ∧ H.ccK = ⊤ ∧ H.TT = H₀.TT ∧ (∀ k, H.g k % (H.QS * H.q * H.d) = 1) ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧ (∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) ∧ (∀ k, N < H.g k) ∧ (∀ k, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g k : H.E) ∧ ((H.QS * H.q * H.d : ℕ) : 𝓞 H.E) ∣ π - 1) ∧ H.pde % (H.QS * H.q * H.d) = 1 ∧ H.pde' % (H.QS * H.q * H.d) = 1 := by
  suffices h : ∀ H₁ : Host R, H₁.ccK = ⊤ → ∃ H : Host R, H.toHostAx = H₁.toHostAx ∧ H.splitBound = H₁.splitBound ∧ H.ccK = ⊤ ∧ H.TT = H₁.TT ∧ (∀ k, H.g k % (H.QS * H.q * H.d) = 1) ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧ (∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) ∧ (∀ k, N < H.g k) ∧ (∀ k, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g k : H.E) ∧ ((H.QS * H.q * H.d : ℕ) : 𝓞 H.E) ∣ π - 1) ∧ H.pde % (H.QS * H.q * H.d) = 1 ∧ H.pde' % (H.QS * H.q * H.d) = 1 from
    h (UpperTheory.Host.withTop H₀) rfl
  intro H hK
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = H.QS * H.q * H.d := ⟨_, rfl⟩
  have hc1 : 1 < c := by
    have h1 : 0 < H.QS * H.q := Nat.mul_pos H.QS_pos H.q_prime.pos
    have h2 : 1 * H.d ≤ H.QS * H.q * H.d := Nat.mul_le_mul_right _ h1
    have h3 := H.d_prime.one_lt
    omega
  have hmod : ∀ x : ℕ, x ≡ 1 [MOD c] → x % c = 1 := fun x hx => by
    have : x % c = 1 % c := hx
    rwa [Nat.mod_eq_of_lt hc1] at this
  obtain ⟨π₀, g₀, hg₀, hN₀, hK₀, hn₀, hi₀, hm₀⟩ :=
    ImaginaryQuadraticNorm.exists_norm_prime R H c 1 N (by omega) (Nat.coprime_one_left c)
  obtain ⟨M, N', hM0, hcM, hdis⟩ := exists_modulus_bb_disjoint R.r g₀ c hg₀ (by omega)
  have hcop : Nat.Coprime (1 + M) (M ^ 2) := Nat.Coprime.pow_right 2 (by simp)
  obtain ⟨π₁, g₁, hg₁, hN₁, hK₁, hn₁, hi₁, hm₁⟩ :=
    ImaginaryQuadraticNorm.exists_norm_prime R H (M ^ 2) (1 + M) (N' + g₀) (pow_ne_zero 2 hM0) hcop
  have hD := hdis g₁ hg₁ (by omega) hm₁
  have hg₀c : g₀ % c = 1 := hmod _ (by simpa using hm₀)
  have hg₁c : g₁ % c = 1 := by
    apply hmod
    refine (hm₁.of_dvd (hcM.trans (dvd_pow_self M two_ne_zero))).trans ?_
    have h1 : 1 + M ≡ 1 + 0 [MOD c] := Nat.ModEq.add_left 1 ((Nat.modEq_zero_iff_dvd).2 hcM)
    simpa using h1.pow 2
  have hd₀ : (c : 𝓞 H.E) ∣ π₀ - 1 := by
    simpa [Ideal.mem_span_singleton] using hi₀
  have hd₁ : (c : 𝓞 H.E) ∣ π₁ - 1 := by
    have h1 : (c : 𝓞 H.E) ∣ (M : 𝓞 H.E) := Nat.cast_dvd_cast hcM
    have h2 : ((M ^ 2 : ℕ) : 𝓞 H.E) ∣ π₁ - ((1 + M : ℕ) : 𝓞 H.E) := Ideal.mem_span_singleton.1 hi₁
    have h3 : (c : 𝓞 H.E) ∣ π₁ - ((1 + M : ℕ) : 𝓞 H.E) :=
      (Nat.cast_dvd_cast (hcM.trans (dvd_pow_self M two_ne_zero))).trans h2
    have h4 : π₁ - 1 = (π₁ - ((1 + M : ℕ) : 𝓞 H.E)) + M := by push_cast; ring
    rw [h4]
    exact dvd_add h3 h1
  obtain ⟨p, hpN, hp, hpm⟩ := Nat.forall_exists_prime_gt_and_modEq g₁ (q := 15 * c) (a := 1) (by omega)
    (Nat.coprime_one_left _)
  obtain ⟨p', hpN', hp', hpm'⟩ := Nat.forall_exists_prime_gt_and_modEq p (q := 15 * c) (a := 1) (by omega)
    (Nat.coprime_one_left _)
  have hpc : p % c = 1 := hmod _ (hpm.of_mul_left 15)
  have hpc' : p' % c = 1 := hmod _ (hpm'.of_mul_left 15)
  have hp15 : p % 15 = 1 := hpm.of_mul_right c
  have hp15' : p' % 15 = 1 := hpm'.of_mul_right c
  subst hc
  have hlv : ∀ x ∈ ({g₀, g₁, p, p'} : Finset ℕ), x.Prime ∧ x % (H.QS * H.q * H.d) = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h | h | h <;> subst h
    · exact ⟨hg₀, hg₀c⟩
    · exact ⟨hg₁, hg₁c⟩
    · exact ⟨hp, hpc⟩
    · exact ⟨hp', hpc'⟩
  have hS : ∀ x ∈ ({g₀, g₁, p, p'} : Finset ℕ), Nat.Coprime x H.QS := by
    intro x hx
    have h1 : Nat.Coprime x (H.QS * H.q * H.d) := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, (hlv x hx).2, Nat.gcd_one_left]
    exact (h1.coprime_mul_right_right).coprime_mul_right_right
  refine ⟨{ H with
    levelPrimes := {g₀, g₁, p, p'}
    g := ![g₀, g₁]
    g_prime := by intro i; fin_cases i <;> simpa
    g_ne := by simp; omega
    g_level := by intro i; fin_cases i <;> simp
    pde := p
    pde' := p'
    pde_prime := hp
    pde'_prime := hp'
    pde_ne := by omega
    pde_level := by constructor <;> simp
    pde_mod := ⟨hp15, hp15'⟩
    pde_ne_g := by intro i; fin_cases i <;> simp <;> omega
    ccK_coprime := fun x _ => by rw [hK, Ideal.absNorm_top]; exact Nat.coprime_one_left x
    level_coprimeS := hS }, rfl, rfl, hK, rfl, ?_, hD, hlv, ?_, ?_, hpc, hpc'⟩
  · intro k
    fin_cases k
    · exact hg₀c
    · exact hg₁c
  · intro k
    fin_cases k
    · exact hN₀
    · show N < g₁
      omega
  · intro k
    fin_cases k
    · exact ⟨π₀, hK₀, hn₀, hd₀⟩
    · exact ⟨π₁, hK₁, hn₁, hd₁⟩

theorem exists_host_level_primes_one_mod : ∀ (R : Ranks), Function.Injective R.h → R.o ^ 64 ≤ 2 ^ R.e → 2 ≤ R.e → ∀ (B N : ℕ) (TT : Finset (R.A)), ∃ H : Host R, H.splitBound = B ∧ N < H.q ∧ N < H.d ∧ H.ccK = ⊤ ∧ H.TT = TT ∧ (∀ k, H.g k % (H.QS * H.q * H.d) = 1) ∧ Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧ (∀ p ∈ H.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1) ∧ (∀ k, N < H.g k) ∧ (∀ k, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g k : H.E) ∧ ((H.QS * H.q * H.d : ℕ) : 𝓞 H.E) ∣ π - 1) ∧ H.pde % (H.QS * H.q * H.d) = 1 ∧ H.pde' % (H.QS * H.q * H.d) = 1 := by
  intro R hinj ho he B N TT
  obtain ⟨H₀, hB, hq, hd, -, hT, -⟩ := UpperTheory.Host.exists_host_of_injective R hinj ho he B N TT
  obtain ⟨H, h1, h2, h3, h4, h5⟩ := exists_relevel_primes_one_mod R H₀ N
  refine ⟨H, h2.trans hB, ?_, ?_, h3, h4.trans hT, h5⟩
  · rw [h1]; exact hq
  · rw [h1]; exact hd

end GlobalTheory.Mem
