import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionQuotientKerEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSMulRegularAdicCompletionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectoidTowerSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltUntiltDividesPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerFontaineThetaEqSpanOfDistinguishedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffXiEqRootSubOnePowStatement

set_option autoImplicit false

noncomputable section

open Ideal WittVector

namespace GlobalTheory.PerfdCompletion

theorem t_complete (p : ℕ) (A : Type) [CommRing A] :
    IsAdicComplete (span {(p : AdicCompletion (span {(p : A)}) A)})
      (AdicCompletion (span {(p : A)}) A) := by
  have h := AdicCompletion.isAdicComplete (R := A) (I := span {(p : A)}) (M := A)
    (Submodule.fg_span_singleton _)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (span {(p : A)}) A)] at h
  simpa [Ideal.map_span] using h

section Closed

theorem exists_pow_eq {A : Type} (K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [IsAlgClosed K]
    [Algebra A K] [IsFractionRing A K] (x : A) {n : ℕ} (hn : 0 < n) : ∃ y : A, y ^ n = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A K x) hn
  have hi : IsIntegral A z := ⟨Polynomial.X ^ n - Polynomial.C x,
    Polynomial.monic_X_pow_sub_C x hn.ne', by simp [hz]⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hi
  exact ⟨y, IsFractionRing.injective A K (by rw [map_pow, hy, hz])⟩

theorem dvd_of_dvd_pow {A : Type} (K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] {a π x : A} {m : ℕ} (hm : 0 < m) (hπ : π ^ m = a) (h0 : π ≠ 0)
    (h : a ∣ x ^ m) : π ∣ x := by
  obtain ⟨b, hb⟩ := h
  have hπK : algebraMap A K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 h0
  set z := algebraMap A K x / algebraMap A K π
  have hz : z ^ m = algebraMap A K b := by
    have ha : algebraMap A K a ≠ 0 := by rw [← hπ, map_pow]; exact pow_ne_zero _ hπK
    rw [div_pow, div_eq_iff (pow_ne_zero _ hπK), ← map_pow, ← map_pow, hπ, hb, map_mul, mul_comm]
  have hi : IsIntegral A z := ⟨Polynomial.X ^ m - Polynomial.C b,
    Polynomial.monic_X_pow_sub_C b hm.ne', by simp [hz]⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hi
  refine ⟨y, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hy, mul_div_cancel₀ _ hπK]

end Closed

theorem exists_cycPerfd : ∀ (p : ℕ) [Fact p.Prime] (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [IsAlgClosed K] [CharZero K] [Algebra A K] [IsFractionRing A K], ¬ IsUnit (p : A) → ∀ ζ : ℕ → A, (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → ∃ (S : GlobalTheory.Published.CycPerfd p) (e : AdicCompletion (Ideal.span {(p : A)}) A ≃+* S.R), ∀ n, GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta S.ε n = e (algebraMap A _ (ζ n)) := by
  intro p _ A K _ _ _ _ _ _ _ _ hpA ζ hζ hζs
  have hp0 : (p : A) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap A K) h
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h'
    exact (Fact.out : p.Prime).ne_zero h'
  have hreg : IsSMulRegular A (p : A) := fun x y h => mul_left_cancel₀ hp0 h
  obtain ⟨hsurj, hker⟩ := GlobalTheory.T.adic_completion_quotient_ker_eq p A hreg
  set R := AdicCompletion (span {(p : A)}) A
  set φ := (Ideal.Quotient.mk (span {(p : R)})).comp (algebraMap A R) with hφ
  have hnu : ¬IsUnit (p : R) := by
    intro h
    have h1 : IsUnit (Ideal.Quotient.mk (span {(p : R)}) (p : R)) := h.map _
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (mem_span_singleton_self _), isUnit_zero_iff] at h1
    have h2 : (1 : A) ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_one]; exact h1.symm
    rw [hker, mem_span_singleton] at h2
    exact hpA (isUnit_of_dvd_one h2)
  haveI : Fact ¬IsUnit (p : R) := ⟨hnu⟩
  haveI : IsAdicComplete (span {(p : R)}) R := t_complete p A
  set z : ℕ → R := fun n => algebraMap A R (ζ n) with hzdef
  have hz : ∀ n, z (n + 1) ^ p = z n := fun n => by simp only [hzdef, ← map_pow, hζs]
  set ε : PreTilt R p := ReciprocityTheory.PGsh.ofRoots z hz with hεdef
  have hroot : (GlobalTheory.Sandwich.root : PreTilt R p → PreTilt R p) =
      ⇑(_root_.frobeniusEquiv (PreTilt R p) p).symm := rfl
  have hzeta : ∀ n, GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta ε n = z n := by
    intro n
    have := ReciprocityTheory.PGsh.untilt_eq_of_coeff (GlobalTheory.Sandwich.root^[n] ε) (fun k => z (n + k))
      (fun k => hz (n + k)) (fun k => by
        rw [hroot, ← PreTilt.coeff_def, PreTilt.coeff_iterate_frobeniusEquiv_symm, PreTilt.coeff_def,
          ReciprocityTheory.PGsh.coeff_ofRoots, add_comm])
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta] using this
  have hzeta0 : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta ε 0 = 1 := by
    rw [hzeta 0, hzdef]
    have h1 : ζ 0 = 1 := by simpa using (hζ 0)
    simp [h1]
  have hfrob : Function.Surjective (_root_.frobenius (ModP R p) p) := by
    intro c
    obtain ⟨x, rfl⟩ := hsurj c
    obtain ⟨y, hy⟩ := exists_pow_eq K x (Fact.out : p.Prime).pos
    exact ⟨φ y, by rw [frobenius_def, ← map_pow, hy]⟩

  have hroots : ∀ x : A, ∃ y : A, y ^ p = x := fun x => exists_pow_eq K x (Fact.out : p.Prime).pos
  choose r hr using hroots
  let π : ℕ → A := fun n => Nat.rec (p : A) (fun _ y => r y) n
  have hπs : ∀ n, π (n + 1) ^ p = π n := fun n => hr _
  have hπpow : ∀ n, π n ^ (p ^ n) = p := by
    intro n
    induction n with
    | zero => simp [π]
    | succ n ih => rw [pow_succ', pow_mul, hπs, ih]
  have hπ0 : ∀ n, π n ≠ 0 := fun n h => hp0 (by rw [← hπpow n, h, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)])
  have hdiv : ∀ (n : ℕ) (x : A), (p : A) ∣ x ^ (p ^ n) → π n ∣ x := fun n x h =>
    dvd_of_dvd_pow K (pow_pos (Fact.out : p.Prime).pos n) (hπpow n) (hπ0 n) h
  obtain ⟨pflat, hpf, hpdiv⟩ := GlobalTheory.T.perfectoid_tower_surjective p A R (algebraMap A R) hp0 hsurj hker π rfl hπs hdiv
  have hregR := GlobalTheory.T.isSMulRegular_adicCompletion p A hreg

  set f : PreTilt R p := (_root_.frobeniusEquiv (PreTilt R p) p).symm (GlobalTheory.Sandwich.root ε) with hf
  have hfp : f ^ p = GlobalTheory.Sandwich.root ε := frobeniusEquiv_symm_pow_p (PreTilt R p) p _
  have hfu : PreTilt.untilt f = z 2 := by
    rw [← hzeta 2]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta, hf, hroot]
  have hass : Associated ((PreTilt.untilt f - 1) ^ (p * (p - 1))) (p : R) := by
    have h := GlobalTheory.associated_primitiveRoot_sub_one_pow_totient_prime_pow (k := 1)
      (Fact.out : p.Prime) (hζ 2)
    rw [Nat.totient_prime_pow_succ (Fact.out : p.Prime), pow_one] at h
    have h2 := h.map (algebraMap A R)
    rw [map_pow, map_sub, map_one, map_natCast] at h2
    rw [hfu]; exact h2
  have hdivξ : ∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → WittVector.constantCoeff (GlobalTheory.Sandwich.xi ε) ∣ c := by
    intro c hc
    rw [GlobalTheory.T.constantCoeff_xi_eq_root_sub_one_pow, ← hfp]
    exact GlobalTheory.T.tilt_untilt_divides_pow p R hregR pflat f hpf hpdiv hass c hc
  have hθξ : fontaineTheta R p (GlobalTheory.Sandwich.xi ε) = 0 := by
    have h1 : PreTilt.untilt (GlobalTheory.Sandwich.root ε) = z 1 := by
      rw [← hzeta 1]; rfl
    rw [GlobalTheory.Sandwich.xi, map_sum]
    simp only [map_pow, fontaineTheta_teichmuller, h1]
    have h2 : ∑ i ∈ Finset.range p, z 1 ^ i = algebraMap A R (∑ i ∈ Finset.range p, ζ 1 ^ i) := by
      simp [hzdef]
    have h3 : ∑ i ∈ Finset.range p, ζ 1 ^ i = 0 := by
      have := (hζ 1).geom_sum_eq_zero (by simpa using (Fact.out : p.Prime).one_lt)
      simpa using this
    rw [h2, h3, map_zero]
  refine ⟨⟨R, hregR, ε, hzeta0, surjective_fontaineTheta hfrob,
    GlobalTheory.T.ker_fontaineTheta_eq_span_of_distinguished p R hregR _ hθξ hdivξ⟩, RingEquiv.refl _, fun n => ?_⟩
  exact hzeta n

end GlobalTheory.PerfdCompletion
