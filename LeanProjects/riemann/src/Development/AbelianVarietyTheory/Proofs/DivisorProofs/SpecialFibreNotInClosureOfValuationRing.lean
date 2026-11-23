import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosure
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel

set_option autoImplicit false

open scoped TensorProduct

namespace GlobalTheory.WeilIntegral

set_option autoImplicit false in
open scoped TensorProduct in

theorem _root_.GlobalTheory.WeilIntegral.isAlgebraic_of_etale (S B : Type) [CommRing S] [IsDomain S] [CommRing B] [Algebra S B]
    [Algebra.Etale S B] (f : B) : IsAlgebraic S f := by
  classical
  let K := FractionRing S
  haveI : Algebra.Etale K (TensorProduct S K B) := Algebra.Etale.baseChange S B K
  haveI : Module.Finite K (TensorProduct S K B) :=
    Algebra.FormallyUnramified.finite_of_free K (TensorProduct S K B)
  haveI hal : Algebra.IsAlgebraic K (TensorProduct S K B) := Algebra.IsAlgebraic.of_finite K _
  obtain ⟨p, hp0, hp⟩ := hal.isAlgebraic ((1 : K) ⊗ₜ[S] f)
  set q := IsLocalization.integerNormalization (nonZeroDivisors S) p
  have hq0 : q ≠ 0 := fun h0 =>
    hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).1 h0)
  have hq : Polynomial.aeval ((1 : K) ⊗ₜ[S] f) q = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero _ p hp
  have hmap : (1 : K) ⊗ₜ[S] Polynomial.aeval f q = 0 := by
    rw [← hq, ← Algebra.TensorProduct.includeRight_apply, ← Polynomial.aeval_algHom_apply]
    rfl
  haveI : IsLocalizedModule (nonZeroDivisors S) (TensorProduct.mk S K B 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors S) K _).2 (TensorProduct.isBaseChange S B K)
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors S) (TensorProduct.mk S K B 1)).1 hmap
  refine ⟨Polynomial.C (s : S) * q, ?_, ?_⟩
  · exact mul_ne_zero (Polynomial.C_ne_zero.2 (nonZeroDivisors.coe_ne_zero s)) hq0
  · rw [map_mul, Polynomial.aeval_C, ← Algebra.smul_def]
    exact hs

theorem exists_eq_C_mul_coeff_one {O σ : Type} [CommRing O] [IsDomain O] [ValuationRing O]
    (a : MvPolynomial σ O) (ha : a ≠ 0) :
    ∃ (c : O) (a' : MvPolynomial σ O) (d : σ →₀ ℕ), c ≠ 0 ∧ a = MvPolynomial.C c * a' ∧ a'.coeff d = 1 := by
  classical
  have key : ∀ s : Finset (σ →₀ ℕ), s.Nonempty → ∃ d ∈ s, ∀ e ∈ s, a.coeff d ∣ a.coeff e := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton x => exact ⟨x, by simp, by simp⟩
    | cons x s hx hs ih =>
      obtain ⟨d, hd, h⟩ := ih
      rcases ValuationRing.dvd_total (a.coeff d) (a.coeff x) with h1 | h1
      · refine ⟨d, by simp [hd], fun e he => ?_⟩
        rcases Finset.mem_cons.1 he with rfl | he
        · exact h1
        · exact h e he
      · refine ⟨x, by simp, fun e he => ?_⟩
        rcases Finset.mem_cons.1 he with rfl | he
        · exact dvd_rfl
        · exact h1.trans (h e he)
  obtain ⟨d, hd, h⟩ := key a.support (MvPolynomial.support_nonempty.2 ha)
  have hc : a.coeff d ≠ 0 := MvPolynomial.mem_support_iff.1 hd
  have hdvd : MvPolynomial.C (a.coeff d) ∣ a := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro e
    by_cases he : e ∈ a.support
    · exact h e he
    · rw [MvPolynomial.notMem_support_iff.1 he]
      exact dvd_zero _
  obtain ⟨a', ha'⟩ := hdvd
  refine ⟨a.coeff d, a', d, hc, ha', ?_⟩
  have := congrArg (MvPolynomial.coeff d) ha'
  rw [MvPolynomial.coeff_C_mul] at this
  exact mul_left_cancel₀ hc (by rw [← this, mul_one])

theorem exists_prime_dvd_of_etale {O B : Type} [CommRing O] [IsDomain O] [ValuationRing O] [CommRing B]
    [IsDomain B] [Algebra O B] {n : ℕ} (φ : MvPolynomial (Fin n) O →ₐ[O] B) (hφ : φ.Etale) (f : B) (hf : f ≠ 0)
    (q : Ideal B) [q.IsPrime] :
    ∃ (q' : Ideal B) (g : B) (c : O), q'.IsPrime ∧ (∀ x : O, algebraMap O B x ∈ q → algebraMap O B x ∈ q') ∧
      g ∉ q' ∧ c ≠ 0 ∧ f ∣ algebraMap O B c * g := by
  let S := MvPolynomial (Fin n) O
  letI : Algebra S B := φ.toRingHom.toAlgebra
  haveI : Algebra.Etale S B := hφ
  have hφ' : ∀ x : S, algebraMap S B x = φ x := fun _ => rfl
  obtain ⟨a, ha, hfa⟩ := (isAlgebraic_of_etale S B f).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)
  obtain ⟨c, a', d, hc, rfl, hd⟩ := exists_eq_C_mul_coeff_one a ha
  let P : Ideal O := q.comap (algebraMap O B)
  let P₀ : Ideal S := RingHom.ker (MvPolynomial.map (σ := Fin n) (Ideal.Quotient.mk P))
  haveI : P₀.IsPrime := RingHom.ker_isPrime _
  have hle : P₀ ≤ q.under S := by
    simp only [P₀]
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_le_iff_le_comap]
    intro x hx
    change φ (MvPolynomial.C x) ∈ q
    rw [MvPolynomial.algHom_C]
    exact hx
  haveI : Module.Flat S B := Algebra.Smooth.flat S B
  haveI : Algebra.HasGoingDown S B := Algebra.HasGoingDown.of_flat
  obtain ⟨q', -, hq', hlies⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := P₀) (q := q.under S) q hle
  have hmem : ∀ x : S, x ∈ P₀ ↔ φ x ∈ q' := fun x => Ideal.mem_of_liesOver q' P₀ x
  refine ⟨q', φ a', c, hq', fun x hx => ?_, fun h => ?_, hc, ?_⟩
  · rw [← MvPolynomial.algHom_C φ, ← hmem, RingHom.mem_ker, MvPolynomial.map_C,
      Ideal.Quotient.eq_zero_iff_mem.2 (show x ∈ P from hx), map_zero]
  · have h0 := congrArg (MvPolynomial.coeff d) (RingHom.mem_ker.1 ((hmem a').2 h))
    rw [MvPolynomial.coeff_map, hd, map_one, MvPolynomial.coeff_zero] at h0
    exact one_ne_zero h0
  · rw [hφ', map_mul, MvPolynomial.algHom_C] at hfa
    exact hfa

theorem specialFibreNotInClosure_of_valuationRing (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] : SpecialFibreNotInClosure p O := by
  rintro R _ _ _ _ f hf ⟨q, hq⟩
  obtain ⟨h, hh, hs⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth O q.asIdeal
  let B := Localization.Away h
  have hh0 : h ≠ 0 := fun e => hh (e ▸ q.asIdeal.zero_mem)
  have hpow : Submonoid.powers h ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hh0
  haveI : IsDomain B := IsLocalization.isDomain_localization hpow
  have hinj : Function.Injective (algebraMap R B) := IsLocalization.injective B hpow
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hs.out
  haveI : Algebra.IsStandardSmoothOfRelativeDimension P.dimension O B :=
    P.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨φ, hφ⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial P.dimension O B
  have hdisj : Disjoint (Submonoid.powers h : Set R) q.asIdeal := by
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  haveI : (q.asIdeal.map (algebraMap R B)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers h) _ _ q.isPrime hdisj
  obtain ⟨q', g, c, hq', hq'', hg, hc, b, hb⟩ := exists_prime_dvd_of_etale φ hφ (algebraMap R B f)
    (fun e => hf (hinj (by rw [e, map_zero]))) (q.asIdeal.map (algebraMap R B))
  obtain ⟨⟨g₀, s⟩, hgs⟩ := IsLocalization.surj (Submonoid.powers h) g
  obtain ⟨⟨b₀, t⟩, hbt⟩ := IsLocalization.surj (Submonoid.powers h) b
  simp only at hgs hbt
  have hs' : algebraMap R B s ∉ q' := fun e =>
    hq'.ne_top (Ideal.eq_top_of_isUnit_mem _ e (IsLocalization.map_units B s))
  have ht' : algebraMap R B t ∉ q' := fun e =>
    hq'.ne_top (Ideal.eq_top_of_isUnit_mem _ e (IsLocalization.map_units B t))
  refine ⟨⟨q'.comap (algebraMap R B), Ideal.comap_isPrime _ _⟩, g₀ * t, c, ?_, ?_, hc, b₀ * s, hinj ?_⟩
  · have := hq'' p (by simpa using Ideal.mem_map_of_mem (algebraMap R B) hq)
    simpa [Ideal.mem_comap] using this
  · change algebraMap R B (g₀ * t) ∉ q'
    rw [map_mul, ← hgs]
    exact hq'.mul_notMem (hq'.mul_notMem hg hs') ht'
  · simp only [map_mul]
    rw [← IsScalarTower.algebraMap_apply, ← hgs, ← hbt]
    linear_combination (algebraMap R B s * algebraMap R B t) * hb

theorem specialFibreNotInClosure (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) : SpecialFibreNotInClosure p O := by
  haveI : IsDomain O := hv.hom_inj.isDomain _
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  exact specialFibreNotInClosure_of_valuationRing p O

end GlobalTheory.WeilIntegral
