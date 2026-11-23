import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsMulInvolutionAddOneMemPow

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

namespace GlobalTheory.NegOneNorm

theorem exists_dvd_mul_involution_add_one {R : Type} [CommRing R] [IsDedekindDomain R] (s : R →+* R)
    (hs : ∀ x, s (s x) = x) (n : R) (hn : n ≠ 0) (hsn : s n = n)
    (hfin : ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P))
    (hne : ∀ P : Ideal R, P.IsMaximal → ∃ x, s x - x ∉ P)
    (h2 : ∀ P : Ideal R, P.IsMaximal → (∀ x ∈ P, s x ∈ P) → (2 : R) ∉ P) :
    ∃ l : R, n ∣ l * s l + 1 := by
  have hn' : Ideal.span {n} ≠ (⊥ : Ideal R) := by simpa using hn
  let S : Finset (Ideal R) := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {n})).toFinset
  have hS : ∀ P : Ideal R, P ∈ S ↔ P.IsPrime ∧ n ∈ P := fun P => by
    simp only [S, Multiset.mem_toFinset]
    rw [Ideal.mem_normalizedFactors_iff hn', Ideal.span_singleton_le_iff_mem]
  have hbot : ∀ P ∈ S, P ≠ ⊥ := fun P hP => by
    rintro rfl
    exact hn (by simpa using ((hS _).1 hP).2)
  have hpr : ∀ P ∈ S, Prime P := fun P hP => Ideal.prime_of_isPrime (hbot P hP) ((hS P).1 hP).1
  have hrad : ∏ P ∈ S, P ≤ (Ideal.span {n}).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro P ⟨h1, h3⟩
    exact Ideal.prod_le_inf.trans
      (Finset.inf_le (f := fun P => P) ((hS P).2 ⟨h3, (Ideal.span_singleton_le_iff_mem _).1 h1⟩))
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hcc : ∀ P : Ideal R, (P.comap s).comap s = P := fun P => by
    ext x; simp [Ideal.mem_comap, hs]
  have hz : ∀ P : Ideal R, ∃ z : R, P ∈ S → P.comap s = P → z * s z + 1 ∈ P ^ N := fun P => by
    by_cases h : P ∈ S ∧ P.comap s = P
    · obtain ⟨hP, hfix⟩ := h
      haveI hM : P.IsMaximal := ((hS P).1 hP).1.isMaximal (hbot P hP)
      haveI := hfin P hM
      have hsP : ∀ x ∈ P, s x ∈ P := fun x hx => by rwa [← hfix] at hx
      have : ∀ k : ℕ, ∃ z : R, k = 0 ∨ z * s z + 1 ∈ P ^ k := fun k => by
        induction k with
        | zero => exact ⟨0, Or.inl rfl⟩
        | succ k ih =>
          obtain ⟨z0, hz0⟩ := ih
          obtain ⟨z, hz, -⟩ := GlobalTheory.NormResidue.exists_mul_involution_add_one_mem_pow R s hs P hsP
            (hne P hM) (h2 P hM hsP) k z0 hz0
          exact ⟨z, Or.inr hz⟩
      obtain ⟨z, hz⟩ := this (N + 1)
      exact ⟨z, fun _ _ => Ideal.pow_le_pow_right (Nat.le_succ N) (hz.resolve_left (Nat.succ_ne_zero N))⟩
    · exact ⟨0, fun h1 h3 => (h ⟨h1, h3⟩).elim⟩
  choose z hz using hz
  let a : Ideal R → R := fun P =>
    if P.comap s = P then z P else if WellOrderingRel P (P.comap s) then 1 else -1
  have ha : ∀ P ∈ S, a P * s (a (P.comap s)) + 1 ∈ P ^ N := fun P hP => by
    by_cases hfix : P.comap s = P
    · simp only [a, hfix, if_true]
      exact hz P hP hfix
    · have hfix' : ¬ P = P.comap s := fun h => hfix h.symm
      simp only [a, hcc, if_neg hfix, if_neg hfix']
      rcases trichotomous_of WellOrderingRel P (P.comap s) with h | h | h
      · rw [if_pos h, if_neg (asymm h)]; simp
      · exact (hfix' h).elim
      · rw [if_pos h, if_neg (asymm h)]; simp
  obtain ⟨l, hl⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun P => P) (fun _ => N)
    hpr (fun _ _ _ _ h => h) (fun P => a P.1)
  have hmem : ∀ P ∈ S, l * s l + 1 ∈ P ^ N := fun P hP => by
    obtain ⟨h1, h3⟩ := (hS P).1 hP
    have hP' : P.comap s ∈ S := (hS _).2 ⟨Ideal.comap_isPrime s P, by rwa [Ideal.mem_comap, hsn]⟩
    have e1 : l - a P ∈ P ^ N := hl P hP
    have e2 : s (l - a (P.comap s)) ∈ P ^ N := Ideal.le_comap_pow s N (hl _ hP')
    have : l * s l + 1 = s l * (l - a P) + a P * s (l - a (P.comap s)) + (a P * s (a (P.comap s)) + 1) := by
      rw [map_sub]; ring
    rw [this]
    exact add_mem (add_mem (Ideal.mul_mem_left _ _ e1) (Ideal.mul_mem_left _ _ e2)) (ha P hP)
  refine ⟨l, Ideal.mem_span_singleton.1 (hN ?_)⟩
  rw [← Finset.prod_pow, ← IsDedekindDomain.inf_pow_eq_prod_of_prime S (fun P => P) (fun _ => N) hpr
    (fun _ _ _ _ h => h), Submodule.mem_finsetInf]
  exact hmem

theorem exists_norm_eq_neg_one : ∀ (D : D7) (m : ℕ), 0 < m → ∃ l b : 𝓞 D.host.E, (l : D.host.E) * D.host.conj (l : D.host.E) = -1 + (m : D.host.E) * (b : D.host.E) := by
  intro D m hm
  have hc : ∀ x, D.host.conj (D.host.conj x) = x := by
    obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    refine fun x => φ.injective ?_
    have h1 := D.host.conjE_apply φ
    exact (h1 _).trans ((congrArg _ (h1 x)).trans (Complex.conj_conj _))
  let s : 𝓞 D.host.E →+* 𝓞 D.host.E := (Formalism.L2.Pj.barE D).toRingHom
  have hs : ∀ x, ((s x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := Formalism.L2.Pj.barE_eq_conj D
  obtain ⟨l, b, hb⟩ := exists_dvd_mul_involution_add_one s
    (fun x => RingOfIntegers.ext (by rw [hs, hs, hc])) (m : 𝓞 D.host.E) (by exact_mod_cast hm.ne')
    (map_natCast s m)
    (fun P hP => Ideal.finiteQuotientOfFreeOfNeBot P
      (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)))
    (fun P hP => by
      obtain ⟨θ, hθ⟩ := Formalism.L2.Pj.cmUnram_conj D P hP
      exact ⟨θ, fun h => hθ (by
        have h' := P.neg_mem h
        rw [neg_sub] at h'
        exact h')⟩)
    (fun P hP hsP h2 => by
      have hw : s (Formalism.L2.Pj.w0E D) = 1 - Formalism.L2.Pj.w0E D := Formalism.L2.Pj.conj_w0E D
      have hsq := Formalism.L2.Pj.w0E_sq D
      obtain ⟨k, hk⟩ : ∃ k, Formalism.L2.Pj.mE D = 2 * k := by
        have h1 := D.host.hyp.2.2.2.1
        have h3 := Formalism.L2.Pj.mE_spec D
        exact ⟨Formalism.L2.Pj.mE D / 2, by omega⟩
      rw [hk] at hsq
      push_cast at hsq
      set w := Formalism.L2.Pj.w0E D
      have hm : w * (1 - w) ∈ P := by
        have : w * (1 - w) = k * 2 := by linear_combination -hsq
        rw [this]; exact P.mul_mem_left _ h2
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one]
      rcases hP.isPrime.mem_or_mem hm with h | h
      · have h' := hsP _ h
        rw [hw] at h'
        simpa using P.add_mem h h'
      · have h' := hsP _ h
        rw [map_sub, map_one, hw] at h'
        simpa using P.add_mem h h')
  refine ⟨l, b, ?_⟩
  have := congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hb
  simp only [map_add, map_mul, map_one, map_natCast] at this
  rw [← hs]
  linear_combination this

end GlobalTheory.NegOneNorm
