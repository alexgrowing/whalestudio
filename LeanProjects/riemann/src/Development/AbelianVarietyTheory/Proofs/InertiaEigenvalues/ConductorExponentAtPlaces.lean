import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.ExpCond

theorem not_mem_sq_of_not_dvd_discr {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (w : HeightOneSpectrum (𝓞 E)) (hv : (p : 𝓞 E) ∈ w.asIdeal) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro h2
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hvZ : ((p : ℤ) : 𝓞 E) ∈ w.asIdeal := by simpa using hv
  have hun : Algebra.IsUnramifiedAt ℤ w.asIdeal :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hpZ).mp hd w.asIdeal w.isPrime hvZ
  have hunder : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    symm
    refine (PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible).eq_of_le
      (Ideal.IsPrime.under ℤ w.asIdeal).ne_top ?_
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_comap.mpr (by simpa using hv)
  let := Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under ℤ) w.asIdeal
  have hloc := ((Algebra.isUnramifiedAt_iff_map_eq ℤ (w.asIdeal.under ℤ) w.asIdeal).mp hun).2
  have h1 := (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff w.ne_bot Ideal.map_comap_le).mpr hloc
  refine (Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).mpr ?_ h1
  have hunder' : Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal = Ideal.span {(p : ℤ)} := hunder
  rw [hunder', Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
  simpa using h2

variable {E : Type} [Field E] [NumberField E]

theorem mem_below (w : HeightOneSpectrum (𝓞 E)) (p : ℕ) : (p : OF E) ∈ (below w).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
  show (p : OF E) ∈ Ideal.comap (algebraMap (OF E) (𝓞 E)) w.asIdeal ↔ _
  rw [Ideal.mem_comap, map_natCast]

theorem emult_zero (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (h : (p : 𝓞 E) ∉ w.asIdeal) :
    emultiplicity (below w).asIdeal (Ideal.span {(p : OF E)}) = 0 := by
  rw [emultiplicity_eq_zero, Ideal.dvd_span_singleton, mem_below]
  exact h

theorem emult_one (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E) (h : (p : 𝓞 E) ∈ w.asIdeal) :
    emultiplicity (below w).asIdeal (Ideal.span {(p : OF E)}) = 1 := by
  have hle : Ideal.map (algebraMap (OF E) (𝓞 E)) (below w).asIdeal ≤ w.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (fun x hx => hx)
  have hdvd : (below w).asIdeal ^ 1 ∣ Ideal.span {(p : OF E)} := by
    rw [pow_one, Ideal.dvd_span_singleton, mem_below]
    exact h
  have hndvd : ¬ (below w).asIdeal ^ (1 + 1) ∣ Ideal.span {(p : OF E)} := by
    intro h2
    rw [Ideal.dvd_span_singleton] at h2
    have hm := Ideal.mem_map_of_mem (algebraMap (OF E) (𝓞 E)) h2
    rw [Ideal.map_pow, map_natCast] at hm
    have hsq : (Ideal.map (algebraMap (OF E) (𝓞 E)) (below w).asIdeal) ^ (1 + 1) ≤ w.asIdeal ^ 2 := by
      rw [show (1 + 1 : ℕ) = 2 from rfl, pow_two, pow_two]
      exact Ideal.mul_mono hle hle
    exact not_mem_sq_of_not_dvd_discr hp hd w h (hsq hm)
  have := (emultiplicity_eq_coe (n := 1)).mpr ⟨hdvd, hndvd⟩
  simpa using this

theorem not_mem_of_ne (w : HeightOneSpectrum (𝓞 E)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h : (p : 𝓞 E) ∈ w.asIdeal) : (q : 𝓞 E) ∉ w.asIdeal := by
  intro hq'
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  obtain ⟨u, v, huv⟩ := hc
  have e : (u : 𝓞 E) * (p : 𝓞 E) + (v : 𝓞 E) * (q : 𝓞 E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) huv
    push_cast at this
    exact this
  have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
    rw [← e]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h) (w.asIdeal.mul_mem_left _ hq')
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem emult_cond (v v0 : HeightOneSpectrum (OF E)) (a b c d : ℕ) :
    emultiplicity v.asIdeal (Ideal.span {((a * b * c * d : ℕ) : OF E)} ^ 2 * v0.asIdeal) =
      2 * (emultiplicity v.asIdeal (Ideal.span {(a : OF E)}) + emultiplicity v.asIdeal (Ideal.span {(b : OF E)}) +
        emultiplicity v.asIdeal (Ideal.span {(c : OF E)}) + emultiplicity v.asIdeal (Ideal.span {(d : OF E)})) +
        emultiplicity v.asIdeal v0.asIdeal := by
  have hv := v.prime
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    emultiplicity_mul hv, emultiplicity_pow hv, emultiplicity_mul hv, emultiplicity_mul hv,
    emultiplicity_mul hv]
  push_cast
  ring

theorem emult_ne {v v0 : HeightOneSpectrum (OF E)} (h : v ≠ v0) : emultiplicity v.asIdeal v0.asIdeal = 0 := by
  rw [emultiplicity_eq_zero, Ideal.dvd_iff_le]
  intro hle
  apply h
  exact HeightOneSpectrum.ext ((v0.isMaximal.eq_of_le v.isPrime.ne_top hle).symm)

theorem emult_self (v : HeightOneSpectrum (OF E)) : emultiplicity v.asIdeal v.asIdeal = 1 := by
  simpa using emultiplicity_pow_self_of_prime v.prime 1

end GlobalTheory.LamTie.ExpCond

namespace GlobalTheory.LamTie

open ExpCond

theorem expIn_cond0 : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), PlacesOk H q0 w0 →
    ∀ w : HeightOneSpectrum (𝓞 H.E), (Over4 H w → expIn (cond0 H w0) (below w) = 2) ∧
      (below w = below w0 → ¬ Over4 H w ∧ expIn (cond0 H w0) (below w) = 1) ∧
      (¬ Over4 H w → below w ≠ below w0 → expIn (cond0 H w0) (below w) = 0) := by
  intro R H q0 w0 hP w
  obtain ⟨hw0, hdist, hspl⟩ := hP
  have hq0 : (q0 : 𝓞 H.E) ∈ w0.asIdeal := hw0
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or, or_false] at hdist
  have pr : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := fun p hp => (hspl p hp).1
  have dc : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ¬ (p : ℤ) ∣ discr H.E := fun p hp => (hspl p hp).2.2.1
  have uniq : ∀ x ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ y ∈ [H.g 0, H.g 1, H.pde, H.pde', q0],
      (x : 𝓞 H.E) ∈ w.asIdeal → (y : 𝓞 H.E) ∈ w.asIdeal → x = y := by
    intro x hx y hy mx my
    by_contra hxy
    exact not_mem_of_ne w (pr x hx) (pr y hy) hxy mx my
  have key : emultiplicity (below w).asIdeal (cond0 H w0) =
      2 * (emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)})) +
      emultiplicity (below w).asIdeal (below w0).asIdeal :=
    emult_cond (below w) (below w0) (H.g 0) (H.g 1) H.pde H.pde'
  have qw : below w = below w0 → (q0 : 𝓞 H.E) ∈ w.asIdeal := fun heq =>
    (mem_below w q0).mp (heq ▸ (mem_below w0 q0).mpr hq0)
  have toExp : ∀ n : ℕ, emultiplicity (below w).asIdeal (cond0 H w0) = n → expIn (cond0 H w0) (below w) = n :=
    fun n h => multiplicity_eq_of_emultiplicity_eq_some h
  have m0 : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m1 : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m2 : (H.pde : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m3 : (H.pde' : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have n0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) = 0 :=
    emult_zero w
  have n1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) = 0 :=
    emult_zero w
  have n2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) = 0 :=
    emult_zero w
  have n3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)}) = 0 :=
    emult_zero w
  have u := fun x (hx : x ∈ [H.g 0, H.g 1, H.pde, H.pde', q0]) y (hy : y ∈ [H.g 0, H.g 1, H.pde, H.pde', q0])
    (hne : x ≠ y) (mx : (x : 𝓞 H.E) ∈ w.asIdeal) (my : (y : 𝓞 H.E) ∈ w.asIdeal) => hne (uniq x hx y hy mx my)
  refine ⟨fun hO => ?_, fun heq => ?_, fun hO hne => ?_⟩
  · have hne : below w ≠ below w0 := by
      intro heq
      have hq := qw heq
      rcases hO with ⟨k, hk⟩ | hk | hk
      · fin_cases k
        · have hk : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal := hk
          exact u _ (by simp) _ (by simp) (by omega) hk hq
        · have hk : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal := hk
          exact u _ (by simp) _ (by simp) (by omega) hk hq
      · exact u _ (by simp) _ (by simp) (by omega) hk hq
      · exact u _ (by simp) _ (by simp) (by omega) hk hq
    apply toExp
    rw [key, emult_ne hne]
    rcases hO with ⟨k, hk⟩ | hk | hk
    · fin_cases k
      · have hk : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal := hk
        rw [m0 hk, n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
        norm_num
      · have hk : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal := hk
        rw [m1 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
        norm_num
    · have hk : (H.pde : 𝓞 H.E) ∈ w.asIdeal := hk
      rw [m2 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
      norm_num
    · have hk : (H.pde' : 𝓞 H.E) ∈ w.asIdeal := hk
      rw [m3 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
      norm_num
  · have hq := qw heq
    have a0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    refine ⟨?_, ?_⟩
    · rintro (⟨k, hk⟩ | hk | hk)
      · fin_cases k
        · exact a0 hk
        · exact a1 hk
      · exact a2 hk
      · exact a3 hk
    · apply toExp
      rw [key, n0 a0, n1 a1, n2 a2, n3 a3, heq, emult_self]
      norm_num
  · have a0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inl ⟨0, h⟩)
    have a1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inl ⟨1, h⟩)
    have a2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inr (Or.inl h))
    have a3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inr (Or.inr h))
    apply toExp
    rw [key, n0 a0, n1 a1, n2 a2, n3 a3, emult_ne hne]
    norm_num

end GlobalTheory.LamTie
