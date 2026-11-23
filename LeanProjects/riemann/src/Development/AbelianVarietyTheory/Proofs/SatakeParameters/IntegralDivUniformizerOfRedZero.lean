import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.TypePrimeUnif

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq {X : _root_.Formalism.L2.Col.Fields} (hX : X.Ok) {Pr : _root_.Formalism.L2.Col.Primes X}
    (hP : Pr.Ok) (i : Fin 2) (P : HeightOneSpectrum (𝓞 X.E))
    (hv : P ∈ Pr.vG i) : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 := by
  classical
  refine ⟨hP.g_mem hv, fun hsq => ?_⟩
  have hdiv : ∀ Q ∈ Pr.vG i, X.conjO (Pr.piG i) ∈ Q.asIdeal := fun Q hQ =>
    _root_.Formalism.L2.Col.decoFin_mem_of_mem_divs (show Q ∈ _root_.Formalism.L2.Col.divs (X.conjO (Pr.piG i)) from hQ)
  have hg1 : 1 < Pr.g i := (hP.g_prime i).one_lt
  have hN : Ideal.absNorm (Ideal.span {X.conjO (Pr.piG i)}) = Pr.g i ^ X.f := by
    have h1 : Ideal.absNorm (Ideal.span {Pr.piG i}) * Ideal.absNorm (Ideal.span {X.conjO (Pr.piG i)})
        = Pr.g i ^ (2 * X.f) := by
      rw [← map_mul, Ideal.span_singleton_mul_span_singleton, hP.piG_norm i, X.absNorm_nat, hX.rankQ]
    rw [X.absNorm_conjO, ← sq, pow_mul'] at h1
    rw [X.absNorm_conjO]
    exact Nat.pow_left_injective two_ne_zero h1
  have hπP : Pr.piG i ∉ P.asIdeal := fun h => by
    obtain ⟨a, b, hab⟩ := hP.piG_cop i
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left a h) (P.asIdeal.mul_mem_left b (hdiv P hv))
  have hcop : IsCoprime (P.asIdeal ^ 2) (Ideal.span {Pr.piG i}) := by
    apply IsCoprime.pow_left
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have heq := P.isMaximal.eq_of_le h le_sup_left
    exact hπP (by rw [heq]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hP2 : P.asIdeal ^ 2 ∣ Ideal.span {X.conjO (Pr.piG i)} := by
    have h : P.asIdeal ^ 2 ∣ Ideal.span {Pr.piG i} * Ideal.span {X.conjO (Pr.piG i)} := by
      rw [Ideal.span_singleton_mul_span_singleton, hP.piG_norm i, Ideal.dvd_span_singleton]
      exact hsq
    first
      | exact hcop.dvd_of_dvd_mul_left h
      | exact hcop.dvd_of_dvd_mul_right h
  let e : HeightOneSpectrum (𝓞 X.E) → ℕ := fun Q => if Q = P then 2 else 1
  have hall : ∏ Q ∈ Pr.vG i, Q.asIdeal ^ e Q ∣ Ideal.span {X.conjO (Pr.piG i)} := by
    apply Finset.prod_dvd_of_coprime
    · intro Q _ Q' _ hne
      simp only [Function.onFun]
      apply IsCoprime.pow
      rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne Q.isMaximal Q'.isMaximal
        (fun h => hne (HeightOneSpectrum.ext h))
    · intro Q hQ
      by_cases h : Q = P
      · subst h
        simpa [e] using hP2
      · simpa [e, h, Ideal.dvd_span_singleton] using hdiv Q hQ
  have hnorm := map_dvd Ideal.absNorm hall
  rw [map_prod, hN] at hnorm
  have hcount : ∏ Q ∈ Pr.vG i, Ideal.absNorm (Q.asIdeal ^ e Q) = Pr.g i ^ (X.f + 1) := by
    rw [Finset.prod_congr rfl (fun Q hQ => show Ideal.absNorm (Q.asIdeal ^ e Q) = Pr.g i ^ e Q by
      rw [map_pow, hP.vG_norm i Q hQ]), Finset.prod_pow_eq_pow_sum]
    congr 1
    have he : ∀ Q, e Q = 1 + if Q = P then 1 else 0 := fun Q => by
      by_cases h : Q = P <;> simp [e, h]
    simp only [he, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
      Finset.sum_ite_eq', hv, if_true, hP.vG_card i]
  rw [hcount] at hnorm
  have := (Nat.pow_dvd_pow_iff_le_right hg1).mp hnorm
  omega

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (g : 𝓞 E)
    (h1 : g ∈ w.asIdeal) (h2 : g ∉ w.asIdeal ^ 2) (a : E) (ha : _root_.Formalism.L2.Col.IntAt w a) (h0 : _root_.Formalism.L2.Col.redP w a = 0) :
    _root_.Formalism.L2.Col.IntAt w (a / algebraMap (𝓞 E) E g) := by
  haveI := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  have key : ∃ c r, ∃ s ∉ w.asIdeal, algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk w.asIdeal s * c = Ideal.Quotient.mk w.asIdeal r := by
    obtain ⟨r, s, hs, hsr⟩ := ha
    have hs0 : Ideal.Quotient.mk w.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    exact ⟨(Ideal.Quotient.mk w.asIdeal s)⁻¹ * Ideal.Quotient.mk w.asIdeal r, r, s, hs, hsr,
      mul_inv_cancel_left₀ hs0 _⟩
  unfold _root_.Formalism.L2.Col.redP at h0
  rw [dif_pos key] at h0
  have hspec := key.choose_spec
  rw [h0] at hspec
  obtain ⟨r, s, hs, hsr, hc⟩ := hspec
  rw [mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at hc
  obtain ⟨J, hJ⟩ := (Ideal.dvd_span_singleton (I := w.asIdeal) (x := g)).mpr h1
  have hJw : ¬ J ≤ w.asIdeal := fun hle => h2 (by
    rw [sq]
    exact Ideal.mul_mono_right hle (hJ ▸ Ideal.mem_span_singleton_self g))
  obtain ⟨t, htJ, htw⟩ := Set.not_subset.mp hJw
  have hrt : r * t ∈ Ideal.span {g} := hJ ▸ Ideal.mul_mem_mul hc htJ
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hrt
  have hg0 : algebraMap (𝓞 E) E g ≠ 0 := by
    intro h
    apply h2
    rw [(IsFractionRing.injective (𝓞 E) E) (h.trans (map_zero _).symm)]
    exact zero_mem _
  refine ⟨x, s * t, fun hst => (w.isPrime.mem_or_mem hst).elim hs htw, ?_⟩
  have hxE : algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g =
      algebraMap (𝓞 E) E r * algebraMap (𝓞 E) E t := by
    rw [← map_mul, ← map_mul, hx]
  have hmain : algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E t * a =
      algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g := by
    linear_combination algebraMap (𝓞 E) E t * hsr - hxE
  calc algebraMap (𝓞 E) E (s * t) * (a / algebraMap (𝓞 E) E g)
      = algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E t * a / algebraMap (𝓞 E) E g := by
        rw [map_mul]; ring
    _ = algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E g / algebraMap (𝓞 E) E g := by rw [hmain]
    _ = algebraMap (𝓞 E) E x := mul_div_cancel_right₀ _ hg0

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.TypePrimeUnif.intAt_div_qOf : ∀ (X : _root_.Formalism.L2.Col.Fields) (Pr : _root_.Formalism.L2.Col.Primes X), X.Ok → Pr.Ok →
    ∀ w ∈ Pr.vGs, ∀ a : X.E, _root_.Formalism.L2.Col.IntAt w a →
    _root_.Formalism.L2.Col.redP w a = 0 → _root_.Formalism.L2.Col.IntAt w (a / (_root_.Formalism.L2.Col.qOf w : X.E)) := by
  classical
  intro X Pr hX hP w hw a ha h0
  have hw' : w ∈ Pr.vG 0 ∪ Pr.vG 1 := hw
  obtain ⟨i, hv⟩ : ∃ i, w ∈ Pr.vG i := by
    rcases Finset.mem_union.mp hw' with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hq : (_root_.Formalism.L2.Col.qOf w : X.E) = algebraMap (𝓞 X.E) X.E ((Pr.g i : ℕ) : 𝓞 X.E) := by
    unfold _root_.Formalism.L2.Col.qOf
    rw [map_natCast, hP.vG_norm i w hv]
  have hgw := _root_.GlobalTheory.TypePrimeUnif.typePrime_mem_and_notMem_sq hX hP i w hv
  rw [hq]
  exact _root_.GlobalTheory.TypePrimeUnif.intAt_div_of_notMem_sq w _ hgw.1 hgw.2 a ha h0

end GlobalTheory.TypePrimeUnif
