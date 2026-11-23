import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.Columns.NonDeg
import Formalism.LocalToGlobal.Columns.CyclotomicIsCyclotomicExtension
import Formalism.LocalToGlobal.Columns.AtTOwedC

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Unram

variable {X : Fields} {Pr : Primes X}

theorem ciPiG_ne_zero (hPr : Pr.Ok) (i : Fin 2) : Pr.piG i ≠ 0 := by
  intro h
  have h1 := hPr.piG_norm i
  rw [h, zero_mul] at h1
  have h2 : ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := by exact_mod_cast (hPr.g_prime i).ne_zero
  exact h2 h1.symm

theorem ciConjPiG_ne_zero (hPr : Pr.Ok) (i : Fin 2) : X.conjO (Pr.piG i) ≠ 0 := by
  intro h
  have h1 := hPr.piG_norm i
  rw [h, mul_zero] at h1
  have h2 : ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := by exact_mod_cast (hPr.g_prime i).ne_zero
  exact h2 h1.symm

theorem ciAbsNorm_conjPiG (hX : X.Ok) (hPr : Pr.Ok) (i : Fin 2) :
    Ideal.absNorm (Ideal.span {X.conjO (Pr.piG i)}) = Pr.g i ^ X.f := by
  have h1 : Ideal.absNorm (Ideal.span {Pr.piG i}) * Ideal.absNorm (Ideal.span {X.conjO (Pr.piG i)}) = Pr.g i ^ (2 * X.f) := by
    rw [← map_mul, Ideal.span_singleton_mul_span_singleton, hPr.piG_norm, X.absNorm_nat, hX.rankQ]
  rw [X.absNorm_conjO] at h1
  have h2 : Ideal.absNorm (Ideal.span {Pr.piG i}) ^ 2 = (Pr.g i ^ X.f) ^ 2 := by
    rw [sq, h1, ← pow_mul, mul_comm]
  rw [X.absNorm_conjO]
  exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2

theorem ciConjPiG_notMem_sq (hX : X.Ok) (hPr : Pr.Ok) (i : Fin 2) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vG i) :
    X.conjO (Pr.piG i) ∉ P.asIdeal ^ 2 := by
  classical
  intro hmem
  have h0 := ciConjPiG_ne_zero hPr i
  let fam : HeightOneSpectrum (𝓞 X.E) → Ideal (𝓞 X.E) := fun Q => if Q = P then P.asIdeal ^ 2 else Q.asIdeal
  have hdvd : ∀ Q ∈ Pr.vG i, fam Q ∣ Ideal.span {X.conjO (Pr.piG i)} := by
    intro Q hQ
    rw [Ideal.dvd_span_singleton]
    by_cases hQP : Q = P
    · simp only [fam, if_pos hQP]; exact hmem
    · simp only [fam, if_neg hQP]; exact (mem_divs h0 Q).1 hQ
  have hbase : ∀ Q Q' : HeightOneSpectrum (𝓞 X.E), Q ≠ Q' → IsCoprime Q.asIdeal Q'.asIdeal := by
    intro Q Q' hne
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne Q.isMaximal Q'.isMaximal (fun h => hne (HeightOneSpectrum.ext h))
  have hcop : (↑(Pr.vG i) : Set (HeightOneSpectrum (𝓞 X.E))).Pairwise (Function.onFun IsCoprime fam) := by
    intro Q _ Q' _ hne
    show IsCoprime (fam Q) (fam Q')
    by_cases hQP : Q = P
    · have hQ'P : Q' ≠ P := fun h => hne (hQP.trans h.symm)
      simp only [fam, if_pos hQP, if_neg hQ'P]
      exact (hbase P Q' hQ'P.symm).pow_left
    · by_cases hQ'P : Q' = P
      · simp only [fam, if_neg hQP, if_pos hQ'P]
        exact (hbase Q P hQP).pow_right
      · simp only [fam, if_neg hQP, if_neg hQ'P]
        exact hbase Q Q' hne
  have hprod : ∏ Q ∈ Pr.vG i, fam Q ∣ Ideal.span {X.conjO (Pr.piG i)} := Finset.prod_dvd_of_coprime hcop hdvd
  have hN : Ideal.absNorm (∏ Q ∈ Pr.vG i, fam Q) = Pr.g i ^ (X.f + 1) := by
    rw [map_prod]
    have h1 : ∀ Q ∈ Pr.vG i, Ideal.absNorm (fam Q) = Pr.g i * (if Q = P then Pr.g i else 1) := by
      intro Q hQ
      by_cases hQP : Q = P
      · simp only [fam, if_pos hQP]
        rw [map_pow, hPr.vG_norm i P hP, sq]
      · simp only [fam, if_neg hQP]
        rw [hPr.vG_norm i Q hQ, mul_one]
    rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const, hPr.vG_card, Finset.prod_ite_eq', if_pos hP,
      pow_succ]
  have h3 := map_dvd Ideal.absNorm hprod
  rw [hN, ciAbsNorm_conjPiG hX hPr i] at h3
  have := (Nat.pow_dvd_pow_iff_le_right (hPr.g_prime i).one_lt).1 h3
  omega

theorem ciPiG_notMem (hPr : Pr.Ok) (i : Fin 2) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) :
    Pr.piG i ∉ w.asIdeal := by
  intro h
  have hc : X.conjO (Pr.piG i) ∈ w.asIdeal := (mem_divs (ciConjPiG_ne_zero hPr i) w).1 hw
  obtain ⟨a, b, hab⟩ := hPr.piG_cop i
  have h1 : (1 : 𝓞 X.E) ∈ w.asIdeal := by
    rw [← hab]
    exact add_mem (w.asIdeal.mul_mem_left _ h) (w.asIdeal.mul_mem_left _ hc)
  exact one_notMem w h1

theorem ciG_notMem_sq (hX : X.Ok) (hPr : Pr.Ok) (i : Fin 2) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2 := by
  intro h
  rw [← hPr.piG_norm i] at h
  have := w.isPrime
  rcases Ideal.IsPrime.mul_mem_pow w.asIdeal h with h1 | h1
  · exact ciPiG_notMem hPr i hw h1
  · exact ciConjPiG_notMem_sq hX hPr i hw h1

theorem ciVGs_cases {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) : ∃ i : Fin 2, w ∈ Pr.vG i := by
  classical
  rcases Finset.mem_union.1 hw with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

theorem ciQOf_eq (hPr : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} {i : Fin 2} (hw : w ∈ Pr.vG i) : qOf w = Pr.g i :=
  hPr.vG_norm i w hw

theorem ciQ_notMem_sq (hX : X.Ok) (hPr : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) :
    ((qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2 := by
  obtain ⟨i, hi⟩ := ciVGs_cases hw
  rw [ciQOf_eq hPr hi]
  exact ciG_notMem_sq hX hPr i hi

theorem ciQ_mem {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : ((qOf w : ℕ) : 𝓞 E) ∈ w.asIdeal :=
  Ideal.absNorm_mem w.asIdeal

end Unram

section Red

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ciQ_ne_zero (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) : (q : E) ≠ 0 := by
  intro h
  have hq : q = 0 := by exact_mod_cast h
  subst hq
  exact hu (by simp)

theorem ciIntAt_div (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {a : E}
    (ha : IntAt P a) (h0 : redP P a = 0) : IntAt P (a / (q : E)) := by
  obtain ⟨r, s, hs, h⟩ := ha
  have hr : r ∈ P.asIdeal := by
    have h1 := reduction_spec P hs h
    rw [h0, mul_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1.symm
  have hle : Ideal.span {((q : ℕ) : 𝓞 E)} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hq
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hJ'
    apply hu
    have h2 : Ideal.span {((q : ℕ) : 𝓞 E)} ≤ P.asIdeal ^ 2 := by
      rw [hJ, sq]
      exact Ideal.mul_mono_right hJ'
    exact h2 (Ideal.mem_span_singleton_self _)
  obtain ⟨s', hs'J, hs'P⟩ := Set.not_subset.1 hJP
  have hmem : r * s' ∈ Ideal.span {((q : ℕ) : 𝓞 E)} := by
    rw [hJ]
    exact Ideal.mul_mem_mul hr hs'J
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hmem
  have hq0 := ciQ_ne_zero hu
  have ht' : algebraMap (𝓞 E) E t * (q : E) = algebraMap (𝓞 E) E r * algebraMap (𝓞 E) E s' := by
    have := congrArg (algebraMap (𝓞 E) E) ht
    rw [map_mul, map_mul, map_natCast] at this
    exact this
  refine ⟨t, s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs'P, ?_⟩
  rw [map_mul, show algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E s' * (a / (q : E)) =
    (algebraMap (𝓞 E) E s * a) * algebraMap (𝓞 E) E s' / (q : E) by ring, h, ← ht', mul_div_assoc, div_self hq0, mul_one]

theorem ciIntAt_q : IntAt P (q : E) := by
  simpa using IntAt.coe P (q : 𝓞 E)

theorem redP_natCast_eq_zero (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) : redP P (q : E) = 0 := by
  have h := reduction_coe P (q : 𝓞 E)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq] at h
  simpa using h

theorem ciRed_of_div (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {a : E} (h : IntAt P (a / (q : E))) :
    IntAt P a ∧ redP P a = 0 := by
  have ha : a = (q : E) * (a / q) := by field_simp
  refine ⟨?_, ?_⟩
  · rw [ha]
    exact ciIntAt_q.mul h
  · rw [ha, reduction_mul ciIntAt_q h, redP_natCast_eq_zero hq, zero_mul]

theorem ciIntAt_zero : IntAt P (0 : E) := by
  simpa using IntAt.coe P 0

theorem ciIntAt_one : IntAt P (1 : E) := by
  simpa using IntAt.coe P 1

theorem redP_zero : redP P (0 : E) = 0 := by
  simpa using reduction_coe P 0

theorem redP_one : redP P (1 : E) = 1 := by
  simpa using reduction_coe P 1

theorem ciIntAt_neg {a : E} (ha : IntAt P a) : IntAt P (-a) := by
  simpa using (IntAt.coe P (-1)).mul ha

theorem ciIntAt_sub {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by
  simpa [sub_eq_add_neg] using ha.add (ciIntAt_neg hb)

theorem redP_neg {a : E} (ha : IntAt P a) : redP P (-a) = -redP P a := by
  have h := reduction_mul (IntAt.coe P (-1)) ha
  rw [reduction_coe] at h
  simpa using h

theorem redP_sub {a b : E} (ha : IntAt P a) (hb : IntAt P b) : redP P (a - b) = redP P a - redP P b := by
  rw [sub_eq_add_neg, reduction_add ha (ciIntAt_neg hb), redP_neg hb, ← sub_eq_add_neg]

theorem ciIntAt_intCast (z : ℤ) : IntAt P (z : E) := by
  simpa using IntAt.coe P (z : 𝓞 E)

theorem redP_intCast (z : ℤ) : redP P (z : E) = (z : 𝓞 E ⧸ P.asIdeal) := by
  simpa using reduction_coe P (z : 𝓞 E)

theorem ciIntAt_sum {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) := Finset.sum_induction f (IntAt P) (fun _ _ ha hb => ha.add hb) ciIntAt_zero h

theorem redP_sum {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    redP P (∑ i ∈ s, f i) = ∑ i ∈ s, redP P (f i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp [redP_zero]) ?_
  intro k s hk ih h
  rw [Finset.sum_insert hk, Finset.sum_insert hk,
    reduction_add (h k (Finset.mem_insert_self k s)) (ciIntAt_sum s f fun i hi => h i (Finset.mem_insert_of_mem hi)),
    ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem ciIntAt_prod {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∏ i ∈ s, f i) := Finset.prod_induction f (IntAt P) (fun _ _ ha hb => ha.mul hb) ciIntAt_one h

theorem redP_prod {ι : Type} (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    redP P (∏ i ∈ s, f i) = ∏ i ∈ s, redP P (f i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp [redP_one]) ?_
  intro k s hk ih h
  rw [Finset.prod_insert hk, Finset.prod_insert hk,
    reduction_mul (h k (Finset.mem_insert_self k s)) (ciIntAt_prod s f fun i hi => h i (Finset.mem_insert_of_mem hi)),
    ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem ciIntAt_det {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n E) (h : ∀ i j, IntAt P (N i j)) : IntAt P N.det := by
  rw [Matrix.det_apply']
  exact ciIntAt_sum _ _ fun σ _ => (ciIntAt_intCast _).mul (ciIntAt_prod _ _ fun i _ => h _ _)

theorem redP_det {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n E) (h : ∀ i j, IntAt P (N i j)) :
    redP P N.det = (N.map (redP P)).det := by
  rw [Matrix.det_apply', Matrix.det_apply',
    redP_sum _ _ fun σ _ => (ciIntAt_intCast _).mul (ciIntAt_prod _ _ fun i _ => h _ _)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [reduction_mul (ciIntAt_intCast _) (ciIntAt_prod _ _ fun i _ => h _ _), redP_intCast,
    redP_prod _ _ fun i _ => h _ _]
  simp

theorem redP_add_natCast_mul (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) {a d : E} (hd : IntAt P d) :
    redP P (a + q * d) = redP P a := by
  have hqd : IntAt P ((q : E) * d) := ciIntAt_q.mul hd
  by_cases ha : IntAt P a
  · rw [reduction_add ha hqd, reduction_mul ciIntAt_q hd, redP_natCast_eq_zero hq, zero_mul, add_zero]
  · have ha' : ¬ IntAt P (a + q * d) := fun h => ha (by simpa using ciIntAt_sub h hqd)
    have hz : ∀ b : E, ¬ IntAt P b → redP P b = 0 := by
      intro b hb
      have hn : ¬ ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧
          algebraMap (𝓞 E) E s * b = algebraMap (𝓞 E) E r ∧
          Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r := by
        rintro ⟨c, r, s, hs, h1, -⟩
        exact hb ⟨r, s, hs, h1⟩
      rw [redP, dif_neg hn]
    rw [hz _ ha', hz _ ha]

theorem ciIntAt_add_iff {a d : E} (hd : IntAt P d) : IntAt P (a + d) ↔ IntAt P a := ⟨fun h => by simpa using ciIntAt_sub h hd, fun h => h.add hd⟩

end Red

section Scl

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

theorem ciMem_stdAt {n : ℕ} (x : Sp E n) : x ∈ stdAt E n P ↔ ∀ i, IntAt P (x i) := mem_localization_standardLattice P x

theorem ciMem_sclLat {N : ℕ} (e : ℕ → ℤ) (v : Sp E N) :
    v ∈ LocE.sclLat P q N e ↔ ∀ l : Fin N, IntAt P (((q : E) ^ e l.1)⁻¹ * v l) := by
  unfold LocE.sclLat
  rw [Submodule.mem_comap, ciMem_stdAt]
  simp [LinearMap.pi_apply, smul_eq_mul]

end Scl

section Cst

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

theorem ciCard (w : HeightOneSpectrum (𝓞 X.E)) : Nat.card (𝓞 X.E ⧸ w.asIdeal) = qOf w := by
  unfold qOf
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem ciFinite {w : HeightOneSpectrum (𝓞 X.E)} (hq : qOf w ≠ 0) : Finite (𝓞 X.E ⧸ w.asIdeal) :=
  Nat.finite_of_card_ne_zero (by rw [ciCard]; exact hq)

theorem ciQOf_prime (hPr : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) : (qOf w).Prime := by
  obtain ⟨i, hi⟩ := ciVGs_cases hw
  rw [ciQOf_eq hPr hi]
  exact hPr.g_prime i

theorem ciAddChar_one_ne {A : Type} [CommRing A] [Finite A] {p : ℕ} (hp : p.Prime) (hA : Nat.card A = p) {M : Type} [CommMonoid M]
    (ψ : AddChar A M) (hψ : ψ ≠ 1) : ψ 1 ≠ 1 := by
  intro h1
  apply hψ
  have : Fintype A := Fintype.ofFinite A
  have : NeZero p := ⟨hp.ne_zero⟩
  let e : ZMod p ≃+* A := ZMod.ringEquivOfPrime A hp (by rw [← Nat.card_eq_fintype_card, hA])
  ext x
  obtain ⟨n, rfl⟩ := e.surjective x
  have h2 : e n = (n.val : ℕ) • (1 : A) := by rw [nsmul_one, ← map_natCast e, ZMod.natCast_zmod_val]
  rw [h2, AddChar.map_nsmul_eq_pow, h1, one_pow, AddChar.one_apply]

open Classical in

def ciPsi {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (P : SB) (x : X.E) : X.K :=
  if IntAt P.1 ((qOf P.1 : X.E) * x) then psi0P Ch P.1 (redP P.1 ((qOf P.1 : X.E) * x)) else 1

open Classical in

def ciSq (P : HeightOneSpectrum (𝓞 X.E)) : X.K :=
  if h : P ∈ Pr.vGs ∧ Finite (𝓞 X.E ⧸ P.asIdeal) then
    haveI := h.2
    haveI := Fintype.ofFinite (𝓞 X.E ⧸ P.asIdeal)
    letI := Ideal.Quotient.field P.asIdeal
    gaussSum ((quadraticChar (𝓞 X.E ⧸ P.asIdeal)).ringHomComp (Int.castRingHom X.K)) (Ch.psi0 ⟨P, h.1⟩)
  else 0

def ciCst (SB : Finset (HeightOneSpectrum (𝓞 X.E))) (mq : ℕ → SB → X.K) : LocCst X SB where
  psi := ciPsi Ch
  D _ := 1
  sq P := ciSq Ch P.1
  muq := mq
  A := 1
  B := 1
  M := 1
  sharp := false

variable {Ch}

theorem ciSq_sq (hPr : Pr.Ok) (hCh : Ch.Ok) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) (h4 : qOf P % 4 = 1) :
    ciSq Ch P ^ 2 = (qOf P : X.K) := by
  classical
  have hqp := ciQOf_prime hPr hP
  have hfin : Finite (𝓞 X.E ⧸ P.asIdeal) := ciFinite hqp.ne_zero
  unfold ciSq
  rw [dif_pos ⟨hP, hfin⟩]
  let _ : Fintype (𝓞 X.E ⧸ P.asIdeal) := Fintype.ofFinite _
  let _ := Ideal.Quotient.field P.asIdeal
  have hcard : Fintype.card (𝓞 X.E ⧸ P.asIdeal) = qOf P := by rw [← Nat.card_eq_fintype_card, ciCard]
  have hq0 : ((qOf P : ℕ) : 𝓞 X.E ⧸ P.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (ciQ_mem P)
  have hch : ringChar (𝓞 X.E ⧸ P.asIdeal) = qOf P := by
    have h1 := ringChar.dvd hq0
    rcases (Nat.dvd_prime hqp).1 h1 with h2 | h2
    · exact absurd h2 (CharP.ringChar_ne_one)
    · exact h2
  have hq2 : ringChar (𝓞 X.E ⧸ P.asIdeal) ≠ 2 := by rw [hch]; omega
  have hχ₁ : (quadraticChar (𝓞 X.E ⧸ P.asIdeal)).ringHomComp (Int.castRingHom X.K) ≠ 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hq2
    refine MulChar.ne_one_iff.mpr ⟨a, ?_⟩
    show ((quadraticChar (𝓞 X.E ⧸ P.asIdeal) a : ℤ) : X.K) ≠ 1
    rw [ha]; norm_num
  have hχ₂ : ((quadraticChar (𝓞 X.E ⧸ P.asIdeal)).ringHomComp (Int.castRingHom X.K)).IsQuadratic :=
    MulChar.IsQuadratic.comp (quadraticChar_isQuadratic _) _
  have hψ : (Ch.psi0 ⟨P, hP⟩).IsPrimitive := AddChar.IsPrimitive.of_ne_one (hCh.psi_zero_nontrivial_character _)
  have h := gaussSum_sq hχ₁ hχ₂ hψ
  have key : ((quadraticChar (𝓞 X.E ⧸ P.asIdeal)).ringHomComp (Int.castRingHom X.K)) (-1) *
      ((Fintype.card (𝓞 X.E ⧸ P.asIdeal) : ℕ) : X.K) = (qOf P : X.K) := by
    show ((quadraticChar (𝓞 X.E ⧸ P.asIdeal) (-1) : ℤ) : X.K) * _ = _
    rw [quadraticChar_neg_one hq2, hcard, ZMod.χ₄_nat_one_mod_four h4]
    push_cast; ring
  convert h.trans key using 3

theorem ciCst_ok (hPr : Pr.Ok) (hCh : Ch.Ok) {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (hSB : ∀ P ∈ SB, P ∈ Pr.vGs)
    (h4 : ∀ P ∈ SB, qOf P % 4 = 1) {mq : ℕ → SB → X.K} : (ciCst Ch SB mq).Ok where
  psi_add P x y hx hy := by
    show ciPsi Ch P (x + y) = ciPsi Ch P x * ciPsi Ch P y
    simp only [ciCst, pow_one] at hx hy
    unfold ciPsi
    rw [if_pos hx, if_pos hy, mul_add, if_pos (hx.add hy), reduction_add hx hy, AddChar.map_add_eq_mul]
  psi_int P x hx := by
    show ciPsi Ch P x = 1
    unfold ciPsi
    rw [if_pos ((ciIntAt_q (q := qOf P.1)).mul hx), reduction_mul (ciIntAt_q (q := qOf P.1)) hx, redP_natCast_eq_zero (ciQ_mem P.1), zero_mul,
      AddChar.map_zero_eq_one]
  psi_ne P := by
    show ciPsi Ch P _ ≠ 1
    have hq0 : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast (ciQOf_prime hPr (hSB P.1 P.2)).ne_zero
    unfold ciPsi
    rw [mul_inv_cancel₀ hq0, if_pos ciIntAt_one, redP_one]
    unfold psi0P
    rw [dif_pos (hSB P.1 P.2)]
    have hqp := ciQOf_prime hPr (hSB P.1 P.2)
    have := ciFinite (w := P.1) hqp.ne_zero
    exact ciAddChar_one_ne hqp (ciCard P.1) _ (hCh.psi_zero_nontrivial_character _)
  D_pos _ := le_refl 1
  sq_sq P := ciSq_sq hPr hCh (hSB P.1 P.2) (h4 P.1 P.2)
  M_pos := le_refl 1
  M_le_A := le_refl 1
  M_le_B := le_refl 1
  B_pos := le_refl 1

end Cst

section Grp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ciInX_apply {n c : ℕ} (x : Fin n → E) (l : Fin (n + c)) :
    Loc.inX E n c x l = if h : l.1 < n then x ⟨l.1, h⟩ else 0 := by
  simp only [Loc.inX, LinearMap.pi_apply]
  split_ifs with h
  · rfl
  · rfl

theorem ciInX_castAdd {n c : ℕ} (x : Fin n → E) (l : Fin n) : Loc.inX E n c x (Fin.castAdd c l) = x l := by
  rw [ciInX_apply, dif_pos (by simp)]
  rfl

theorem ciFPos {k₀ c n l : ℕ} (hfr : c = 0 ∨ k₀ = n) (hl : l < n + c) : LocE.fPos k₀ c n l = l := by
  unfold LocE.fPos
  rcases hfr with rfl | rfl <;> split_ifs <;> omega

theorem ciFIdx {k₀ c n s : ℕ} (hfr : c = 0 ∨ k₀ = n) (hs : s < n + c) : LocE.fIdx k₀ c n s = s := by
  unfold LocE.fIdx
  rcases hfr with rfl | rfl <;> split_ifs <;> omega

theorem ciScE_lt {n : ℕ} (ex : ℕ → ℕ) {l : ℕ} (hl : l < n) : LocE.scE n ex l = 0 := by
  simp [LocE.scE, hl]

variable (P q) in
theorem ciMem_flagG {k₀ n c s : ℕ} (v : Sp E (n + c)) :
    v ∈ LocE.flagG P q k₀ n c s ↔ ∀ l : Fin (n + c),
      IntAt P (((q : E) ^ (LocE.scE n (fun i => i + 1) l.1 + if s ≤ LocE.fPos k₀ c n l.1 then 1 else 0))⁻¹ * v l) := by
  unfold LocE.flagG
  exact ciMem_sclLat P q _ v

theorem ciInX_single_mem_flagG {k₀ n c s : ℕ} (hfr : c = 0 ∨ k₀ = n) (l' : Fin n) (h1 : l'.1 < s) :
    Loc.inX E n c (Pi.single l' 1) ∈ LocE.flagG P q k₀ n c s := by
  rw [ciMem_flagG]
  intro m
  rw [ciInX_apply]
  by_cases hm : m.1 < n
  · rw [dif_pos hm]
    by_cases he : (⟨m.1, hm⟩ : Fin n) = l'
    · have hml : m.1 = l'.1 := by rw [← he]
      rw [he, Pi.single_eq_same, ciScE_lt _ hm, ciFPos hfr m.2, if_neg (by omega)]
      simpa using (ciIntAt_one (P := P))
    · rw [Pi.single_eq_of_ne he, mul_zero]
      exact ciIntAt_zero
  · rw [dif_neg hm, mul_zero]
    exact ciIntAt_zero

theorem ciJG_stab {k₀ r0 t n c : ℕ} {r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hr : r ∈ LocE.JG P q k₀ r0 t n c) {s : ℕ}
    (hs : s < r0 ∨ ∃ i, s = r0 + i * t) : r ∈ stabL E (n + c) (LocE.flagG P q k₀ n c s) := by
  have h2 := hr.2
  rcases hs with hs | hs
  · exact (h2.2 s hs).1
  · exact h2.1 s hs

theorem ciJG_entry (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {k₀ r0 t n c : ℕ} (hfr : c = 0 ∨ k₀ = n)
    {r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hr : r ∈ LocE.JG P q k₀ r0 t n c) {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : ∀ x, r (Loc.inX E n c x) = Loc.inX E n c (g x)) {s : ℕ} (hs : s < r0 ∨ ∃ i, s = r0 + i * t)
    {l l' : Fin n} (h1 : l'.1 < s) (h2 : s ≤ l.1) : redP P (g (Pi.single l' 1) l) = 0 := by
  have hm := ((ciJG_stab hr hs) _).2 (ciInX_single_mem_flagG (P := P) (q := q) hfr l' h1)
  rw [hg, ciMem_flagG] at hm
  have h3 := hm (Fin.castAdd c l)
  rw [ciInX_castAdd] at h3
  simp only [Fin.val_castAdd, ciScE_lt _ l.2, ciFPos hfr (show l.1 < n + c by omega), if_pos h2] at h3
  rw [zero_add, zpow_one, inv_mul_eq_div] at h3
  exact (ciRed_of_div hq hq0 h3).2

theorem ciJG_diag (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {k₀ r0 t n c : ℕ} (hfr : c = 0 ∨ k₀ = n)
    {r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hr : r ∈ LocE.JG P q k₀ r0 t n c) {g : Sp E n ≃ₗ[E] Sp E n}
    (hg : ∀ x, r (Loc.inX E n c x) = Loc.inX E n c (g x)) (hgi : ∀ l l', IntAt P (g (Pi.single l' 1) l))
    {l : Fin n} (hl : l.1 < r0) : redP P (g (Pi.single l 1) l) = 1 := by
  have hm := (hr.2.2 l.1 hl).2
  have hb : LocE.bvecG E q k₀ n c l.1 = Loc.inX E n c (Pi.single l 1) := by
    unfold LocE.bvecG
    rw [ciFIdx hfr (show l.1 < n + c by omega), ciScE_lt _ l.2, zpow_zero, one_smul]
    funext m
    rw [ciInX_apply]
    unfold Loc.eN
    by_cases hm : m.1 < n
    · rw [dif_pos hm]
      by_cases he : (⟨m.1, hm⟩ : Fin n) = l
      · rw [he, Pi.single_eq_same, if_pos (by rw [← he])]
      · rw [Pi.single_eq_of_ne he, if_neg (fun h => he (Fin.ext h))]
    · rw [dif_neg hm, if_neg (by omega)]
  rw [hb, hg, ← map_sub, ciMem_flagG] at hm
  have h3 := hm (Fin.castAdd c l)
  rw [ciInX_castAdd] at h3
  simp only [Fin.val_castAdd, ciScE_lt _ l.2, ciFPos hfr (show l.1 < n + c by omega), le_refl, if_true] at h3
  rw [zero_add, zpow_one, inv_mul_eq_div] at h3
  have h4 := (ciRed_of_div hq hq0 h3).2
  rw [Pi.sub_apply, Pi.single_eq_same, redP_sub (hgi l l) ciIntAt_one, redP_one, sub_eq_zero] at h4
  exact h4

theorem ciMem_lamY {n c : ℕ} (ex : ℕ → ℕ) (x : Sp E n) :
    Loc.inX E n c x ∈ LocE.lamY P q n c ex ↔ x ∈ stdAt E n P := by
  unfold LocE.lamY
  rw [ciMem_sclLat, ciMem_stdAt]
  constructor
  · intro h l
    have h1 := h (Fin.castAdd c l)
    rwa [ciInX_castAdd, Fin.val_castAdd, ciScE_lt _ l.2, zpow_zero, inv_one, one_mul] at h1
  · intro h m
    rw [ciInX_apply]
    by_cases hm : m.1 < n
    · rw [dif_pos hm, ciScE_lt _ hm, zpow_zero, inv_one, one_mul]
      exact h _
    · rw [dif_neg hm, mul_zero]
      exact ciIntAt_zero

theorem ciPrX_le {k₀ r0 t n c : ℕ} :
    Loc.prX (Loc.Cbe (LocE.JG P q k₀ r0 t n c) 1) ≤ GLint E n P := by
  rintro g ⟨r, hr, hg⟩ x
  have hr' : r ∈ LocE.JG P q k₀ r0 t n c := by
    have := hr.2
    simpa [MulAut.conj_apply] using this
  rw [← ciMem_lamY (P := P) (q := q) (c := c) (fun i => i + 1) (g x), ← hg]
  exact (hr'.1 _).trans (ciMem_lamY _ _)

end Grp

section Lift

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

variable (P) in
open Classical in

def ciLift (c : 𝓞 E ⧸ P.asIdeal) : 𝓞 E :=
  if c = 0 then 0 else if c = 1 then 1 else (Ideal.Quotient.mk_surjective c).choose

theorem ciLift_mk (c : 𝓞 E ⧸ P.asIdeal) : Ideal.Quotient.mk P.asIdeal (ciLift P c) = c := by
  unfold ciLift
  split_ifs with h0 h1
  · simp [h0]
  · simp [h1]
  · exact (Ideal.Quotient.mk_surjective c).choose_spec

theorem ciLift_zero : ciLift P 0 = 0 := by
  unfold ciLift
  simp

theorem ciLift_one : ciLift P 1 = 1 := by
  unfold ciLift
  simp

variable (P) in

def ciLiftO {n : ℕ} (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E) := M.map (ciLift P)

variable (P) in
def ciLiftM {n : ℕ} (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) : Matrix (Fin n) (Fin n) E :=
  (algebraMap (𝓞 E) E).mapMatrix (ciLiftO P M)

theorem ciLiftO_red {n : ℕ} (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) :
    (Ideal.Quotient.mk P.asIdeal).mapMatrix (ciLiftO P M) = M := by
  ext i j
  simp [ciLiftO, ciLift_mk]

theorem ciLiftM_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) (i j : Fin n) :
    ciLiftM P M i j = algebraMap (𝓞 E) E (ciLift P (M i j)) := rfl

theorem ciLiftO_det_notMem {n : ℕ} (M : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) : (ciLiftO P M.1).det ∉ P.asIdeal := by
  intro h
  have h1 : Ideal.Quotient.mk P.asIdeal (ciLiftO P M.1).det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
  rw [RingHom.map_det, ciLiftO_red] at h1
  exact (Matrix.isUnits_det_units M).ne_zero h1

theorem ciLiftM_det {n : ℕ} (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) :
    (ciLiftM P M).det = algebraMap (𝓞 E) E (ciLiftO P M).det := by
  rw [ciLiftM, RingHom.map_det]

theorem ciLiftM_det_ne {n : ℕ} (M : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) : (ciLiftM P M.1).det ≠ 0 := by
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := by
    first
    | exact FaithfulSMul.algebraMap_injective (𝓞 E) E
    | exact NoZeroSMulDivisors.algebraMap_injective (𝓞 E) E
    | exact RingOfIntegers.coe_injective
  rw [ciLiftM_det]
  intro h
  apply ciLiftO_det_notMem M
  rw [(map_eq_zero_iff _ hinj).mp h]
  exact Ideal.zero_mem _

theorem ciLiftM_int {n : ℕ} (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) (i j : Fin n) : IntAt P (ciLiftM P M i j) := by
  rw [ciLiftM_apply]
  exact IntAt.coe P _

theorem ciLiftM_red {n : ℕ} (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) (i j : Fin n) : redP P (ciLiftM P M i j) = M i j := by
  rw [ciLiftM_apply, reduction_coe, ciLift_mk]

theorem ciLiftM_inv_int {n : ℕ} (M : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) (i j : Fin n) : IntAt P ((ciLiftM P M.1)⁻¹ i j) := by
  have hne : algebraMap (𝓞 E) E (ciLiftO P M.1).det ≠ 0 := by
    rw [← ciLiftM_det]
    exact ciLiftM_det_ne M
  have hd : IntAt P ((ciLiftM P M.1).det)⁻¹ := by
    rw [ciLiftM_det]
    refine ⟨1, (ciLiftO P M.1).det, ciLiftO_det_notMem M, ?_⟩
    rw [map_one]
    exact mul_inv_cancel₀ hne
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  refine hd.mul ?_
  rw [ciLiftM, ← RingHom.map_adjugate, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact IntAt.coe P _

theorem ciLiftM_blockTriangular {n : ℕ} {β : Fin n → ℕ} {M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)} (h : M.BlockTriangular β) :
    (ciLiftM P M).BlockTriangular β := by
  intro i j hij
  rw [ciLiftM_apply, h hij, ciLift_zero, map_zero]

def ciExtM {n : ℕ} (c : ℕ) (A : Matrix (Fin n) (Fin n) E) : Matrix (Fin (n + c)) (Fin (n + c)) E :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin c) (Fin c) E))

theorem ciExtM_mul {n c : ℕ} (A B : Matrix (Fin n) (Fin n) E) : ciExtM c (A * B) = ciExtM c A * ciExtM c B := by
  simp only [ciExtM, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem ciExtM_one {n c : ℕ} : ciExtM c (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  simp [ciExtM]

theorem ciExtM_castAdd {n c : ℕ} (A : Matrix (Fin n) (Fin n) E) (v : Fin (n + c) → E) (l : Fin n) :
    (ciExtM c A).mulVec v (Fin.castAdd c l) = ∑ l' : Fin n, A l l' * v (Fin.castAdd c l') := by
  simp [ciExtM, Matrix.mulVec, dotProduct, Fin.sum_univ_add]

theorem ciExtM_natAdd {n c : ℕ} (A : Matrix (Fin n) (Fin n) E) (v : Fin (n + c) → E) (j : Fin c) :
    (ciExtM c A).mulVec v (Fin.natAdd n j) = v (Fin.natAdd n j) := by
  simp [ciExtM, Matrix.mulVec, dotProduct, Fin.sum_univ_add, Matrix.one_apply]

end Lift

section Mem

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

def ciEquiv {N : ℕ} (M M' : Matrix (Fin N) (Fin N) E) (h1 : M * M' = 1) (h2 : M' * M = 1) : Sp E N ≃ₗ[E] Sp E N :=
  LinearEquiv.ofLinear (Matrix.toLin' M) (Matrix.toLin' M') (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])

theorem ciEquiv_apply {N : ℕ} (M M' : Matrix (Fin N) (Fin N) E) (h1 : M * M' = 1) (h2 : M' * M = 1) (v : Sp E N) :
    ciEquiv M M' h1 h2 v = M.mulVec v := by
  simp [ciEquiv]

theorem ciEquiv_inv_apply {N : ℕ} (M M' : Matrix (Fin N) (Fin N) E) (h1 : M * M' = 1) (h2 : M' * M = 1) (v : Sp E N) :
    (ciEquiv M M' h1 h2)⁻¹ v = M'.mulVec v := by
  first
  | rfl
  | simp [ciEquiv]

theorem ciEquiv_stab {N : ℕ} {M M' : Matrix (Fin N) (Fin N) E} {h1 : M * M' = 1} {h2 : M' * M = 1} {L : Submodule (𝓞 E) (Sp E N)}
    (hM : ∀ v ∈ L, M.mulVec v ∈ L) (hM' : ∀ v ∈ L, M'.mulVec v ∈ L) : ciEquiv M M' h1 h2 ∈ stabL E N L := by
  show ∀ x, ciEquiv M M' h1 h2 x ∈ L ↔ x ∈ L
  intro x
  rw [ciEquiv_apply]
  constructor
  · intro h
    have h' := hM' _ h
    rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at h'
  · exact hM x

theorem ciExtM_inX {n c : ℕ} (A : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    (ciExtM c A).mulVec (Loc.inX E n c x) = Loc.inX E n c (A.mulVec x) := by
  funext l
  refine Fin.addCases (fun l => ?_) (fun j => ?_) l
  · rw [ciExtM_castAdd, ciInX_castAdd]
    simp only [ciInX_castAdd]
    rfl
  · rw [ciExtM_natAdd, ciInX_apply, ciInX_apply, dif_neg (by simp), dif_neg (by simp)]

theorem ciExtM_fix {n c : ℕ} (A : Matrix (Fin n) (Fin n) E) (v : Sp E (n + c)) (hv : ∀ l : Fin n, v (Fin.castAdd c l) = 0) :
    (ciExtM c A).mulVec v = v := by
  funext l
  refine Fin.addCases (fun l => ?_) (fun j => ?_) l
  · rw [ciExtM_castAdd, hv l]
    simp [hv]
  · rw [ciExtM_natAdd]

theorem ciExtM_maps {n c : ℕ} (hq0 : (q : E) ≠ 0) (A : Matrix (Fin n) (Fin n) E) (e : ℕ → ℤ)
    (he : ∀ l l' : Fin n, IntAt P (A l l' * (q : E) ^ (e l'.1 - e l.1))) (v : Sp E (n + c))
    (hv : v ∈ LocE.sclLat P q (n + c) e) : (ciExtM c A).mulVec v ∈ LocE.sclLat P q (n + c) e := by
  rw [ciMem_sclLat] at hv ⊢
  intro m
  refine Fin.addCases (fun l => ?_) (fun j => ?_) m
  · rw [ciExtM_castAdd, Finset.mul_sum]
    refine ciIntAt_sum _ _ fun l' _ => ?_
    have e1 : ((q : E) ^ e (Fin.castAdd c l).1)⁻¹ * (A l l' * v (Fin.castAdd c l')) =
        (A l l' * (q : E) ^ (e l'.1 - e l.1)) * (((q : E) ^ e (Fin.castAdd c l').1)⁻¹ * v (Fin.castAdd c l')) := by
      simp only [Fin.val_castAdd]
      rw [zpow_sub₀ hq0]
      field_simp
    rw [e1]
    exact (he l l').mul (hv _)
  · rw [ciExtM_natAdd]
    exact hv _

theorem ciR1cond {n c : ℕ} (A : Matrix (Fin n) (Fin n) E) (r : Sp E (n + c) ≃ₗ[E] Sp E (n + c))
    (hr : ∀ v, r v = (ciExtM c A).mulVec v) : Loc.R1cond E n c r := by
  have hfixN : ∀ i : ℕ, r (Loc.eN E (n + c) (n + i)) = Loc.eN E (n + c) (n + i) := by
    intro i
    rw [hr, ciExtM_fix]
    intro l
    unfold Loc.eN
    rw [if_neg (by simp; omega)]
  refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
  · intro m hm
    have hm' : ¬ m.1 < n + i := hm
    refine Fin.addCases (motive := fun m => ¬ m.1 < n + i → (r v) m = 0) (fun l hl => ?_) (fun j hj => ?_) m hm'
    · simp at hl; omega
    · rw [hr, ciExtM_natAdd]
      exact hv _ hj
  · have := hfixN 0
    rwa [add_zero] at this
  · rw [hfixN i, sub_self]
    exact zero_mem _

theorem extended_matrix_in_reduction {n c : ℕ} (A A' : Matrix (Fin n) (Fin n) E) (h1 : ciExtM c A * ciExtM c A' = 1) (h2 : ciExtM c A' * ciExtM c A = 1) :
    ciEquiv (ciExtM c A) (ciExtM c A') h1 h2 ∈ Loc.R1 E n c :=
  ⟨ciR1cond A _ (ciEquiv_apply _ _ h1 h2), ciR1cond A' _ (ciEquiv_inv_apply _ _ h1 h2)⟩

end Mem

section Mem2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ciFine_zero {a n : ℕ} {bl : List ℕ} {A : Matrix (Fin n) (Fin n) E} (hAt : A.BlockTriangular (fun i => fine a bl i.1))
    {l l' : Fin n} (h1 : l'.1 < a) (h2 : l'.1 < l.1) : A l l' = 0 := by
  apply hAt
  show fine a bl l'.1 < fine a bl l.1
  simp only [fine]
  split_ifs <;> omega

theorem ciHe_flag {k₀ n c a s : ℕ} {bl : List ℕ} (hfr : c = 0 ∨ k₀ = n) (A : Matrix (Fin n) (Fin n) E)
    (hAi : ∀ i j, IntAt P (A i j)) (hAt : A.BlockTriangular (fun i => fine a bl i.1)) (hs : s ≤ a ∨ n ≤ s) (l l' : Fin n) :
    IntAt P (A l l' * (q : E) ^ ((LocE.scE n (fun i => i + 1) l'.1 + if s ≤ LocE.fPos k₀ c n l'.1 then (1 : ℤ) else 0) -
      (LocE.scE n (fun i => i + 1) l.1 + if s ≤ LocE.fPos k₀ c n l.1 then (1 : ℤ) else 0))) := by
  rw [ciScE_lt _ l.2, ciScE_lt _ l'.2, ciFPos hfr (show l.1 < n + c by omega), ciFPos hfr (show l'.1 < n + c by omega), zero_add,
    zero_add]
  by_cases h1 : s ≤ l'.1 <;> by_cases h2 : s ≤ l.1
  · rw [if_pos h1, if_pos h2, sub_self, zpow_zero, mul_one]; exact hAi _ _
  · rw [if_pos h1, if_neg h2, sub_zero, zpow_one]; exact (hAi _ _).mul ciIntAt_q
  · have h3 : A l l' = 0 := by
      rcases hs with hs | hs
      · exact ciFine_zero hAt (by omega) (by omega)
      · omega
    rw [h3, zero_mul]; exact ciIntAt_zero
  · rw [if_neg h1, if_neg h2, sub_self, zpow_zero, mul_one]; exact hAi _ _

theorem ciBvecG {k₀ n c : ℕ} (hfr : c = 0 ∨ k₀ = n) (l : Fin n) :
    LocE.bvecG E q k₀ n c l.1 = Loc.inX E n c (Pi.single l 1) := by
  unfold LocE.bvecG
  rw [ciFIdx hfr (show l.1 < n + c by omega), ciScE_lt _ l.2, zpow_zero, one_smul]
  funext m
  rw [ciInX_apply]
  unfold Loc.eN
  by_cases hm : m.1 < n
  · rw [dif_pos hm]
    by_cases he : (⟨m.1, hm⟩ : Fin n) = l
    · rw [he, Pi.single_eq_same, if_pos (by rw [← he])]
    · rw [Pi.single_eq_of_ne he, if_neg (fun h => he (Fin.ext h))]
  · rw [dif_neg hm, if_neg (by omega)]

theorem ciGrp_mem (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {k₀ r0 t n c a : ℕ} {bl : List ℕ}
    (hfr : c = 0 ∨ k₀ = n) (hr0 : r0 ≤ n + c) (hsa : ∀ s, s < r0 → s < n → s < a)
    (hst : ∀ i, r0 + i * t ≤ a ∨ n ≤ r0 + i * t) (hbar : GL (Fin n) (𝓞 E ⧸ P.asIdeal))
    (hh : hbar ∈ uniUT n (𝓞 E ⧸ P.asIdeal) a bl) :
    ∃ g ∈ Loc.prX (Loc.Cbe (LocE.JG P q k₀ r0 t n c) 1), ∀ x ∈ stdAt E n P, redV P (g x) = hbar.1.mulVec (redV P x) := by
  have hq0 := ciQ_ne_zero hu
  set G := ciLiftM P hbar.1 with hGdef
  have hdet : IsUnit G.det := isUnit_iff_ne_zero.2 (ciLiftM_det_ne hbar)
  have hG1 : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hdet
  have hG2 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hdet
  have hE1 : ciExtM c G * ciExtM c G⁻¹ = 1 := by rw [← ciExtM_mul, hG1, ciExtM_one]
  have hE2 : ciExtM c G⁻¹ * ciExtM c G = 1 := by rw [← ciExtM_mul, hG2, ciExtM_one]
  have hbt : (hbar.1 : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)).BlockTriangular (fun i => fine a bl i.1) := hh.1
  have hdiag : ∀ i : Fin n, i.1 < a → (hbar.1 : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) i i = 1 := hh.2
  have hGt : G.BlockTriangular (fun i => fine a bl i.1) := ciLiftM_blockTriangular hbt
  have : Invertible G := Matrix.invertibleOfIsUnitDet G hdet
  have hGit : G⁻¹.BlockTriangular (fun i => fine a bl i.1) := Matrix.blockTriangular_inv_of_blockTriangular hGt
  have hGi : ∀ i j, IntAt P (G i j) := ciLiftM_int _
  have hGii : ∀ i j, IntAt P (G⁻¹ i j) := ciLiftM_inv_int hbar
  have hsX : ∀ s, s < r0 ∨ (∃ i, s = r0 + i * t) → s ≤ a ∨ n ≤ s := by
    rintro s (hs | ⟨i, rfl⟩)
    · by_cases hsn : s < n
      · exact Or.inl (hsa s hs hsn).le
      · exact Or.inr (by omega)
    · exact hst i
  have hstab : ∀ s, s < r0 ∨ (∃ i, s = r0 + i * t) →
      ciEquiv (ciExtM c G) (ciExtM c G⁻¹) hE1 hE2 ∈ stabL E (n + c) (LocE.flagG P q k₀ n c s) := by
    intro s hs
    refine ciEquiv_stab (fun v hv => ?_) (fun v hv => ?_)
    · unfold LocE.flagG at hv ⊢
      exact ciExtM_maps hq0 G _ (ciHe_flag hfr G hGi hGt (hsX s hs)) v hv
    · unfold LocE.flagG at hv ⊢
      exact ciExtM_maps hq0 G⁻¹ _ (ciHe_flag hfr G⁻¹ hGii hGit (hsX s hs)) v hv
  refine ⟨ciEquiv G G⁻¹ hG1 hG2, ⟨ciEquiv (ciExtM c G) (ciExtM c G⁻¹) hE1 hE2, ⟨extended_matrix_in_reduction G G⁻¹ hE1 hE2, ?_⟩, fun x => ?_⟩,
    fun x hx => ?_⟩
  · simp only [inv_one]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · show _ ∈ stabL E (n + c) (LocE.sclLat P q (n + c) (LocE.scE n fun i => i + 1))
      have he : ∀ (A : Matrix (Fin n) (Fin n) E), (∀ i j, IntAt P (A i j)) → ∀ l l' : Fin n,
          IntAt P (A l l' * (q : E) ^ (LocE.scE n (fun i => i + 1) l'.1 - LocE.scE n (fun i => i + 1) l.1)) := by
        intro A hA l l'
        rw [ciScE_lt _ l.2, ciScE_lt _ l'.2, sub_self, zpow_zero, mul_one]
        exact hA _ _
      exact ciEquiv_stab (fun v hv => ciExtM_maps hq0 G _ (he G hGi) v hv) (fun v hv => ciExtM_maps hq0 G⁻¹ _ (he G⁻¹ hGii) v hv)
    · refine ⟨fun s hs => hstab s (Or.inr hs), fun s hs => ⟨hstab s (Or.inl hs), ?_⟩⟩
      by_cases hsn : s < n
      · have hb := ciBvecG (E := E) (q := q) (k₀ := k₀) (c := c) hfr ⟨s, hsn⟩
        simp only at hb
        rw [hb, ciEquiv_apply, ciExtM_inX, ← map_sub, ciMem_flagG]
        intro m
        refine Fin.addCases (fun l => ?_) (fun j => ?_) m
        · rw [ciInX_castAdd, Fin.val_castAdd, ciScE_lt _ l.2, ciFPos hfr (show l.1 < n + c by omega), zero_add]
          have hv : ((G.mulVec (Pi.single (⟨s, hsn⟩ : Fin n) (1 : E)) - Pi.single (⟨s, hsn⟩ : Fin n) (1 : E) : Fin n → E) l) =
              G l ⟨s, hsn⟩ - (Pi.single (⟨s, hsn⟩ : Fin n) (1 : E) : Fin n → E) l := by
            simp [Pi.single_apply]
          rw [hv]
          by_cases hsl : s ≤ l.1
          · rcases Nat.eq_or_lt_of_le hsl with h | h
            · have hl : l = ⟨s, hsn⟩ := Fin.ext h.symm
              subst hl
              rw [Pi.single_eq_same, hGdef, ciLiftM_apply, hdiag _ (hsa s hs hsn), ciLift_one, map_one, sub_self, mul_zero]
              exact ciIntAt_zero
            · have hl : l ≠ ⟨s, hsn⟩ := fun h' => by rw [h'] at h; simp at h
              rw [ciFine_zero hGt (show (⟨s, hsn⟩ : Fin n).1 < a from hsa s hs hsn) h, Pi.single_eq_of_ne hl, sub_zero, mul_zero]
              exact ciIntAt_zero
          · rw [if_neg hsl, zpow_zero, inv_one, one_mul]
            by_cases hl : l = ⟨s, hsn⟩
            · rw [hl, Pi.single_eq_same]; exact ciIntAt_sub (hGi _ _) ciIntAt_one
            · rw [Pi.single_eq_of_ne hl, sub_zero]; exact hGi _ _
        · rw [ciInX_apply, dif_neg (by simp), mul_zero]
          exact ciIntAt_zero
      · have hfix : ciEquiv (ciExtM c G) (ciExtM c G⁻¹) hE1 hE2 (LocE.bvecG E q k₀ n c s) = LocE.bvecG E q k₀ n c s := by
          rw [ciEquiv_apply, ciExtM_fix]
          intro l
          unfold LocE.bvecG Loc.eN
          rw [ciFIdx hfr (show s < n + c by omega), Pi.smul_apply, if_neg (by simp; omega), smul_zero]
        rw [hfix, sub_self]
        exact zero_mem _
  · rw [ciEquiv_apply, ciEquiv_apply, ciExtM_inX]
  · funext l
    have hx' := (ciMem_stdAt P x).1 hx
    simp only [redV, ciEquiv_apply, Matrix.mulVec, dotProduct]
    rw [redP_sum _ _ (fun l' _ => (hGi _ _).mul (hx' _))]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [reduction_mul (hGi _ _) (hx' _), ciLiftM_red]

end Mem2

section Of

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ciEN {n c p : ℕ} (hp : p < n) : Loc.eN E (n + c) p = Loc.inX E n c (Pi.single ⟨p, hp⟩ 1) := by
  funext l
  rw [ciInX_apply]
  simp only [Loc.eN]
  split_ifs <;> first | omega | rfl | simp_all [Pi.single_apply, Fin.ext_iff]

theorem ciAtN_inX {n c p : ℕ} (hp : p < n) (v : Fin n → E) : Loc.atN (Loc.inX E n c v) p = v ⟨p, hp⟩ := by
  simp [Loc.atN, ciInX_apply, hp, show p < n + c by omega]

theorem ciRedV_single {n : ℕ} (l : Fin n) : redV P (Pi.single l (1 : E)) = Pi.single l 1 := by
  funext i
  simp only [redV]
  by_cases h : i = l
  · subst h
    simp [redP_one]
  · simp [Pi.single_eq_of_ne h, redP_zero]

theorem ciSingle_mem {n : ℕ} (l : Fin n) : (Pi.single l (1 : E) : Sp E n) ∈ stdAt E n P := by
  rw [ciMem_stdAt]
  intro i
  by_cases h : i = l
  · subst h
    simpa using (ciIntAt_one : IntAt P (1 : E))
  · simpa [Pi.single_eq_of_ne h] using (ciIntAt_zero : IntAt P (0 : E))

theorem ciEntry {n : ℕ} {g : Sp E n ≃ₗ[E] Sp E n} {hbar : GL (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (hred : ∀ x ∈ stdAt E n P, redV P (g x) = hbar.1.mulVec (redV P x)) (l l' : Fin n) :
    (hbar.1 : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) l l' = redP P (g (Pi.single l' 1) l) := by
  have h := congrFun (hred _ (ciSingle_mem l')) l
  rw [ciRedV_single] at h
  simp only [redV] at h
  rw [h]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem ciJG_of_Cbe {k₀ r0 t n c : ℕ} {r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hr : r ∈ Loc.Cbe (LocE.JG P q k₀ r0 t n c) 1) :
    r ∈ LocE.JG P q k₀ r0 t n c := by
  have := hr.2
  simpa [MulAut.conj_apply] using this

theorem ciInt_of_prX {k₀ r0 t n c : ℕ} {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ Loc.prX (Loc.Cbe (LocE.JG P q k₀ r0 t n c) 1))
    (l l' : Fin n) : IntAt P (g (Pi.single l' 1) l) := by
  have h1 := ((ciPrX_le (P := P) (q := q) (k₀ := k₀) (r0 := r0) (t := t) (c := c) hg) _).2 (ciSingle_mem (P := P) l')
  exact (ciMem_stdAt P _).1 h1 l

theorem ciGrp_of (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {k₀ r0 t n c a : ℕ} {bl : List ℕ}
    (hfr : c = 0 ∨ k₀ = n) (ha : a ≤ r0)
    (hblk : ∀ i j : Fin n, coarse a bl j.1 < coarse a bl i.1 → ∃ s, (s < r0 ∨ ∃ i', s = r0 + i' * t) ∧ j.1 < s ∧ s ≤ i.1)
    (hbar : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ Loc.prX (Loc.Cbe (LocE.JG P q k₀ r0 t n c) 1))
    (hred : ∀ x ∈ stdAt E n P, redV P (g x) = hbar.1.mulVec (redV P x)) : hbar ∈ uniUT n (𝓞 E ⧸ P.asIdeal) a bl := by
  obtain ⟨r, hr, hrg⟩ := hg
  have hJ := ciJG_of_Cbe hr
  have hgi := ciInt_of_prX ⟨r, hr, hrg⟩
  rw [mem_uniUT]
  refine ⟨fun i j hij => ?_, fun i j hi hji => ?_, fun i hi => ?_⟩
  · obtain ⟨s, hs, h1, h2⟩ := hblk i j hij
    rw [ciEntry hred]
    exact ciJG_entry hq hq0 hfr hJ hrg hs h1 h2
  · rw [ciEntry hred]
    exact ciJG_entry hq hq0 hfr hJ hrg (s := j.1 + 1) (Or.inl (by omega)) (by omega) (by omega)
  · rw [ciEntry hred]
    exact ciJG_diag hq hq0 hfr hJ hrg hgi (by omega)

theorem ciEntB_X {k₀ n c : ℕ} (hfr : c = 0 ∨ k₀ = n) (ex ex' : ℕ → ℕ) {r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} {g : Sp E n ≃ₗ[E] Sp E n}
    (hrg : ∀ x, r (Loc.inX E n c x) = Loc.inX E n c (g x)) {p p' : ℕ} (hp : p < n) (hp' : p' < n) :
    LocE.entB q k₀ c n c n ex' ex r.toLinearMap p p' = g (Pi.single ⟨p', hp'⟩ 1) ⟨p, hp⟩ := by
  unfold LocE.entB
  rw [ciFIdx hfr (show p < n + c by omega), ciFIdx hfr (show p' < n + c by omega), ciScE_lt _ hp, ciScE_lt _ hp', sub_self,
    zpow_zero, mul_one, ciEN hp', LinearEquiv.coe_coe, hrg, ciAtN_inX hp]

theorem entry_block_vanishing {k₀ n c : ℕ} (hfr : c = 0 ∨ k₀ = n) (ex ex' : ℕ → ℕ) {r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hr : r ∈ Loc.R1 E n c) {p : ℕ} (hp : p < n) (hc : 1 ≤ c) :
    LocE.entB q k₀ c n c n ex' ex r.toLinearMap p n = 0 := by
  unfold LocE.entB
  rw [ciFIdx hfr (show p < n + c by omega), ciFIdx hfr (show n < n + c by omega), LinearEquiv.coe_coe, hr.1.2.1]
  unfold Loc.atN Loc.eN
  rw [dif_pos (by omega)]
  simp only
  rw [if_neg (by omega), zero_mul]

end Of

section Lev

variable {X : Fields} {Pr : Primes X} (Ch : Chars X Pr Examples₂.R0.m)

theorem ciJat (j : ℕ) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) :
    Jat (Pr := Pr) (R := Examples₂.R0) false j w = LocE.JG w (qOf w) Examples₂.R0.k Examples₂.R0.r Examples₂.R0.t (Examples₂.R0.N j) (cOf Examples₂.R0 j) := by
  unfold Jat
  rw [if_pos hw]
  rfl

theorem first_level_reduction_group (hX : X.Ok) (hPr : Pr.Ok) (w : Pr.vGs) (hbar : GL (Fin (Examples₂.R0.N 0)) (𝓞 X.E ⧸ w.1.asIdeal)) :
    hbar ∈ (colLev Ch 0 w).H ↔ ∃ g ∈ prCat (Pr := Pr) (R := Examples₂.R0) false 0 w.1 1,
      ∀ x ∈ stdAt X.E (Examples₂.R0.N 0) w.1, redV w.1 (g x) = hbar.1.mulVec (redV w.1 x) := by
  have hq := ciQ_mem (E := X.E) w.1
  have hu := ciQ_notMem_sq hX hPr w.2
  have hq0 := ciQ_ne_zero hu
  unfold prCat
  rw [ciJat 0 w.2]
  change hbar ∈ uniUT (Examples₂.R0.N 0) (𝓞 X.E ⧸ w.1.asIdeal) (Examples₂.R0.k + 0) (List.replicate 0 Examples₂.R0.t) ↔ _
  constructor
  · intro hh
    exact ciGrp_mem hu (Or.inr rfl) (by decide) (fun s h1 h2 => by simp [Examples₂.exampleRanks_N_formula] at h2 ⊢; omega)
      (fun i => Or.inr (by simp [Examples₂.exampleRanks_N_formula]; omega)) hbar hh
  · rintro ⟨g, hg, hred⟩
    refine ciGrp_of hq hq0 (Or.inr rfl) (by decide) (fun i j h => ?_) hbar hg hred
    have hi := i.2
    have hj := j.2
    simp only [Examples₂.exampleRanks_N_formula] at hi hj
    simp [coarse, blkIdx, hi, hj] at h

theorem second_level_reduction_group (hX : X.Ok) (hPr : Pr.Ok) (w : Pr.vGs) (hbar : GL (Fin (Examples₂.R0.N 1)) (𝓞 X.E ⧸ w.1.asIdeal)) :
    hbar ∈ (colLev Ch 1 w).H ↔ ∃ g ∈ prCat (Pr := Pr) (R := Examples₂.R0) false 1 w.1 1,
      ∀ x ∈ stdAt X.E (Examples₂.R0.N 1) w.1, redV w.1 (g x) = hbar.1.mulVec (redV w.1 x) := by
  have hq := ciQ_mem (E := X.E) w.1
  have hu := ciQ_notMem_sq hX hPr w.2
  have hq0 := ciQ_ne_zero hu
  unfold prCat
  rw [ciJat 1 w.2]
  change hbar ∈ uniUT (Examples₂.R0.N 1) (𝓞 X.E ⧸ w.1.asIdeal) (Examples₂.R0.k + 1) (List.replicate 1 Examples₂.R0.t) ↔ _
  constructor
  · intro hh
    exact ciGrp_mem hu (Or.inl rfl) (by decide) (fun s h1 h2 => by simp [Examples₂.exampleRanks_N_formula] at h1 h2 ⊢; omega)
      (fun i => by simp [Examples₂.exampleRanks_N_formula]; omega) hbar hh
  · rintro ⟨g, hg, hred⟩
    refine ciGrp_of hq hq0 (Or.inl rfl) (by decide) (fun i j h => ?_) hbar hg hred
    have hi := i.2
    have hj := j.2
    simp only [Examples₂.exampleRanks_N_formula] at hi hj
    refine ⟨Examples₂.R0.r, Or.inr ⟨0, by simp⟩, ?_, ?_⟩
    · simp only [coarse, blkIdx, List.replicate] at h
      split_ifs at h <;> simp_all <;> omega
    · simp only [coarse, blkIdx, List.replicate] at h
      split_ifs at h <;> simp_all <;> omega

end Lev

section Chr

theorem ciSupSum {κ : Type} [CommRing κ] {n a : ℕ} {S : Finset ℕ} (M : Matrix (Fin n) (Fin n) κ) :
    supSum a S M = ∑ i ∈ Finset.range n,
      if h : i + 1 < n ∧ i + 1 < a ∧ i ∈ S then M ⟨i, by omega⟩ ⟨i + 1, h.1⟩ else 0 := by
  unfold supSum
  rw [← Fin.sum_univ_eq_sum_range (fun i => if h : i + 1 < n ∧ i + 1 < a ∧ i ∈ S then M ⟨i, by omega⟩ ⟨i + 1, h.1⟩ else 0) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i.1 + 1 < n ∧ i.1 + 1 < a ∧ i.1 ∈ S
  · rw [dif_pos h, Finset.sum_eq_single (⟨i.1 + 1, h.1⟩ : Fin n)]
    · rw [if_pos ⟨rfl, h.2.1, h.2.2⟩]
    · intro j _ hj
      rw [if_neg]
      intro hc
      exact hj (Fin.ext hc.1.symm)
    · intro hc
      exact absurd (Finset.mem_univ _) hc
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2, h3⟩
    exact h ⟨by rw [h1]; exact j.2, by rw [h1]; exact h2, h3⟩

variable {X : Fields} {Pr : Primes X} (Ch : Chars X Pr Examples₂.R0.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  {mq : ℕ → rowSG Pr sel (mu0 X.F X.E X.K S) → X.K}

theorem ciPsi_zero {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (P : SB) : ciPsi Ch P 0 = 1 := by
  unfold ciPsi
  rw [mul_zero, if_pos ciIntAt_zero, redP_zero]
  first
  | exact AddChar.map_zero_eq_one _
  | simp

theorem ciPsi0P (w : Pr.vGs) : psi0P Ch w.1 = Ch.psi0 w := by
  unfold psi0P
  rw [dif_pos w.2]

theorem ciChiP (w : Pr.vGs) : chiP Ch w.1 = extChi fun s => Ch.chi s w := by
  unfold chiP
  rw [dif_pos w.2]
  rfl

theorem character_first_level_group (hX : X.Ok) (hPr : Pr.Ok) (w : Pr.vGs) (hw : w.1 ∈ rowSG Pr sel (mu0 X.F X.E X.K S))
    (hbar : ↥(colLev Ch 0 w).H) (g : Sp X.E (Examples₂.R0.N 0) ≃ₗ[X.E] Sp X.E (Examples₂.R0.N 0))
    (r : AutY X Examples₂.R0 0) (hr : r ∈ Loc.Cbe (Jat (Pr := Pr) (R := Examples₂.R0) false 0 w.1) 1)
    (hrg : ∀ x, r (Loc.inX X.E (Examples₂.R0.N 0) (cOf Examples₂.R0 0) x) = Loc.inX X.E (Examples₂.R0.N 0) (cOf Examples₂.R0 0) (g x))
    (hred : ∀ x ∈ stdAt X.E (Examples₂.R0.N 0) w.1, redV w.1 (g x) = hbar.1.1.mulVec (redV w.1 x)) :
    ((((colLev Ch 0 w).lam hbar : X.Kˣ) : X.K)) =
      chiInv Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 ⟨w.1, hw⟩ 1 r := by
  have hq := ciQ_mem (E := X.E) w.1
  have hu := ciQ_notMem_sq hX hPr w.2
  have hq0 := ciQ_ne_zero hu
  rw [ciJat 0 w.2] at hr
  have hJ := ciJG_of_Cbe hr
  have hgi := ciInt_of_prX ⟨r, hr, hrg⟩
  have hfr0 : cOf Examples₂.R0 0 = 0 ∨ Examples₂.R0.k = Examples₂.R0.N 0 := Or.inr rfl
  unfold chiInv
  have hn1 : Loc.n1Arg r = 0 := by
    unfold Loc.n1Arg
    rw [show cOf Examples₂.R0 0 - 1 = 0 from rfl, Finset.range_zero, Finset.sum_empty]
  rw [hn1]
  show _ = (ciPsi Ch _ 0)⁻¹ * _
  rw [ciPsi_zero, inv_one, one_mul, inv_one, one_mul, mul_one]
  unfold lamRow
  rw [if_pos w.2]
  unfold LocE.lamGB LocE.lamGv
  rw [ciPsi0P, Finset.range_zero, Finset.prod_empty, mul_one]
  have e1 : (((colLev Ch 0 w).lam hbar : X.Kˣ) : X.K) =
      ((lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (Examples₂.R0.N 0) Examples₂.R0.k Examples₂.R0.m Examples₂.R0.t 0 ⟨hbar.1, hbar.2⟩ : X.Kˣ) : X.K) := rfl
  rw [e1]
  unfold lamX lamGen
  rw [MonoidHom.mul_apply, Units.val_mul, supChar_val, MonoidHom.comp_apply, detChar_apply]
  simp only [List.replicate, List.length_nil, Finset.range_zero, Finset.prod_empty, Units.val_one, mul_one]
  congr 1
  rw [ciSupSum]
  have hint : ∀ i ∈ Finset.range (Examples₂.R0.r - 1), IntAt w.1 (LocE.entB (qOf w.1) Examples₂.R0.k (cOf Examples₂.R0 0) (Examples₂.R0.N 0)
      (cOf Examples₂.R0 0) (Examples₂.R0.N 0) (fun i => i + 1) (fun i => i + 1) r.toLinearMap i (i + 1)) := by
    intro i hi
    simp only [Finset.mem_range, show Examples₂.R0.r - 1 = 8 from rfl] at hi
    by_cases h7 : i < 7
    · rw [ciEntB_X hfr0 _ _ hrg (show i < Examples₂.R0.N 0 by simp [Examples₂.exampleRanks_N_formula]; omega) (show i + 1 < Examples₂.R0.N 0 by simp [Examples₂.exampleRanks_N_formula]; omega)]
      exact hgi _ _
    · rw [show i = Examples₂.R0.N 0 - 1 by simp [Examples₂.exampleRanks_N_formula]; omega, show Examples₂.R0.N 0 - 1 + 1 = Examples₂.R0.N 0 from rfl,
        entry_block_vanishing hfr0 _ _ hr.1 (by simp [Examples₂.exampleRanks_N_formula]) (by decide)]
      exact ciIntAt_zero
  rw [redP_sum _ _ hint, show Examples₂.R0.r - 1 = Examples₂.R0.N 0 from rfl]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_range, Examples₂.exampleRanks_N_formula] at hi
  by_cases h7 : i < 7
  · rw [dif_pos ⟨by simp [Examples₂.exampleRanks_N_formula]; omega, by simp; omega, by simp [SX]; omega⟩,
      ciEntB_X hfr0 _ _ hrg (show i < Examples₂.R0.N 0 by simp [Examples₂.exampleRanks_N_formula]; omega) (show i + 1 < Examples₂.R0.N 0 by simp [Examples₂.exampleRanks_N_formula]; omega)]
    exact ciEntry hred _ _
  · rw [dif_neg (by simp [Examples₂.exampleRanks_N_formula]; omega), show i = Examples₂.R0.N 0 - 1 by simp [Examples₂.exampleRanks_N_formula]; omega,
      show Examples₂.R0.N 0 - 1 + 1 = Examples₂.R0.N 0 from rfl, entry_block_vanishing hfr0 _ _ hr.1 (by simp [Examples₂.exampleRanks_N_formula]) (by decide), redP_zero]

end Chr

section Chr1

variable {X : Fields} {Pr : Primes X} (Ch : Chars X Pr Examples₂.R0.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  {mq : ℕ → rowSG Pr sel (mu0 X.F X.E X.K S) → X.K}

theorem ciCoarse1 (x : ℕ) : coarse 9 [15] x = 1 ↔ 9 ≤ x ∧ x < 24 := by
  unfold coarse
  simp only [blkIdx]
  by_cases h1 : x < 9 <;> by_cases h2 : x - 9 < 15 <;> simp [h1, h2] <;> omega

def secondBlockIndexEquiv : Fin 15 ≃ {i : Fin 24 // coarse 9 [15] i.1 = 1} where
  toFun s := ⟨⟨9 + s.1, by have := s.2; omega⟩, (ciCoarse1 (9 + s.1)).2 ⟨by omega, by have := s.2; omega⟩⟩
  invFun i := ⟨i.1.1 - 9, by have := (ciCoarse1 _).1 i.2; omega⟩
  left_inv s := by ext; simp
  right_inv i := by
    have := (ciCoarse1 _).1 i.2
    ext
    simp
    omega

theorem character_second_level_group (hX : X.Ok) (hPr : Pr.Ok) (w : Pr.vGs) (hw : w.1 ∈ rowSG Pr sel (mu0 X.F X.E X.K S))
    (hbar : ↥(colLev Ch 1 w).H) (g : Sp X.E (Examples₂.R0.N 1) ≃ₗ[X.E] Sp X.E (Examples₂.R0.N 1))
    (r : AutY X Examples₂.R0 1) (hr : r ∈ Loc.Cbe (Jat (Pr := Pr) (R := Examples₂.R0) false 1 w.1) 1)
    (hrg : ∀ x, r (Loc.inX X.E (Examples₂.R0.N 1) (cOf Examples₂.R0 1) x) = Loc.inX X.E (Examples₂.R0.N 1) (cOf Examples₂.R0 1) (g x))
    (hred : ∀ x ∈ stdAt X.E (Examples₂.R0.N 1) w.1, redV w.1 (g x) = hbar.1.1.mulVec (redV w.1 x)) :
    ((((colLev Ch 1 w).lam hbar : X.Kˣ) : X.K)) =
      chiInv Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 1 ⟨w.1, hw⟩ 1 r := by
  have hu := ciQ_notMem_sq hX hPr w.2
  rw [ciJat 1 w.2] at hr
  have hgi := ciInt_of_prX ⟨r, hr, hrg⟩
  have hfr1 : cOf Examples₂.R0 1 = 0 ∨ Examples₂.R0.k = Examples₂.R0.N 1 := Or.inl rfl
  unfold chiInv
  have hn1 : Loc.n1Arg r = 0 := by
    unfold Loc.n1Arg
    rw [show cOf Examples₂.R0 1 - 1 = 0 from rfl, Finset.range_zero, Finset.sum_empty]
  rw [hn1]
  show _ = (ciPsi Ch _ 0)⁻¹ * _
  rw [ciPsi_zero, inv_one, one_mul, inv_one, one_mul, mul_one]
  unfold lamRow
  rw [if_pos w.2]
  unfold LocE.lamGB LocE.lamGv
  rw [ciPsi0P, ciChiP]
  have e1 : (((colLev Ch 1 w).lam hbar : X.Kˣ) : X.K) =
      ((lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (Examples₂.R0.N 1) Examples₂.R0.k Examples₂.R0.m Examples₂.R0.t 1 ⟨hbar.1, hbar.2⟩ : X.Kˣ) : X.K) := rfl
  rw [e1]
  unfold lamX lamGen
  rw [MonoidHom.mul_apply, Units.val_mul, supChar_val, MonoidHom.comp_apply, detChar_apply]
  have hM : ∀ p p' : ℕ, ∀ (hp : p < 24) (hp' : p' < 24), LocE.entB (qOf w.1) Examples₂.R0.k (cOf Examples₂.R0 1) (Examples₂.R0.N 1) (cOf Examples₂.R0 1)
      (Examples₂.R0.N 1) (fun i => i + 1) (fun i => i + 1) r.toLinearMap p p' = g (Pi.single ⟨p', hp'⟩ 1) ⟨p, hp⟩ :=
    fun p p' hp hp' => ciEntB_X hfr1 _ _ hrg hp hp'
  congr 1
  ·
    rw [ciSupSum]
    have hint : ∀ i ∈ Finset.range (Examples₂.R0.r - 1), IntAt w.1 (LocE.entB (qOf w.1) Examples₂.R0.k (cOf Examples₂.R0 1) (Examples₂.R0.N 1)
        (cOf Examples₂.R0 1) (Examples₂.R0.N 1) (fun i => i + 1) (fun i => i + 1) r.toLinearMap i (i + 1)) := by
      intro i hi
      simp only [Finset.mem_range, show Examples₂.R0.r - 1 = 8 from rfl] at hi
      rw [hM i (i + 1) (by omega) (by omega)]
      exact hgi _ _
    rw [redP_sum _ _ hint, ← Finset.sum_range_add_sum_Ico _ (show Examples₂.R0.r - 1 ≤ Examples₂.R0.N 1 by decide)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (Examples₂.R0.r - 1) (Examples₂.R0.N 1)) (fun i hi => by
      simp only [Finset.mem_Ico, show Examples₂.R0.r - 1 = 8 from rfl] at hi
      rw [dif_neg (by simp; omega)]), add_zero]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range, show Examples₂.R0.r - 1 = 8 from rfl] at hi
    rw [dif_pos ⟨by simp [Examples₂.exampleRanks_N_formula]; omega, by simp; omega, by simp [SX]; omega⟩, hM i (i + 1) (by omega) (by omega)]
    exact ciEntry hred _ _
  ·
    simp only [List.replicate, List.length_singleton, Finset.range_one, Finset.prod_singleton, zero_mul, add_zero]
    set D : Matrix (Fin Examples₂.R0.t) (Fin Examples₂.R0.t) X.E := Matrix.of fun s s' : Fin Examples₂.R0.t =>
      LocE.entB (qOf w.1) Examples₂.R0.k (cOf Examples₂.R0 1) (Examples₂.R0.N 1) (cOf Examples₂.R0 1) (Examples₂.R0.N 1) (fun i => i + 1) (fun i => i + 1)
        r.toLinearMap (Examples₂.R0.r + s.1) (Examples₂.R0.r + s'.1) with hD
    have hDint : ∀ s s', IntAt w.1 (D s s') := by
      intro s s'
      rw [hD, Matrix.of_apply, hM _ _ (by have := s.2; simp at this ⊢; omega) (by have := s'.2; simp at this ⊢; omega)]
      exact hgi _ _
    have hmem : (hbar.1 : GL (Fin (Examples₂.R0.N 1)) (𝓞 X.E ⧸ w.1.asIdeal)) ∈
        uniUT (Examples₂.R0.N 1) (𝓞 X.E ⧸ w.1.asIdeal) (Examples₂.R0.k + 1) (List.replicate 1 Examples₂.R0.t) := hbar.2
    have hdet : redP w.1 D.det = ((blkDet (Examples₂.R0.N 1) (𝓞 X.E ⧸ w.1.asIdeal) (coarse (Examples₂.R0.k + 1) (List.replicate 1 Examples₂.R0.t)) 1
        ⟨hbar.1, uniUT_le_blockUT _ _ _ _ hmem⟩ : (𝓞 X.E ⧸ w.1.asIdeal)ˣ) : 𝓞 X.E ⧸ w.1.asIdeal) := by
      rw [redP_det D hDint, blkDet_val]
      refine Eq.trans ?_ (Matrix.det_submatrix_equiv_self secondBlockIndexEquiv _)
      congr 1
      ext s s'
      simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.toSquareBlock_def, Matrix.of_apply, hD]
      rw [hM _ _ (by have := s.2; simp at this ⊢; omega) (by have := s'.2; simp at this ⊢; omega), ← ciEntry hred]
      rfl
    have hU : IsUnit (redP w.1 D.det) := by rw [hdet]; exact Units.isUnit _
    unfold LocE.unitV
    rw [dif_pos hU]
    congr 2
    exact Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)

end Chr1

section Phi

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ciOm_one {a b : ℕ} (mu : E → K) (v : E → ℤ) (sq : K) (Φ : Loc.SF E K a b) (x : (Fin a → E) →ₗ[E] (Fin b → E)) :
    Loc.om mu v sq (1 : (Fin a → E) ≃ₗ[E] (Fin a → E)) (1 : (Fin b → E) ≃ₗ[E] (Fin b → E)) Φ x =
      (mu 1 * (mu 1)⁻¹ * sq ^ (-(v 1) * b) * sq ^ (v 1 * a)) * Φ x := by
  unfold Loc.om
  have e : ((1 : (Fin b → E) ≃ₗ[E] (Fin b → E)).symm.toLinearMap ∘ₗ x ∘ₗ (1 : (Fin a → E) ≃ₗ[E] (Fin a → E)).toLinearMap) = x :=
    LinearMap.ext fun _ => rfl
  rw [e, map_one, map_one, Units.val_one]

theorem ciUnitV_congr (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a a' : E} (h : redP P a' = redP P a) :
    LocE.unitV χ a' = LocE.unitV χ a := by
  unfold LocE.unitV
  by_cases hu : IsUnit (redP P a)
  · rw [dif_pos hu, dif_pos (h ▸ hu)]
    congr 2
    exact Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h])
  · rw [dif_neg hu, dif_neg (fun h' => hu (h ▸ h'))]

theorem ciLamGv_congr (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {r t j a : ℕ} (M M' : ℕ → ℕ → E)
    (hr : r - 1 < a) (hja : r + j * t ≤ a)
    (h : ∀ p p', p < a → p' < a → IntAt P (M p p') ∧ IntAt P (M' p p') ∧ redP P (M' p p') = redP P (M p p')) :
    LocE.lamGv ψ₀ χ r t j M' = LocE.lamGv ψ₀ χ r t j M := by
  unfold LocE.lamGv
  congr 1
  · congr 1
    have hb : ∀ i ∈ Finset.range (r - 1), i < a ∧ i + 1 < a := fun i hi => by simp at hi; omega
    rw [redP_sum _ _ (fun i hi => (h i (i + 1) (hb i hi).1 (hb i hi).2).2.1),
      redP_sum _ _ (fun i hi => (h i (i + 1) (hb i hi).1 (hb i hi).2).1)]
    exact Finset.sum_congr rfl fun i hi => (h i (i + 1) (hb i hi).1 (hb i hi).2).2.2
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < j := by simpa using hi
    have hb : ∀ s : Fin t, r + i * t + s.1 < a := fun s => by
      have h1 := s.2
      have h2 : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right _ hi'
      nlinarith
    apply ciUnitV_congr
    rw [redP_det (Matrix.of fun s s' : Fin t => M' (r + i * t + s.1) (r + i * t + s'.1)) (fun s s' => (h _ _ (hb s) (hb s')).2.1),
      redP_det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1)) (fun s s' => (h _ _ (hb s) (hb s')).1)]
    congr 1
    ext s s'
    exact (h _ _ (hb s) (hb s')).2.2

variable (P) in

def ciPhiCond (q : ℕ) (sharp : Bool) (k₀ r t j c n : ℕ) (M : ℕ → ℕ → E) : Prop :=
  (∀ p p', p < n + c → p' < r + (j - 1) * t → IntAt P (M p p')) ∧
    (∀ p p', r + (j - 1) * t ≤ p → p < n + c → p' < r + (j - 1) * t → IntAt P (M p p' / (q : E))) ∧
    (∀ p', p' < r → redP P (M p' p') = 1 ∧ ∀ p, p' < p → p < r + (j - 1) * t → redP P (M p p') = 0) ∧
    (∀ p p', r ≤ p' → p' < r + (j - 1) * t → p < r + (j - 1) * t → (p' - r) / t < (p - r) / t → redP P (M p p') = 0) ∧
    (sharp = true → ∀ p, p < n + c → redP P (M p k₀) = if p = k₀ then 1 else 0)

open Classical in
theorem ciPhiG_eq (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (sharp : Bool)
    (k₀ r t j c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) :
    LocE.PhiG (P := P) q ψ₀ χ sharp k₀ r t j c' n' c n x =
      if ciPhiCond P q sharp k₀ r t j c n (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x) then
        LocE.lamGv ψ₀ χ r t (j - 1) (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x) *
          (LocE.unitV (χ (j - 1)) (Matrix.det (Matrix.of fun s s' : Fin (r + (j - 1) * t) =>
            LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x s.1 s'.1)))⁻¹
      else 0 := by
  unfold LocE.PhiG ciPhiCond
  dsimp only
  split_ifs <;> rfl

open Classical in

theorem ciPhiG_congr (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (sharp : Bool) {k₀ r t j c' n' c n : ℕ} (x x' : HomE E (n' + c') (n + c))
    (hk : k₀ < r + (j - 1) * t) (hr1 : 1 ≤ r) (hra : r ≤ r + (j - 1) * t) (han : r + (j - 1) * t ≤ n + c)
    (hD : ∀ p p', p < n + c → p' < r + (j - 1) * t → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p' + q * d) :
    LocE.PhiG (P := P) q ψ₀ χ sharp k₀ r t j c' n' c n x' = LocE.PhiG (P := P) q ψ₀ χ sharp k₀ r t j c' n' c n x := by
  rw [ciPhiG_eq, ciPhiG_eq]
  set M := LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x with hM
  set M' := LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' with hM'
  set a := r + (j - 1) * t with ha
  have k1 : ∀ p p', p < n + c → p' < a → (IntAt P (M' p p') ↔ IntAt P (M p p')) := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he]
    exact ciIntAt_add_iff ((ciIntAt_q (q := q)).mul hd)
  have k2 : ∀ p p', p < n + c → p' < a → (IntAt P (M' p p' / q) ↔ IntAt P (M p p' / q)) := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he, add_div, mul_div_cancel_left₀ _ hq0]
    exact ciIntAt_add_iff hd
  have k3 : ∀ p p', p < n + c → p' < a → redP P (M' p p') = redP P (M p p') := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he]
    exact redP_add_natCast_mul hq hd
  have hc : ciPhiCond P q sharp k₀ r t j c n M' ↔ ciPhiCond P q sharp k₀ r t j c n M := by
    unfold ciPhiCond
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨fun p p' hp hp' => (k1 p p' hp hp').1 (h1 p p' hp hp'), fun p p' h0 hp hp' => (k2 p p' hp hp').1 (h2 p p' h0 hp hp'),
        fun p' hp' => ⟨?_, fun p hpp hp => ?_⟩, fun p p' h0 hp' hp hpp => ?_, fun hs p hp => ?_⟩
      · rw [← k3 p' p' (by omega) (by omega)]; exact (h3 p' hp').1
      · rw [← k3 p p' (by omega) (by omega)]; exact (h3 p' hp').2 p hpp hp
      · rw [← k3 p p' (by omega) hp']; exact h4 p p' h0 hp' hp hpp
      · rw [← k3 p k₀ hp hk]; exact h5 hs p hp
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨fun p p' hp hp' => (k1 p p' hp hp').2 (h1 p p' hp hp'), fun p p' h0 hp hp' => (k2 p p' hp hp').2 (h2 p p' h0 hp hp'),
        fun p' hp' => ⟨?_, fun p hpp hp => ?_⟩, fun p p' h0 hp' hp hpp => ?_, fun hs p hp => ?_⟩
      · rw [k3 p' p' (by omega) (by omega)]; exact (h3 p' hp').1
      · rw [k3 p p' (by omega) (by omega)]; exact (h3 p' hp').2 p hpp hp
      · rw [k3 p p' (by omega) hp']; exact h4 p p' h0 hp' hp hpp
      · rw [k3 p k₀ hp hk]; exact h5 hs p hp
  by_cases hC : ciPhiCond P q sharp k₀ r t j c n M
  · rw [if_pos (hc.2 hC), if_pos hC]
    have htrip : ∀ p p', p < a → p' < a → IntAt P (M p p') ∧ IntAt P (M' p p') ∧ redP P (M' p p') = redP P (M p p') :=
      fun p p' hp hp' => ⟨hC.1 p p' (by omega) hp', (hc.2 hC).1 p p' (by omega) hp', k3 p p' (by omega) hp'⟩
    congr 1
    · exact ciLamGv_congr ψ₀ χ M M' (by omega) (le_refl _) htrip
    · congr 1
      apply ciUnitV_congr
      rw [redP_det (Matrix.of fun s s' : Fin a => M' s.1 s'.1) (fun s s' => (htrip s.1 s'.1 s.2 s'.2).2.1),
        redP_det (Matrix.of fun s s' : Fin a => M s.1 s'.1) (fun s s' => (htrip s.1 s'.1 s.2 s'.2).1)]
      congr 1
      ext s s'
      exact (htrip s.1 s'.1 s.2 s'.2).2.2
  · rw [if_neg (fun h => hC (hc.1 h)), if_neg hC]

open Classical in
theorem ciPhiG_int (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (sharp : Bool)
    {k₀ r t j c' n' c n : ℕ} (x : HomE E (n' + c') (n + c)) (h : LocE.PhiG (P := P) q ψ₀ χ sharp k₀ r t j c' n' c n x ≠ 0) :
    ∀ p p', p < n + c → p' < r + (j - 1) * t →
      IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p') := by
  rw [ciPhiG_eq] at h
  by_cases hC : ciPhiCond P q sharp k₀ r t j c n (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x)
  · exact hC.1
  · rw [if_neg hC] at h
    exact absurd rfl h

theorem ciEntB_join {k₀ n' c' n c : ℕ} (hk : k₀ = n') (hc' : c' = 1) (hc : c = 0) (x₀ : HomE E n' n) (y' : Sp E n)
    {p p' : ℕ} (hp : p < n) (hp' : p' ≤ n') :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (joinCol (c' := c') (c := c) x₀ y') p p' =
      if h : p' < n' then x₀ (Pi.single ⟨p', h⟩ 1) ⟨p, hp⟩ else (q : E) * y' ⟨p, hp⟩ := by
  subst hk hc' hc
  unfold LocE.entB joinCol atNL
  rw [ciFIdx (Or.inr rfl) (show p' < k₀ + 1 by omega), ciFIdx (Or.inl rfl) (show p < n + 0 by omega), ciScE_lt _ hp,
    dif_pos (show k₀ < k₀ + 1 by omega)]
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.funLeft_apply, LinearMap.proj_apply]
  rw [ciAtN_inX hp]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : p' < k₀
  · rw [dif_pos h, ciScE_lt _ h, sub_zero, zpow_zero, mul_one]
    have e1 : (LinearMap.funLeft E E (Fin.castAdd 1)) (Loc.eN E (k₀ + 1) p') = (Pi.single ⟨p', h⟩ 1 : Fin k₀ → E) := by
      funext i
      show Loc.eN E (k₀ + 1) p' (Fin.castAdd 1 i) = _
      unfold Loc.eN
      simp only [Fin.val_castAdd]
      by_cases hi : i = ⟨p', h⟩
      · rw [hi, Pi.single_eq_same, if_pos rfl]
      · rw [Pi.single_eq_of_ne hi, if_neg (fun h' => hi (Fin.ext h'))]
    have e2 : Loc.eN E (k₀ + 1) p' ⟨k₀, by omega⟩ = 0 := by
      unfold Loc.eN
      rw [if_neg (by simp; omega)]
    rw [e1, e2, zero_mul, add_zero]
  · have hpk : p' = k₀ := by omega
    subst hpk
    rw [dif_neg (lt_irrefl _)]
    have e1 : (LinearMap.funLeft E E (Fin.castAdd 1)) (Loc.eN E (p' + 1) p') = (0 : Fin p' → E) := by
      funext i
      show Loc.eN E (p' + 1) p' (Fin.castAdd 1 i) = 0
      unfold Loc.eN
      simp only [Fin.val_castAdd]
      rw [if_neg (by have := i.2; omega)]
    have e2 : Loc.eN E (p' + 1) p' ⟨p', by omega⟩ = 1 := by
      unfold Loc.eN
      rw [if_pos rfl]
    have e3 : LocE.scE p' (fun i => i + 1) p' = 1 := by simp [LocE.scE]
    rw [e1, e2, e3, map_zero, Pi.zero_apply, zero_add, one_mul, sub_zero, zpow_one, mul_comm]

end Phi

section Inst

def ciIdx {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) : ChIdx X Pr R Q where
  β j := Fin (if j ≤ 1 then 1 else 0)
  h _ _ _ := 1
  levG j _ := colLev Ch j
  levQ j _ := LevQFam.top X.E X.K (R.N j) Q

theorem ciQE_one {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) :
    QE sel (1 : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime (1 : Chr X.F X.E X.K) = ∅ := by
    ext v
    simp [Qprime]
  unfold QE
  rw [dif_pos (by rw [h]; exact Set.finite_empty)]
  simp [h]

variable {X : Fields} {Pr : Primes X} (Ch : Chars X Pr Examples₂.R0.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  {mq : ℕ → rowSG Pr sel (mu0 X.F X.E X.K S) → X.K}

open Classical in
theorem ciRowSG : rowSG Pr sel (mu0 X.F X.E X.K S) = Pr.vGs := by
  show Pr.vGs ∪ QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) = Pr.vGs
  rw [show ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) = 1 from rfl, ciQE_one, Finset.union_empty]

theorem ciNotQ (P : HeightOneSpectrum (𝓞 X.E)) : P ∉ QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) := by
  rw [show ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K) = 1 from rfl, ciQE_one]
  exact Finset.notMem_empty P

theorem ciMemG (P : rowSG Pr sel (mu0 X.F X.E X.K S)) : P.1 ∈ Pr.vGs := by
  classical
  rcases Finset.mem_union.1 P.2 with h | h
  · exact h
  · exact absurd h (ciNotQ sel S P.1)

end Inst

section PsiInst

theorem ciEntB_join0 {E : Type} [Field E] [NumberField E] [StarRing E] (q : ℕ) (x₀ : HomE E (Examples₂.R0.N 0) (Examples₂.R0.N (0 + 1)))
    (y' : Sp E (Examples₂.R0.N (0 + 1))) {p p' : ℕ} (hp : p < Examples₂.R0.N (0 + 1)) (hp' : p' ≤ Examples₂.R0.N 0) :
    LocE.entB q Examples₂.R0.k (cOf Examples₂.R0 0) (Examples₂.R0.N 0) (cOf Examples₂.R0 (0 + 1)) (Examples₂.R0.N (0 + 1)) (fun i => i + 1) (fun i => i + 1)
      (joinCol (c' := cOf Examples₂.R0 0) (c := cOf Examples₂.R0 (0 + 1)) x₀ y') p p' = if h : p' < Examples₂.R0.N 0 then x₀ (Pi.single ⟨p', h⟩ 1) ⟨p, hp⟩ else (q : E) * y' ⟨p, hp⟩ :=
  ciEntB_join rfl rfl rfl x₀ y' hp hp'

variable {X : Fields} {Pr : Primes X} (Ch : Chars X Pr Examples₂.R0.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  {mq : ℕ → rowSG Pr sel (mu0 X.F X.E X.K S) → X.K}

theorem ciPsiAt_eq (P : rowSG Pr sel (mu0 X.F X.E X.K S)) : ∃ cK : X.K, ∀ (x₀ : HomE X.E (Examples₂.R0.N 0) (Examples₂.R0.N (0 + 1)))
    (y' : Sp X.E (Examples₂.R0.N (0 + 1))),
    PsiAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P 1 x₀ y' =
      cK * LocE.PhiG (P := P.1) (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) false Examples₂.R0.k Examples₂.R0.r Examples₂.R0.t (0 + 1) (cOf Examples₂.R0 0)
        (Examples₂.R0.N 0) (cOf Examples₂.R0 (0 + 1)) (Examples₂.R0.N (0 + 1)) (joinCol x₀ y') := by
  refine ⟨muAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P 1 *
    (muAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P 1)⁻¹ *
    (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq).sq P ^ (-(LocE.vP P.1 (qOf P.1) 1) * ((Examples₂.R0.N (0 + 1) + cOf Examples₂.R0 (0 + 1) : ℕ) : ℤ)) *
    (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq).sq P ^ (LocE.vP P.1 (qOf P.1) 1 * ((Examples₂.R0.N 0 + cOf Examples₂.R0 0 : ℕ) : ℤ)),
    fun x₀ y' => ?_⟩
  unfold PsiAt omPhi
  rw [ciOm_one]
  congr 1
  unfold PhiAt
  rw [if_pos (ciMemG sel S P)]
  rfl

open Classical in
theorem ciPsiSupp (_hX : X.Ok) (_hPr : Pr.Ok) (al : (ciIdx Ch (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K))).β 0)
    (P : rowSG Pr sel (mu0 X.F X.E X.K S)) (x₀ : HomE X.E (Examples₂.R0.N 0) (Examples₂.R0.N (0 + 1))) (y' : Sp X.E (Examples₂.R0.N (0 + 1)))
    (hne : PsiAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P
      ((ciIdx Ch (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K))).h 0 al P) x₀ y' ≠ 0)
    (i : Fin (Examples₂.R0.N (0 + 1))) :
    IntAt P.1 ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq).M) * y' i) := by
  rw [if_pos (ciMemG sel S P), pow_one]
  obtain ⟨cK, hcK⟩ := ciPsiAt_eq Ch sel S P
  have hne' : LocE.PhiG (P := P.1) (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) false Examples₂.R0.k Examples₂.R0.r Examples₂.R0.t (0 + 1) (cOf Examples₂.R0 0)
      (Examples₂.R0.N 0) (cOf Examples₂.R0 (0 + 1)) (Examples₂.R0.N (0 + 1)) (joinCol x₀ y') ≠ 0 := by
    intro h0
    apply hne
    show PsiAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P 1 x₀ y' = 0
    rw [hcK, h0, mul_zero]
  have h1 := ciPhiG_int _ _ _ (joinCol x₀ y') hne' i.1 (Examples₂.R0.N 0) (Nat.lt_of_lt_of_le i.2 (Nat.le_add_right _ _)) (by decide)
  rw [ciEntB_join0 _ x₀ y' i.2 (le_refl _), dif_neg (lt_irrefl _)] at h1
  exact h1

theorem ciPsiSuppX (_hX : X.Ok) (_hPr : Pr.Ok) (al : (ciIdx Ch (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K))).β 0)
    (P : rowSG Pr sel (mu0 X.F X.E X.K S)) (x₀ : HomE X.E (Examples₂.R0.N 0) (Examples₂.R0.N (0 + 1))) (y' : Sp X.E (Examples₂.R0.N (0 + 1)))
    (hne : PsiAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P
      ((ciIdx Ch (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K))).h 0 al P) x₀ y' ≠ 0)
    (s : Fin (Examples₂.R0.N 0)) (l : Fin (Examples₂.R0.N (0 + 1))) :
    IntAt P.1 ((qOf P.1 : X.E) ^ (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq).A * x₀ (Pi.single s 1) l) := by
  show IntAt P.1 ((qOf P.1 : X.E) ^ 1 * x₀ (Pi.single s 1) l)
  rw [pow_one]
  obtain ⟨cK, hcK⟩ := ciPsiAt_eq Ch sel S P
  have hne' : LocE.PhiG (P := P.1) (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) false Examples₂.R0.k Examples₂.R0.r Examples₂.R0.t (0 + 1) (cOf Examples₂.R0 0)
      (Examples₂.R0.N 0) (cOf Examples₂.R0 (0 + 1)) (Examples₂.R0.N (0 + 1)) (joinCol x₀ y') ≠ 0 := by
    intro h0
    apply hne
    show PsiAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P 1 x₀ y' = 0
    rw [hcK, h0, mul_zero]
  have hs8 : s.1 < Examples₂.R0.r + (0 + 1 - 1) * Examples₂.R0.t := by have := s.2; simp [Examples₂.exampleRanks_N_formula] at this ⊢; omega
  have h1 := ciPhiG_int _ _ _ (joinCol x₀ y') hne' l.1 s.1 (Nat.lt_of_lt_of_le l.2 (Nat.le_add_right _ _)) hs8
  rw [ciEntB_join0 _ x₀ y' l.2 s.2.le, dif_pos s.2] at h1
  exact (ciIntAt_q (q := qOf P.1)).mul h1

open Classical in
theorem ciPsiInv (hX : X.Ok) (hPr : Pr.Ok) (al : (ciIdx Ch (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K))).β 0)
    (P : rowSG Pr sel (mu0 X.F X.E X.K S)) (x₀ : HomE X.E (Examples₂.R0.N 0) (Examples₂.R0.N (0 + 1))) (y' z : Sp X.E (Examples₂.R0.N (0 + 1)))
    (hz : ∀ i, IntAt P.1 (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq).M))⁻¹ * z i)) :
    PsiAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P
        ((ciIdx Ch (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K))).h 0 al P) x₀ (y' + z) =
      PsiAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P
        ((ciIdx Ch (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K))).h 0 al P) x₀ y' := by
  have hG := ciMemG sel S P
  have hu := ciQ_notMem_sq hX hPr hG
  obtain ⟨cK, hcK⟩ := ciPsiAt_eq Ch sel S P
  show PsiAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P 1 x₀ (y' + z) =
    PsiAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P 1 x₀ y'
  rw [hcK, hcK]
  congr 1
  refine ciPhiG_congr (ciQ_mem P.1) (ciQ_ne_zero hu) _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) fun p p' hp hp' => ?_
  have hc1 : cOf Examples₂.R0 (0 + 1) = 0 := rfl
  have hN1 : Examples₂.R0.N (0 + 1) = 24 := rfl
  have hN0 : Examples₂.R0.N 0 = 8 := rfl
  have ha : Examples₂.R0.r + (0 + 1 - 1) * Examples₂.R0.t = 9 := rfl
  have hp24 : p < Examples₂.R0.N (0 + 1) := by omega
  have hp8 : p' ≤ Examples₂.R0.N 0 := by omega
  rw [ciEntB_join0 _ x₀ (y' + z) hp24 hp8, ciEntB_join0 _ x₀ y' hp24 hp8]
  by_cases h8 : p' < Examples₂.R0.N 0
  · rw [dif_pos h8, dif_pos h8]
    exact ⟨0, ciIntAt_zero, by rw [mul_zero, add_zero]⟩
  · rw [dif_neg h8, dif_neg h8]
    have h1 := hz ⟨p, hp24⟩
    rw [if_pos hG, pow_zero, inv_one, one_mul] at h1
    exact ⟨z ⟨p, hp24⟩, h1, by rw [Pi.add_apply, mul_add]⟩

theorem ciPsiInvX (hX : X.Ok) (hPr : Pr.Ok) (al : (ciIdx Ch (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K))).β 0)
    (P : rowSG Pr sel (mu0 X.F X.E X.K S)) (x₀ z : HomE X.E (Examples₂.R0.N 0) (Examples₂.R0.N (0 + 1))) (y' : Sp X.E (Examples₂.R0.N (0 + 1)))
    (hz : ∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq).B)⁻¹ * z (Pi.single s 1) l)) :
    PsiAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P
        ((ciIdx Ch (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K))).h 0 al P) (x₀ + z) y' =
      PsiAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P
        ((ciIdx Ch (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K))).h 0 al P) x₀ y' := by
  have hG := ciMemG sel S P
  have hu := ciQ_notMem_sq hX hPr hG
  have hq0 := ciQ_ne_zero hu
  obtain ⟨cK, hcK⟩ := ciPsiAt_eq Ch sel S P
  show PsiAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P 1 (x₀ + z) y' =
    PsiAt Ch sel (mu0 X.F X.E X.K S) (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq) 0 P 1 x₀ y'
  rw [hcK, hcK]
  congr 1
  refine ciPhiG_congr (ciQ_mem P.1) hq0 _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) fun p p' hp hp' => ?_
  have hc1 : cOf Examples₂.R0 (0 + 1) = 0 := rfl
  have hN1 : Examples₂.R0.N (0 + 1) = 24 := rfl
  have hN0 : Examples₂.R0.N 0 = 8 := rfl
  have ha : Examples₂.R0.r + (0 + 1 - 1) * Examples₂.R0.t = 9 := rfl
  have hp24 : p < Examples₂.R0.N (0 + 1) := by omega
  have hp8 : p' ≤ Examples₂.R0.N 0 := by omega
  rw [ciEntB_join0 _ (x₀ + z) y' hp24 hp8, ciEntB_join0 _ x₀ y' hp24 hp8]
  by_cases h8 : p' < Examples₂.R0.N 0
  · rw [dif_pos h8, dif_pos h8]
    have h1 := hz ⟨p', h8⟩ ⟨p, hp24⟩
    rw [show (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) mq).B = 1 from rfl, pow_one] at h1
    refine ⟨_, h1, ?_⟩
    rw [LinearMap.add_apply, Pi.add_apply, ← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
  · rw [dif_neg h8, dif_neg h8]
    exact ⟨0, ciIntAt_zero, by rw [mul_zero, add_zero]⟩

end PsiInst

section Tied

variable {X : Fields} {Pr : Primes X}

open Classical in

def ciQU (P : HeightOneSpectrum (𝓞 X.E)) : X.Eˣ := if h : (qOf P : X.E) ≠ 0 then Units.mk0 _ h else 1

open Classical in

def ciMuqG {m : ℕ} (G : ChGlob X m) (i : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : X.K :=
  if h : ∃ (hi : i < m) (y : X.K), G.σ₀ y = ((((G.mu0 ⟨i, hi⟩).locK P (ciQU P)) : ℂˣ) : ℂ)⁻¹ then h.choose_spec.choose else 1

def ciMuq {m : ℕ} (G : ChGlob X m) (ξ : Chr X.F X.E X.K) {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (j : ℕ) (P : SB) : X.K :=
  ciMuqG G (j - 1) P.1 * (((qValC ξ P.1)⁻¹ : X.Kˣ) : X.K)

theorem ciMuq_tie {m : ℕ} (G : ChGlob X m) (ξ : Chr X.F X.E X.K) {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
    (hval : ∀ (j : Fin m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    (i : ℕ) (h : i < m) (P : SB) (hP : P.1 ∈ Pr.vGs) (qu : X.Eˣ) (hqu : (qu : X.E) = (qOf P.1 : X.E)) :
    G.σ₀ (ciMuq G ξ (i + 1) P) =
      (((G.mu0 ⟨i, h⟩).locK P.1 qu : ℂˣ) : ℂ)⁻¹ * G.σ₀ ((((qValC ξ P.1)⁻¹ : X.Kˣ)) : X.K) := by
  have hq0 : (qOf P.1 : X.E) ≠ 0 := by rw [← hqu]; exact qu.ne_zero
  have e : qu = ciQU P.1 := by
    unfold ciQU
    rw [dif_pos hq0]
    exact Units.ext (by rw [Units.val_mk0, hqu])
  have hd : ∃ (hi : i < m) (y : X.K), G.σ₀ y = ((((G.mu0 ⟨i, hi⟩).locK P.1 (ciQU P.1)) : ℂˣ) : ℂ)⁻¹ := ⟨h, hval ⟨i, h⟩ P.1 hP⟩
  unfold ciMuq ciMuqG
  rw [Nat.add_sub_cancel, dif_pos hd, map_mul, hd.choose_spec.choose_spec, e]

variable {R : Ranks} (Ch : Chars X Pr R.m)

theorem ciCst_weil (hX : X.Ok) (hPr : Pr.Ok) {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (hSB : ∀ P ∈ SB, P ∈ Pr.vGs)
    (mq : ℕ → SB → X.K) {σ₀ : X.K →+* ℂ} {xi0 : X.E} (hW : Ch.WeilTied σ₀ xi0) (hxi : ∀ P ∈ SB, IntAt P xi0) :
    (ciCst Ch SB mq).WeilTied σ₀ xi0 := by
  intro P a b ha hab
  have hD : (ciCst Ch SB mq).D P = 1 := rfl
  rw [hD, pow_one] at ha hab ⊢
  have hq := ciQ_mem (E := X.E) P.1
  have hu := ciQ_notMem_sq hX hPr (hSB P.1 P.2)
  have hq0 : (qOf P.1 : X.E) ≠ 0 := ciQ_ne_zero hu
  show σ₀ (ciPsi Ch P a) = _
  unfold ciPsi
  rw [if_pos ha]
  have hpsi : psi0P Ch P.1 = Ch.psi0 ⟨P.1, hSB P.1 P.2⟩ := by
    unfold psi0P
    rw [dif_pos (hSB P.1 P.2)]
  rw [hpsi]
  apply hW
  have e1 : xi0 * ((qOf P.1 : X.E) * a) - (b : X.E) = (qOf P.1 : X.E) * (xi0 * a - (b : X.E) / (qOf P.1 : X.E)) := by
    field_simp
  have h0 : redP P.1 (xi0 * ((qOf P.1 : X.E) * a) - (b : X.E)) = 0 := by
    rw [e1, reduction_mul ciIntAt_q hab, redP_natCast_eq_zero hq, zero_mul]
  rw [redP_sub ((hxi P.1 P.2).mul ha) (ciIntAt_intCast b), reduction_mul (hxi P.1 P.2) ha, redP_intCast, sub_eq_zero] at h0
  exact h0

theorem intAt_of_redP_ne_zero₂ {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : redP P a ≠ 0) : IntAt P a := by
  by_contra h'
  exact h (reduction_eq_zero_of_not_integral P h')

def ciXiUnitG (Pr : Primes X) (xi0 : X.E) : Prop :=
  ∀ i : Fin 2, ∃ b : ℤ, ¬ (Pr.g i : ℤ) ∣ b ∧ ∀ w ∈ Pr.vG i, redP w xi0 = (b : 𝓞 X.E ⧸ w.asIdeal)

theorem ciXiUnitG.unit (hPr : Pr.Ok) {xi0 : X.E} (h : ciXiUnitG Pr xi0) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs) :
    IntAt w xi0 ∧ redP w xi0 ≠ 0 := by
  obtain ⟨i, hi⟩ := ciVGs_cases hw
  obtain ⟨b, hb, hbw⟩ := h i
  have hne : redP w xi0 ≠ 0 := by
    rw [hbw w hi]
    intro h0
    have h1 := (owedC_intCast_eq_iff (A := 𝓞 X.E ⧸ w.asIdeal) (ciQOf_prime hPr hw) (ciCard w) b 0).1 (by rw [h0, Int.cast_zero])
    rw [sub_zero, ciQOf_eq hPr hi] at h1
    exact hb h1
  exact ⟨intAt_of_redP_ne_zero₂ hne, hne⟩

def ciWeilChars {m : ℕ} (hPr : Pr.Ok) (Ch : Chars X Pr m) (ζ : {w // w ∈ Pr.vGs} → X.K) (hζ : ∀ w, ζ w ^ qOf w.1 = 1) (xi0 : X.E) :
    Chars X Pr m :=
  { Ch with psi0 := fun w => AddChar.mulShift (owedC_chr (ciQOf_prime hPr w.2) (ciCard w.1) (hζ w)) (redP w.1 xi0) }

theorem ciWeilChars_weilTied {m : ℕ} (hPr : Pr.Ok) (Ch : Chars X Pr m) (σ₀ : X.K →+* ℂ) (ζ : {w // w ∈ Pr.vGs} → X.K)
    (hζ : ∀ w, ζ w ^ qOf w.1 = 1) (hσ : ∀ w, σ₀ (ζ w) = Complex.exp (2 * Real.pi * Complex.I / (qOf w.1 : ℂ))) (xi0 : X.E) :
    (ciWeilChars hPr Ch ζ hζ xi0).WeilTied σ₀ xi0 := by
  intro w c b h
  have e : (ciWeilChars hPr Ch ζ hζ xi0).psi0 w c = owedC_chr (ciQOf_prime hPr w.2) (ciCard w.1) (hζ w) (redP w.1 xi0 * c) := rfl
  rw [e, h, owedC_chr_intCast, map_zpow₀, hσ, owedC_exp_zpow]

theorem ciWeilChars_ok {m : ℕ} (hPr : Pr.Ok) {Ch : Chars X Pr m} (hCh : Ch.Ok) (σ₀ : X.K →+* ℂ) (ζ : {w // w ∈ Pr.vGs} → X.K)
    (hζ : ∀ w, ζ w ^ qOf w.1 = 1) (hσ : ∀ w, σ₀ (ζ w) = Complex.exp (2 * Real.pi * Complex.I / (qOf w.1 : ℂ))) {xi0 : X.E}
    (hxi : ciXiUnitG Pr xi0) : (ciWeilChars hPr Ch ζ hζ xi0).Ok where
  psi_zero_nontrivial_character w h := by
    obtain ⟨i, hi⟩ := ciVGs_cases w.2
    obtain ⟨b, hb, hbw⟩ := hxi i
    have h1 := ciWeilChars_weilTied hPr Ch σ₀ ζ hζ hσ xi0 w 1 b (by rw [hbw w.1 hi, mul_one])
    rw [h, AddChar.one_apply, map_one, ← owedC_exp_zpow] at h1
    have hq := ciQOf_prime hPr w.2
    have h2 := ((Complex.isPrimitiveRoot_exp (qOf w.1) hq.ne_zero).zpow_eq_one_iff_dvd b).1 h1.symm
    rw [ciQOf_eq hPr hi] at h2
    exact hb h2
  chi_inj := hCh.chi_inj
  chi_same := hCh.chi_same
  characterAgreesOnPlaces i w w' hw hw' a := by
    obtain ⟨b, -, hbw⟩ := hxi i
    apply σ₀.injective
    rw [ciWeilChars_weilTied hPr Ch σ₀ ζ hζ hσ xi0 w (a : 𝓞 X.E ⧸ w.1.asIdeal) (b * a) (by rw [hbw w.1 hw, Int.cast_mul]),
      ciWeilChars_weilTied hPr Ch σ₀ ζ hζ hσ xi0 w' (a : 𝓞 X.E ⧸ w'.1.asIdeal) (b * a) (by rw [hbw w'.1 hw', Int.cast_mul]),
      ciQOf_eq hPr hw, ciQOf_eq hPr hw']
  chi_om := hCh.chi_om

variable {Ch} in
open Classical in

theorem ChIdx.Ok.chars_weilTied (hX : X.Ok) (hPr : Pr.Ok) {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m}
    {m2 : ℕ} (hL : L.Ok Ch sel mu cst G m2) : Ch.WeilTied G.σ₀ G.xi0 := by
  intro w c b h
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective c
  let P : rowSG Pr sel mu := ⟨w.1, Finset.mem_union_left _ w.2⟩
  have hq := ciQ_mem (E := X.E) w.1
  have hu := ciQ_notMem_sq hX hPr w.2
  have hq0 : (qOf w.1 : X.E) ≠ 0 := ciQ_ne_zero hu
  have hy : IntAt w.1 (algebraMap (𝓞 X.E) X.E y) := IntAt.coe w.1 y
  have h1 := hL.psi0 P (algebraMap (𝓞 X.E) X.E y) w.2 hy
  have hD : cst.D P = 1 := hL.depthG P w.2
  have hxi : IntAt w.1 G.xi0 := (hL.xiUnitAtPrime P).1
  have e2 : G.xi0 * (algebraMap (𝓞 X.E) X.E y / (qOf w.1 : X.E)) - (b : X.E) / (qOf w.1 : X.E) =
      (G.xi0 * algebraMap (𝓞 X.E) X.E y - (b : X.E)) / (qOf w.1 : X.E) := by ring
  have hab : IntAt P.1 (G.xi0 * (algebraMap (𝓞 X.E) X.E y / (qOf w.1 : X.E)) - (b : X.E) / (qOf P.1 : X.E) ^ cst.D P) := by
    rw [hD, pow_one]
    show IntAt w.1 (G.xi0 * (algebraMap (𝓞 X.E) X.E y / (qOf w.1 : X.E)) - (b : X.E) / (qOf w.1 : X.E))
    rw [e2]
    refine ciIntAt_div hq hu (ciIntAt_sub (hxi.mul hy) (ciIntAt_intCast b)) ?_
    rw [redP_sub (hxi.mul hy) (ciIntAt_intCast b), reduction_mul hxi hy, redP_intCast, reduction_coe, h, sub_self]
  have ha : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * (algebraMap (𝓞 X.E) X.E y / (qOf w.1 : X.E))) := by
    rw [hD, pow_one]
    show IntAt w.1 ((qOf w.1 : X.E) * (algebraMap (𝓞 X.E) X.E y / (qOf w.1 : X.E)))
    rw [mul_div_cancel₀ _ hq0]
    exact hy
  have h2 := hL.weil P _ b ha hab
  rw [h1, hD, pow_one] at h2
  have e : psi0P Ch P.1 (redP P.1 (algebraMap (𝓞 X.E) X.E y)) = Ch.psi0 w (Ideal.Quotient.mk w.1.asIdeal y) := by
    show psi0P Ch w.1 (redP w.1 (algebraMap (𝓞 X.E) X.E y)) = _
    unfold psi0P
    rw [dif_pos w.2, reduction_coe]
  rw [e] at h2
  exact h2

end Tied

section InstOk

variable {X : Fields} {Pr : Primes X} (Ch : Chars X Pr Examples₂.R0.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  {mq : ℕ → rowSG Pr sel (mu0 X.F X.E X.K S) → X.K}

theorem ciIdx_ok (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (h4 : ∀ w ∈ Pr.vGs, qOf w % 4 = 1) (G : ChGlob X Examples₂.R0.m)
    (hW : Ch.WeilTied G.σ₀ G.xi0) (hxi : ∀ w ∈ Pr.vGs, IntAt w G.xi0 ∧ redP w G.xi0 ≠ 0)
    (hmu : ∀ (j : Fin Examples₂.R0.m) (w : {w // w ∈ Pr.vGs}) (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ), (x : X.E) = (y : X.E) →
      (c : 𝓞 X.E ⧸ w.1.asIdeal) = Ideal.Quotient.mk w.1.asIdeal y →
      (((G.mu0 j).locK w.1 x : ℂˣ) : ℂ) = G.σ₀ (((Ch.chi j w c)⁻¹ : X.Kˣ) : X.K))
    (hval : ∀ (j : Fin Examples₂.R0.m) (w : HeightOneSpectrum (𝓞 X.E)), w ∈ Pr.vGs →
      ∃ y : X.K, G.σ₀ y = ((((G.mu0 j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹) :
    (ciIdx Ch (QE sel ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K))).Ok Ch sel (mu0 X.F X.E X.K S)
      (ciCst Ch (rowSG Pr sel (mu0 X.F X.E X.K S)) (ciMuq G ((mu0 X.F X.E X.K S : Tup X.F X.E X.K S) : Chr X.F X.E X.K))) G 0 := by
  refine
    { hm := rfl
      cst_ok := ciCst_ok hPr hCh (fun P hP => ciMemG sel S ⟨P, hP⟩) (fun P hP => h4 P (ciMemG sel S ⟨P, hP⟩))
      xiUnitAtPrime := fun P => hxi P.1 (ciMemG sel S P)
      weil := ciCst_weil Ch hX hPr (fun P hP => ciMemG sel S ⟨P, hP⟩) _ hW (fun P hP => (hxi P (ciMemG sel S ⟨P, hP⟩)).1)
      muqQ := fun _ _ P hP => absurd (ciMemG sel S P) hP
      muqG := fun i h P hP qu hqu => ciMuq_tie G _ hval i h P hP qu hqu
      mu0G := hmu
      psi0 := ?_
      deep := fun _ _ _ _ i hi => absurd hi (Nat.not_lt_zero i)
      zero_uniq := ⟨⟨0, by decide⟩, fun b => Fin.ext (by have := b.2; simp at this; omega)⟩
      zero_h := fun _ _ => rfl
      zero_G := fun _ => rfl
      zero_Q := fun _ => rfl
      last_uniq := ⟨⟨0, by decide⟩, fun b => Fin.ext (by have := b.2; simp at this; omega)⟩
      last_h := fun _ _ => rfl
      nonvan := fun i hi => absurd hi (Nat.not_lt_zero i)
      inj := fun i hi => absurd hi (Nat.not_lt_zero i)
      surj := fun i hi => absurd hi (Nat.not_lt_zero i)
      stabG := fun _ _ _ _ => Subgroup.one_mem _
      depthG := fun _ _ => rfl
      depthQ := fun P hP => absurd (ciMemG sel S P) hP
      depthQ' := fun P hP => absurd (ciMemG sel S P) hP
      boundQ := fun _ _ P hP => absurd (ciMemG sel S P) hP
      psiSupp := ciPsiSupp Ch sel S hX hPr
      psiInv := ciPsiInv Ch sel S hX hPr
      xiSupp := fun i hi => absurd hi (Nat.not_lt_zero i)
      xiInv := fun i hi => absurd hi (Nat.not_lt_zero i)
      psiSuppX := ciPsiSuppX Ch sel S hX hPr
      psiInvX := ciPsiInvX Ch sel S hX hPr
      int := ?_
      grpQ := fun _ _ P => absurd P.2 (ciNotQ sel S P.1)
      chrQ := fun _ _ P => absurd P.2 (ciNotQ sel S P.1)
      grpG := ?_
      chrG := ?_ }
  · intro P a _ ha
    show ciPsi Ch P _ = _
    have hq0 : (qOf P.1 : X.E) ≠ 0 := by exact_mod_cast (ciQOf_prime hPr (ciMemG sel S P)).ne_zero
    unfold ciPsi
    rw [mul_div_cancel₀ _ hq0, if_pos ha]
  · intro j b P
    show Loc.prX (Loc.Cbe (Jat (Pr := Pr) (R := Examples₂.R0) false j P.1) 1) ≤ _
    rw [ciJat j (ciMemG sel S P)]
    exact ciPrX_le
  · intro j b w hbar
    have hj : j ≤ 1 := by
      by_contra h
      have h0 : (if j ≤ 1 then 1 else 0) = 0 := if_neg h
      exact Nat.not_lt_zero _ (lt_of_lt_of_eq (show Fin (if j ≤ 1 then 1 else 0) from b).2 h0)
    interval_cases j
    · exact first_level_reduction_group Ch hX hPr w hbar
    · exact second_level_reduction_group Ch hX hPr w hbar
  · intro j b w hbar g r hr hrg hred
    have hj : j ≤ 1 := by
      by_contra h
      have h0 : (if j ≤ 1 then 1 else 0) = 0 := if_neg h
      exact Nat.not_lt_zero _ (lt_of_lt_of_eq (show Fin (if j ≤ 1 then 1 else 0) from b).2 h0)
    interval_cases j
    · exact character_first_level_group Ch sel S hX hPr w _ hbar g r hr hrg hred
    · exact character_second_level_group Ch sel S hX hPr w _ hbar g r hr hrg hred

end InstOk

section Nd2

open Formalism.L2.Host Formalism.FrobeniusOrbits

variable (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hLL : cycQ nd2N ≤ LL)

theorem primes_over_one_mod_four : ∀ w ∈ (toyPrimes LL hLL).vGs, qOf w % 4 = 1 := by
  intro w hw
  obtain ⟨i, hi⟩ := ciVGs_cases hw
  rw [ciQOf_eq (examplePrimes_ok LL hLL) hi]
  have h4 : toyFirstParameter % 4 = 1 ∧ toySecondParameter % 4 = 1 := by decide +kernel
  fin_cases i
  · exact h4.1
  · exact h4.2

theorem exists_root_of_unity_phase (w : {w // w ∈ (toyPrimes LL hLL).vGs}) :
    ∃ ζ : (nd2X LL hLL).K, toyComplexEmbedding LL hLL ζ = Complex.exp (2 * Real.pi * Complex.I / (qOf w.1 : ℂ)) := by
  obtain ⟨i, hi⟩ := ciVGs_cases w.2
  have hq : qOf w.1 = (toyPrimes LL hLL).g i := ciQOf_eq (examplePrimes_ok LL hLL) hi
  have hdvd : (toyPrimes LL hLL).g i ∣ nd2N := by
    fin_cases i
    · exact example_primes_dvd_level.1
    · exact example_primes_dvd_level.2.1
  have := example_enough_roots LL hLL hdvd
  have : NeZero ((toyPrimes LL hLL).g i) := ⟨((examplePrimes_ok LL hLL).g_prime i).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (CoF ndIota LL) ((toyPrimes LL hLL).g i)
  rw [hq]
  exact owedC_exists_exp (toyComplexEmbedding LL hLL) ((examplePrimes_ok LL hLL).g_prime i).ne_zero hζ

def nd2Zeta (w : {w // w ∈ (toyPrimes LL hLL).vGs}) : (nd2X LL hLL).K := (exists_root_of_unity_phase LL hLL w).choose

theorem nd2Zeta_sig (w : {w // w ∈ (toyPrimes LL hLL).vGs}) :
    toyComplexEmbedding LL hLL (nd2Zeta LL hLL w) = Complex.exp (2 * Real.pi * Complex.I / (qOf w.1 : ℂ)) :=
  (exists_root_of_unity_phase LL hLL w).choose_spec

theorem nd2Zeta_pow (w : {w // w ∈ (toyPrimes LL hLL).vGs}) : nd2Zeta LL hLL w ^ qOf w.1 = 1 := by
  apply (toyComplexEmbedding LL hLL).injective
  rw [map_pow, nd2Zeta_sig, map_one]
  exact (Complex.isPrimitiveRoot_exp _ (ciQOf_prime (examplePrimes_ok LL hLL) w.2).ne_zero).pow_eq_one

def nd2B : Fin 2 → ℤ := ![((Examples₂.H0.condN : ℕ) : ℤ) * 18, ((Examples₂.H0.condN : ℕ) : ℤ) * 768]

theorem prime_generator_formula (i : Fin 2) : (toyPrimes LL hLL).piG i = nd2z LL hLL 1 (nd2B i) := by
  fin_cases i <;> rfl

def nd2Xi : (nd2X LL hLL).E := -1 / hwE Examples₂.H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL)

theorem highest_weight_element_ne : hwE Examples₂.H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL) ≠ 0 := by
  intro h0
  have h1 := hwE_sq Examples₂.H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL)
  rw [h0, zero_pow two_ne_zero, zero_eq_neg] at h1
  have h2 : (Examples₂.H0.d : ℕ) ≠ 0 := example_discriminant_pos.ne'
  exact h2 (by exact_mod_cast h1)

theorem xi_unit_at_gaussian_primes : ciXiUnitG (toyPrimes LL hLL) (nd2Xi LL hLL) := by
  have hPr := examplePrimes_ok LL hLL
  intro i
  refine ⟨-(nd2B i), ?_, fun w hw => ?_⟩
  · have h1 : ¬ ((toyFirstParameter : ℕ) : ℤ) ∣ -(((Examples₂.H0.condN : ℕ) : ℤ) * 18) := by decide +kernel
    have h2 : ¬ ((toySecondParameter : ℕ) : ℤ) ∣ -(((Examples₂.H0.condN : ℕ) : ℤ) * 768) := by decide +kernel
    fin_cases i
    · exact h1
    · exact h2
  · have hc : (nd2X LL hLL).conjO ((toyPrimes LL hLL).piG i) ∈ w.asIdeal := (mem_divs (ciConjPiG_ne_zero hPr i) w).1 hw
    rw [prime_generator_formula, conjO_hz _ _ _ _ example_discriminant_pos] at hc
    have hs : hwO Examples₂.H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL) ∉ w.asIdeal := by
      intro hm
      apply one_notMem w
      have e : (1 : 𝓞 (nd2X LL hLL).E) = hz Examples₂.H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL) 1 (-nd2B i) -
          ((-nd2B i : ℤ) : 𝓞 (nd2X LL hLL).E) * hwO Examples₂.H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL) := by
        unfold hz; push_cast; ring
      rw [e]
      exact sub_mem hc (Ideal.mul_mem_left _ _ hm)
    refine redP_eq w (r := -1) hs ?_ ?_
    · show hwE Examples₂.H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL) * nd2Xi LL hLL = _
      unfold nd2Xi
      rw [map_neg, map_one, mul_div_cancel₀ _ (highest_weight_element_ne LL hLL)]
    · rw [← map_intCast (Ideal.Quotient.mk w.asIdeal), ← map_mul, Ideal.Quotient.eq]
      have e : hwO Examples₂.H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL) * ((-nd2B i : ℤ) : 𝓞 (nd2X LL hLL).E) - (-1) =
          hz Examples₂.H0.toHostRaw ndIota LL (exampleField_le_cyclotomic.trans hLL) 1 (-nd2B i) := by
        unfold hz; push_cast; ring
      rw [e]
      exact hc

def nd2ChW (h : ToyHeckeCondition LL hLL) : Chars (nd2X LL hLL) (toyPrimes LL hLL) Examples₂.R0.m :=
  ciWeilChars (examplePrimes_ok LL hLL) ((toyCharacters LL hLL).ofHecke (toyComplexEmbedding LL hLL) h.choose h.choose_spec.choose) (nd2Zeta LL hLL)
    (nd2Zeta_pow LL hLL) (nd2Xi LL hLL)

def nd2G (h : ToyHeckeCondition LL hLL) : ChGlob (nd2X LL hLL) Examples₂.R0.m := ⟨toyComplexEmbedding LL hLL, nd2Xi LL hLL, h.choose⟩

theorem nd2ChW_ok (h : ToyHeckeCondition LL hLL) : (nd2ChW LL hLL h).Ok :=
  ciWeilChars_ok (examplePrimes_ok LL hLL) (Chars.ofHecke_ok (exampleCharacters_ok LL hLL) _ _ _) (toyComplexEmbedding LL hLL) _ _ (nd2Zeta_sig LL hLL)
    (xi_unit_at_gaussian_primes LL hLL)

theorem nd2ChW_weil (h : ToyHeckeCondition LL hLL) : (nd2ChW LL hLL h).WeilTied (toyComplexEmbedding LL hLL) (nd2Xi LL hLL) :=
  ciWeilChars_weilTied (examplePrimes_ok LL hLL) _ (toyComplexEmbedding LL hLL) _ _ (nd2Zeta_sig LL hLL) (nd2Xi LL hLL)

theorem nd2ChW_tied (h : ToyHeckeCondition LL hLL) :
    (nd2ChW LL hLL h).Tied (toyComplexEmbedding LL hLL) (fun j τ => ((nd2W LL hLL).row τ).e j) h.choose h.choose_spec.choose := by
  have t := Chars.ofHecke_tied h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2.1 h.choose_spec.choose_spec.2.2.1
    h.choose_spec.choose_spec.2.2.2
  exact ⟨fun j => ⟨(t.mu0 j).unitary, (t.mu0 j).triv, (t.mu0 j).inf, (t.mu0 j).unr, (t.mu0 j).tame, (t.mu0 j).atg⟩, t.muVal, t.etaT,
    t.etaVal⟩

theorem local_constants_conditions (h : ToyHeckeCondition LL hLL) (sel : HeightOneSpectrum (𝓞 (nd2X LL hLL).F) → HeightOneSpectrum (𝓞 (nd2X LL hLL).E))
    (S : Set ℕ) :
    (ciCst (nd2ChW LL hLL h) (rowSG (toyPrimes LL hLL) sel (mu0 (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K S))
      (ciMuq (nd2G LL hLL h) ((mu0 (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K S : Tup (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K S) : Chr (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K))).Ok :=
  ciCst_ok (examplePrimes_ok LL hLL) (nd2ChW_ok LL hLL h) (fun P hP => ciMemG sel S ⟨P, hP⟩)
    (fun P hP => primes_over_one_mod_four LL hLL P (ciMemG sel S ⟨P, hP⟩))

theorem character_index_conditions (h : ToyHeckeCondition LL hLL)
    (hval : ∀ (j : Fin Examples₂.R0.m) (w : HeightOneSpectrum (𝓞 (nd2X LL hLL).E)), w ∈ (toyPrimes LL hLL).vGs →
      ∃ y : (nd2X LL hLL).K, toyComplexEmbedding LL hLL y = ((((h.choose j).locK w (ciQU w)) : ℂˣ) : ℂ)⁻¹)
    (sel : HeightOneSpectrum (𝓞 (nd2X LL hLL).F) → HeightOneSpectrum (𝓞 (nd2X LL hLL).E)) (S : Set ℕ) :
    (ciIdx (R := Examples₂.R0) (nd2ChW LL hLL h) (QE sel ((mu0 (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K S : Tup (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K S) : Chr (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K))).Ok
      (nd2ChW LL hLL h) sel (mu0 (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K S)
      (ciCst (nd2ChW LL hLL h) (rowSG (toyPrimes LL hLL) sel (mu0 (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K S))
        (ciMuq (nd2G LL hLL h) ((mu0 (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K S : Tup (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K S) : Chr (nd2X LL hLL).F (nd2X LL hLL).E (nd2X LL hLL).K)))
      (nd2G LL hLL h) 0 :=
  ciIdx_ok (nd2ChW LL hLL h) sel S (exampleFields_ok LL hLL) (examplePrimes_ok LL hLL) (nd2ChW_ok LL hLL h) (primes_over_one_mod_four LL hLL) (nd2G LL hLL h)
    (nd2ChW_weil LL hLL h) (fun w hw => (xi_unit_at_gaussian_primes LL hLL).unit (examplePrimes_ok LL hLL) w hw)
    (fun j => (h.choose_spec.choose_spec.1 j).atg) hval

end Nd2

end Formalism.L2.Col
