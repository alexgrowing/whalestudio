import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast

open Polynomial Ideal

namespace GlobalTheory.TiltAlgClosed

theorem exists_prod_dvd_pow {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O]
    (s : Multiset O) : s = 0 ∨ ∃ a ∈ s, s.prod ∣ a ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => exact Or.inl rfl
  | cons b s ih =>
    right
    rcases ih with rfl | ⟨a, ha, h⟩
    · exact ⟨b, by simp, by simp⟩
    · rw [Multiset.prod_cons, Multiset.card_cons]
      rcases ValuationRing.dvd_total a b with hab | hba
      · refine ⟨b, by simp, ?_⟩
        rw [pow_succ']
        exact mul_dvd_mul_left _ (h.trans (pow_dvd_pow_of_dvd hab _))
      · refine ⟨a, by simp [ha], ?_⟩
        rw [pow_succ']
        exact mul_dvd_mul hba h

theorem splits_of_monic (O K : Type*) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K]
    {f : Polynomial O} (hf : f.Monic) : f.Splits := by
  refine Polynomial.Splits.of_splits_map_of_injective (IsFractionRing.injective O K)
    (IsAlgClosed.splits _) ?_
  intro a ha
  have hi : IsIntegral O a := by
    refine ⟨f, hf, ?_⟩
    rw [← Polynomial.eval_map]
    exact (Polynomial.mem_roots (hf.map _).ne_zero).mp ha
  exact IsIntegrallyClosed.isIntegral_iff.mp hi

section Roots

variable {O : Type*} (K : Type*) [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
  [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] {p : ℕ} [Fact p.Prime]
  [Fact ¬IsUnit (p : O)]

include K in

theorem roots_modP {g : (ModP O p)[X]} (hg : g.Monic) {d : ℕ} (hd : g.natDegree = d)
    (hd0 : d ≠ 0) :
    (∃ x, g.eval x = 0) ∧ {y | ∃ x, g.eval x = 0 ∧ y = x ^ p ^ d}.Finite := by
  classical
  have hl : g ∈ Polynomial.lifts (Ideal.Quotient.mk (span {(p : O)})) :=
    (Polynomial.mem_lifts _).mpr
      (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective g)
  obtain ⟨f, rfl, hdeg, hf⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hg
  have hs := splits_of_monic O K hf
  have hcard : Multiset.card f.roots = d := by
    rw [← hs.natDegree_eq_card_roots, hdeg, hd]
  have hev : ∀ x : O, (f.map (Ideal.Quotient.mk (span {(p : O)}))).eval
      (Ideal.Quotient.mk (span {(p : O)}) x) = Ideal.Quotient.mk (span {(p : O)}) (f.eval x) := by
    intro x
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
  constructor
  · obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (hcard ▸ Nat.pos_of_ne_zero hd0)
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [hev, ((Polynomial.mem_roots hf.ne_zero).mp ha).eq_zero, map_zero]
  · refine ((f.roots.toFinset.finite_toSet).image
      (fun a => (Ideal.Quotient.mk (span {(p : O)}) a : ModP O p) ^ p ^ d)).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hev, hs.eval_eq_prod_roots_of_monic hf, Ideal.Quotient.eq_zero_iff_mem,
      mem_span_singleton] at hx
    rcases exists_prod_dvd_pow (f.roots.map (x - ·)) with h0 | ⟨c, hc, hdvd⟩
    · have := congrArg Multiset.card h0
      rw [Multiset.card_map, hcard] at this
      exact absurd this hd0
    · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hc
      rw [Multiset.card_map, hcard] at hdvd
      refine ⟨a, by simpa using ha, ?_⟩
      have hle : d ≤ p ^ d := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
      have h1 : (p : O) ∣ (x - a) ^ p ^ d := (hx.trans hdvd).trans (pow_dvd_pow _ hle)
      rw [← mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_pow, map_sub] at h1
      have h2 := sub_pow_char_pow (R := ModP O p) (p := p) (n := d)
        (Ideal.Quotient.mk (span {(p : O)}) x) (Ideal.Quotient.mk (span {(p : O)}) a)
      exact (sub_eq_zero.mp (h2.symm.trans h1)).symm

omit [IsDomain O] [ValuationRing O] in
theorem eval₂_pow_p (P : (PreTilt O p)[X]) (n : ℕ) (x : ModP O p)
    (hx : P.eval₂ (PreTilt.coeff (n + 1)) x = 0) :
    P.eval₂ (PreTilt.coeff n) (x ^ p) = 0 := by
  have h := Polynomial.hom_eval₂ P (PreTilt.coeff (n + 1)) (frobenius (ModP O p) p) x
  have hc : (frobenius (ModP O p) p).comp (PreTilt.coeff (n + 1)) =
      (PreTilt.coeff n : PreTilt O p →+* ModP O p) := by
    ext z
    exact PreTilt.coeff_pow_p z n
  rw [hx, map_zero, hc, frobenius_def] at h
  exact h.symm

omit [IsDomain O] [ValuationRing O] in
theorem eval₂_pow_p_pow (P : (PreTilt O p)[X]) (k n : ℕ) (x : ModP O p)
    (hx : P.eval₂ (PreTilt.coeff (n + k)) x = 0) :
    P.eval₂ (PreTilt.coeff n) (x ^ p ^ k) = 0 := by
  induction k generalizing x with
  | zero => simpa using hx
  | succ k ih =>
    rw [pow_succ', pow_mul]
    exact ih _ (eval₂_pow_p P (n + k) x hx)

include K in

theorem exists_root_preTilt {P : (PreTilt O p)[X]} (hP : P.Monic) (hd0 : P.natDegree ≠ 0) :
    ∃ x, P.eval x = 0 := by
  classical
  set d := P.natDegree with hd
  haveI : Nontrivial (ModP O p) := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  have key := fun n => roots_modP K (hP.map (PreTilt.coeff (O := O) (p := p) n))
    (hP.natDegree_map _) hd0
  simp only [Polynomial.eval_map] at key
  let α : ℕ → Type _ := fun n =>
    {y : ModP O p | ∃ x, P.eval₂ (PreTilt.coeff (n + d)) x = 0 ∧ y = x ^ p ^ d}
  haveI hfin : ∀ n, Finite (α n) := fun n => (key (n + d)).2.to_subtype
  haveI : ∀ n, Nonempty (α n) := fun n => by
    obtain ⟨x, hx⟩ := (key (n + d)).1
    exact ⟨⟨_, x, hx, rfl⟩⟩
  let π : {i j : ℕ} → (hij : i ≤ j) → α j → α i := fun {i j} hij b =>
    ⟨b.1 ^ p ^ (j - i), by
      obtain ⟨x, hx, h⟩ := b.2
      refine ⟨x ^ p ^ (j - i), eval₂_pow_p_pow P _ _ x ?_, ?_⟩
      · rwa [show i + d + (j - i) = j + d by omega]
      · rw [h, ← pow_mul, ← pow_mul, mul_comm]⟩
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite (α := α) π
    (fun i a => Subtype.ext (by simp [π]))
    (fun i j k hij hjk a => Subtype.ext (by
      simp only [π]
      rw [← pow_mul, ← pow_add, show k - j + (j - i) = k - i by omega]))
    (fun i a => Set.toFinite _)
  have hcomp : ∀ n, (f (n + 1)).1 ^ p = (f n).1 := fun n => by
    have := congrArg Subtype.val (hf (Nat.le_add_right n 1))
    simpa [π] using this
  let x : PreTilt O p := ⟨fun n => (f n).1, hcomp⟩
  refine ⟨x, Perfection.ext fun n => ?_⟩
  change PreTilt.coeff n (P.eval x) = PreTilt.coeff n 0
  rw [map_zero, ← Polynomial.eval₂_at_apply]
  obtain ⟨y, hy, h⟩ := (f n).2
  have hx : PreTilt.coeff n x = (f n).1 := rfl
  rw [hx, h]
  exact eval₂_pow_p_pow P _ _ y hy

end Roots

theorem isAlgClosed_of_monic_root (A L : Type*) [CommRing A] [IsDomain A] [Field L] [Algebra A L]
    [IsFractionRing A L] (h : ∀ P : A[X], P.Monic → P.natDegree ≠ 0 → ∃ x, P.eval x = 0) :
    IsAlgClosed L := by
  refine IsAlgClosed.of_exists_root _ fun g hg hirr => ?_
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) g
  set q := IsLocalization.integerNormalization (nonZeroDivisors A) g
  have hinj := IsFractionRing.injective A L
  have hb0 : algebraMap A L b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hq' : q.map (algebraMap A L) = C (algebraMap A L b) * g := by
    rw [hq, Algebra.smul_def]; rfl
  have hdeg : q.natDegree = g.natDegree := by
    rw [← Polynomial.natDegree_map_eq_of_injective hinj, hq', Polynomial.natDegree_C_mul hb0]
  have hpos : 0 < q.natDegree := hdeg ▸ hirr.natDegree_pos
  have hq0 : q ≠ 0 := by rintro h0; rw [h0] at hpos; simp at hpos
  have hlc : algebraMap A L q.leadingCoeff ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; exact Polynomial.leadingCoeff_ne_zero.mpr hq0
  obtain ⟨r, hr⟩ := h _ (Polynomial.monic_integralNormalization hq0)
    (by rw [Polynomial.natDegree_integralNormalization]; exact hpos.ne')
  refine ⟨algebraMap A L r / algebraMap A L q.leadingCoeff, ?_⟩
  have h1 := Polynomial.integralNormalization_eval₂_leadingCoeff_mul (p := q) hpos
    (algebraMap A L) (algebraMap A L r / algebraMap A L q.leadingCoeff)
  rw [mul_div_cancel₀ _ hlc, Polynomial.eval₂_at_apply, hr, map_zero, ← Polynomial.eval_map, hq',
    Polynomial.eval_mul, Polynomial.eval_C] at h1
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ hlc))).resolve_left
    hb0

section Val

variable {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O] {p : ℕ} [Fact p.Prime]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

noncomputable def sharpRoot (x : PreTilt O p) (n : ℕ) : O :=
  (((_root_.frobeniusEquiv (PreTilt O p) p).symm)^[n] x).untilt

omit [IsDomain O] [ValuationRing O] in
theorem sharpRoot_pow_succ (x : PreTilt O p) (n : ℕ) :
    sharpRoot x (n + 1) ^ p = sharpRoot x n := by
  rw [sharpRoot, sharpRoot, Function.iterate_succ_apply', ← map_pow, ← frobenius_def,
    frobenius_apply_frobeniusEquiv_symm]

omit [IsDomain O] [ValuationRing O] in
theorem sharpRoot_pow (x : PreTilt O p) (n : ℕ) : sharpRoot x n ^ p ^ n = x.untilt :=
  PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x n

omit [IsDomain O] [ValuationRing O] in
theorem mk_sharpRoot (x : PreTilt O p) (n : ℕ) :
    Ideal.Quotient.mk (span {(p : O)}) (sharpRoot x n) = PreTilt.coeff n x := by
  rw [sharpRoot, PreTilt.mk_untilt_eq_coeff_zero]
  have := PreTilt.coeff_iterate_frobeniusEquiv_symm 0 n x
  rw [zero_add] at this
  exact this

theorem dvd_of_untilt_dvd {x y : PreTilt O p} (h : x.untilt ∣ y.untilt) : x ∣ y := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hdvd : ∀ n, sharpRoot x n ∣ sharpRoot y n := by
    intro n
    rw [← IsIntegrallyClosed.pow_dvd_pow_iff (pow_ne_zero n hp0), sharpRoot_pow, sharpRoot_pow]
    exact h
  by_cases hy : y.untilt = 0
  · have : y = 0 := by
      refine Perfection.ext fun n => ?_
      change PreTilt.coeff n y = PreTilt.coeff n 0
      have h0 : sharpRoot y n = 0 := by
        have := sharpRoot_pow y n
        rw [hy] at this
        exact eq_zero_of_pow_eq_zero this
      rw [← mk_sharpRoot, h0, map_zero, map_zero]
    rw [this]
    exact dvd_zero _
  have hsne : ∀ n, sharpRoot x n ≠ 0 := by
    intro n h0
    apply hy
    rw [← sharpRoot_pow x n, h0, zero_pow (pow_ne_zero _ hp0), zero_dvd_iff] at h
    exact h
  choose e he using hdvd
  have hcomp : ∀ n, e (n + 1) ^ p = e n := by
    intro n
    have h2 := sharpRoot_pow_succ y n
    rw [he (n + 1), he n, mul_pow, sharpRoot_pow_succ] at h2
    exact mul_left_cancel₀ (hsne n) h2
  let z : PreTilt O p := ⟨fun n => Ideal.Quotient.mk _ (e n), fun n => by
    simp only [← map_pow, hcomp]⟩
  refine ⟨z, Perfection.ext fun n => ?_⟩
  change PreTilt.coeff n y = PreTilt.coeff n (x * z)
  rw [map_mul, ← mk_sharpRoot, ← mk_sharpRoot, he n, map_mul]
  rfl

theorem dvd_total_preTilt (x y : PreTilt O p) : x ∣ y ∨ y ∣ x :=
  (ValuationRing.dvd_total x.untilt y.untilt).imp dvd_of_untilt_dvd dvd_of_untilt_dvd

end Val

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

theorem isAlgClosed_tilt_and_valuationRing :
    ∀ (l : ℕ) [Fact l.Prime], IsAlgClosed (Cb l) ∧ ValuationRing (OCb l) := by
  intro l _
  refine ⟨isAlgClosed_of_monic_root (OCb l) (Cb l) fun P hP hd =>
    exists_root_preTilt (PadicComplex l) hP hd, ?_⟩
  haveI : IsAdicComplete (span {((l : ℕ) : OC l)}) (OC l) := by
    open scoped Formalism.Per in infer_instance
  rw [ValuationRing.iff_dvd_total]
  exact ⟨fun x y => dvd_total_preTilt x y⟩

end GlobalTheory.TiltAlgClosed
