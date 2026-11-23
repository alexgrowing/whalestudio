import Mathlib

open PowerSeries

noncomputable section

namespace GlobalTheory.ChartRing

section Eval

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

theorem pow_dvd_sub_aeval_trunc (φ : A⟦X⟧ →ₐ[A] S) (n : ℕ) (f : A⟦X⟧) :
    φ X ^ n ∣ φ f - Polynomial.aeval (φ X) (trunc n f) := by
  have h1 : ∀ p : Polynomial A, φ (p : A⟦X⟧) = Polynomial.aeval (φ X) p := by
    intro p
    have : φ.comp (Polynomial.coeToPowerSeries.algHom A) = Polynomial.aeval (φ X) := by
      ext; simp
    simpa using DFunLike.congr_fun this p
  refine ⟨φ (mk fun i => coeff (i + n) f), ?_⟩
  conv_lhs => rw [f.eq_X_pow_mul_shift_add_trunc n]
  rw [← h1, ← map_pow, ← map_mul, ← map_sub]
  congr 1
  rw [← f.eq_X_pow_mul_shift_add_trunc n, sub_eq_iff_eq_add]
  exact f.eq_X_pow_mul_shift_add_trunc n

theorem aeval_sub_mem_pow {J : Ideal S} {s : S} (hs : s ∈ J) {n : ℕ} {p q : Polynomial A}
    (h : ∀ i < n, p.coeff i = q.coeff i) :
    Polynomial.aeval s p - Polynomial.aeval s q ∈ J ^ n := by
  have : (Polynomial.X : Polynomial A) ^ n ∣ p - q :=
    Polynomial.X_pow_dvd_iff.2 fun i hi => by simp [h i hi]
  obtain ⟨r, hr⟩ := this
  rw [← map_sub, hr, map_mul, map_pow, Polynomial.aeval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hs n)

def evalMod (A : Type*) [CommRing A] [Algebra A S] (J : Ideal S) {s : S} (hs : s ∈ J) (n : ℕ) :
    A⟦X⟧ →ₐ[A] S ⧸ J ^ n where
  toFun f := Ideal.Quotient.mk _ (Polynomial.aeval s (trunc n f))
  map_one' := by
    rw [← map_one (Ideal.Quotient.mk (J ^ n)), Ideal.Quotient.eq,
      ← map_one (Polynomial.aeval (R := A) s)]
    refine aeval_sub_mem_pow hs fun i hi => ?_
    simp [coeff_trunc, hi, Polynomial.coeff_one, coeff_one]
  map_mul' f g := by
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq]
    refine aeval_sub_mem_pow hs fun i hi => ?_
    rw [coeff_trunc, if_pos hi, coeff_mul, Polynomial.coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    rw [coeff_trunc, coeff_trunc, if_pos (by omega), if_pos (by omega)]
  map_zero' := by simp
  map_add' f g := by simp
  commutes' a := by
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq,
      ← (Polynomial.aeval (R := A) s).commutes a]
    refine aeval_sub_mem_pow hs fun i hi => ?_
    simp [coeff_trunc, hi, Polynomial.coeff_C, coeff_C, PowerSeries.algebraMap_apply]

theorem factor_comp_evalMod (J : Ideal S) {s : S} (hs : s ∈ J) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hle)).comp (evalMod A J hs n) =
      evalMod A J hs m := by
  refine AlgHom.ext fun f => ?_
  change Ideal.Quotient.mk _ (Polynomial.aeval s (trunc n f)) =
    Ideal.Quotient.mk _ (Polynomial.aeval s (trunc m f))
  rw [Ideal.Quotient.eq]
  refine aeval_sub_mem_pow hs fun i hi => ?_
  rw [coeff_trunc, coeff_trunc, if_pos hi, if_pos (by omega)]

def evalAdic (A : Type*) [CommRing A] [Algebra A S] (J : Ideal S) [IsAdicComplete J S] {s : S}
    (hs : s ∈ J) : A⟦X⟧ →ₐ[A] S :=
  IsAdicComplete.liftAlgHom J (evalMod A J hs) (factor_comp_evalMod J hs)

variable (J : Ideal S) [IsAdicComplete J S] {s : S} (hs : s ∈ J)

theorem evalAdic_sub_aeval_trunc_mem (n : ℕ) (f : A⟦X⟧) :
    evalAdic A J hs f - Polynomial.aeval s (trunc n f) ∈ J ^ n := by
  rw [← Ideal.Quotient.eq]
  exact IsAdicComplete.mk_liftAlgHom J (evalMod A J hs) (factor_comp_evalMod J hs) n f

theorem eq_of_forall_sub_mem_pow {x y : S} (h : ∀ n, x - y ∈ J ^ n) : x = y := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun n => ?_
  rw [SModEq.zero]
  simpa using h n

@[simp] theorem evalAdic_X : evalAdic A J hs X = s := by
  refine eq_of_forall_sub_mem_pow J fun n => ?_
  have h1 := evalAdic_sub_aeval_trunc_mem J hs n (X : A⟦X⟧)
  have h2 : Polynomial.aeval s (trunc n (X : A⟦X⟧)) -
      Polynomial.aeval s (Polynomial.X : Polynomial A) ∈ J ^ n :=
    aeval_sub_mem_pow hs fun i hi => by
      simp [coeff_trunc, hi, coeff_X, Polynomial.coeff_X, eq_comm]
  simpa using add_mem h1 h2

@[simp] theorem evalAdic_C (a : A) : evalAdic A J hs (C a) = algebraMap A S a :=
  (evalAdic A J hs).commutes a

theorem algHom_ext_of_isHausdorff (J : Ideal S) [IsHausdorff J S] {φ ψ : A⟦X⟧ →ₐ[A] S}
    (hφ : φ X ∈ J) (h : φ X = ψ X) : φ = ψ := by
  refine AlgHom.ext fun f => ?_
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun n => ?_
  rw [SModEq.zero]
  have h1 := pow_dvd_sub_aeval_trunc φ n f
  have h2 := pow_dvd_sub_aeval_trunc ψ n f
  rw [← h] at h2
  have h3 : φ X ^ n ∣ φ f - ψ f := by simpa using dvd_sub h1 h2
  simpa using Ideal.mem_of_dvd _ h3 (Ideal.pow_mem_pow hφ n)

theorem eq_evalAdic (φ : A⟦X⟧ →ₐ[A] S) (h : φ X = s) : φ = evalAdic A J hs :=
  algHom_ext_of_isHausdorff J (h ▸ hs) (by simp [h])

end Eval

section Division

variable {A : Type*} [CommRing A]

theorem X_sub_C_dvd_sub_C (φ : A⟦X⟧ →ₐ[A] A) (f : A⟦X⟧) : X - C (φ X) ∣ f - C (φ f) := by
  have key : ∀ n, φ (mk fun i => coeff (i + n) f) =
      φ X * φ (mk fun i => coeff (i + (n + 1)) f) + coeff n f := by
    intro n
    have h := (mk fun i => coeff (i + n) f).eq_X_mul_shift_add_const
    have hC : ∀ a, φ (C a) = a := fun a => φ.commutes a
    rw [h, map_add, map_mul, hC]
    simp [add_assoc, add_comm 1 n]
  refine ⟨mk fun n => φ (mk fun i => coeff (i + (n + 1)) f), ?_⟩
  ext n
  cases n with
  | zero =>
    have h0 := key 0
    have : (mk fun i => coeff (i + 0) f) = f := by ext; simp
    rw [this] at h0
    simp only [sub_mul, map_sub, coeff_zero_C, coeff_C_mul, coeff_mk, coeff_zero_X_mul]
    rw [h0]; ring
  | succ n =>
    simp only [sub_mul, map_sub, coeff_C_mul, coeff_mk, coeff_succ_X_mul, coeff_succ_C]
    rw [key (n + 1)]; ring

theorem ker_eq_span_X_sub_C (φ : A⟦X⟧ →ₐ[A] A) :
    RingHom.ker φ = Ideal.span {X - C (φ X)} := by
  apply le_antisymm
  · intro f hf
    have h := X_sub_C_dvd_sub_C φ f
    rw [RingHom.mem_ker.1 hf] at h
    simpa [Ideal.mem_span_singleton] using h
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub]
    exact sub_eq_zero.2 (φ.commutes _).symm

end Division

section Complete

variable {A : Type*} [CommRing A] (I : Ideal A)

theorem map_C_sup_span_X :
    I.map (C : A →+* A⟦X⟧) ⊔ Ideal.span {X} = I.comap (constantCoeff (R := A)) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simpa using ha
    · simp [Ideal.span_singleton_le_iff_mem]
  · intro f hf
    rw [f.eq_X_mul_shift_add_const]
    exact add_mem
      (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf))

theorem mem_pow_comap_constantCoeff_iff (n : ℕ) (f : A⟦X⟧) :
    f ∈ I.comap (constantCoeff (R := A)) ^ n ↔ ∀ i, coeff i f ∈ I ^ (n - i) := by
  constructor
  · induction n generalizing f with
    | zero => simp
    | succ n ih =>
      intro hf
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf (fun a ha b hb i => ?_) (fun a b ha hb i => ?_)
      · rw [coeff_mul]
        refine sum_mem fun x hx => ?_
        have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
        have h1 := ih a ha x.1
        have h2 : coeff x.2 b ∈ I ^ (1 - x.2) := by
          rcases Nat.eq_zero_or_pos x.2 with h | h
          · rw [h]; simpa using hb
          · rw [show 1 - x.2 = 0 by omega]; simp
        have h3 := Ideal.mul_mem_mul h1 h2
        rw [← pow_add] at h3
        exact Ideal.pow_le_pow_right (by omega) h3
      · rw [map_add]; exact add_mem (ha i) (hb i)
  · intro h
    have hX : (X : A⟦X⟧) ∈ I.comap (constantCoeff (R := A)) := by simp
    rw [f.eq_X_pow_mul_shift_add_trunc n]
    refine add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hX n)) ?_
    rw [trunc_apply, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    refine sum_mem fun i hi => ?_
    have hi' : i < n := (Finset.mem_Ico.1 hi).2
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_monomial,
      monomial_eq_C_mul_X_pow]
    have h1 : C (coeff i f) ∈ I.comap (constantCoeff (R := A)) ^ (n - i) := by
      have := Ideal.mem_map_of_mem (C : A →+* A⟦X⟧) (h i)
      rw [Ideal.map_pow] at this
      refine Ideal.pow_right_mono ?_ _ this
      rw [← map_C_sup_span_X]; exact le_sup_left
    have h2 := Ideal.mul_mem_mul h1 (Ideal.pow_mem_pow hX i)
    rwa [← pow_add, Nat.sub_add_cancel hi'.le] at h2

theorem isHausdorff_comap_constantCoeff [IsHausdorff I A] :
    IsHausdorff (I.comap (constantCoeff (R := A))) A⟦X⟧ where
  haus' f hf := by
    ext i
    refine IsHausdorff.haus' (I := I) _ fun n => ?_
    have := hf (n + i)
    rw [SModEq.zero] at this ⊢
    simp only [smul_eq_mul, Ideal.mul_top] at this ⊢
    simpa using (mem_pow_comap_constantCoeff_iff I _ f).1 this i

theorem isPrecomplete_comap_constantCoeff [IsPrecomplete I A] :
    IsPrecomplete (I.comap (constantCoeff (R := A))) A⟦X⟧ where
  prec' F hF := by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_pow_comap_constantCoeff_iff] at hF ⊢
    have : ∀ i, ∃ L : A, ∀ n, coeff i (F (n + i)) - L ∈ I ^ n := by
      intro i
      have := IsPrecomplete.prec' (I := I) (fun n => coeff i (F (n + i))) (by
        intro m n h
        simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
        simpa using hF (show m + i ≤ n + i by omega) i)
      simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using this
    choose L hL using this
    refine ⟨mk L, fun n i => ?_⟩
    rcases le_or_gt i n with h | h
    · have := hL i (n - i)
      rw [Nat.sub_add_cancel h] at this
      simpa using this
    · rw [show n - i = 0 by omega]; simp

theorem isAdicComplete_comap_constantCoeff [IsAdicComplete I A] :
    IsAdicComplete (I.comap (constantCoeff (R := A))) A⟦X⟧ :=
  { isHausdorff_comap_constantCoeff I, isPrecomplete_comap_constantCoeff I with }

theorem map_comap_constantCoeff_le {S : Type*} [CommRing S] [Algebra A S] (J : Ideal S)
    (φ : A⟦X⟧ →ₐ[A] S) (hI : I.map (algebraMap A S) ≤ J) (hX : φ X ∈ J) :
    (I.comap (constantCoeff (R := A))).map φ ≤ J := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, f.eq_X_mul_shift_add_const, map_add, map_mul]
  refine add_mem (Ideal.mul_mem_right _ _ hX) ?_
  have : φ (C (constantCoeff f)) = algebraMap A S (constantCoeff f) := φ.commutes _
  rw [this]
  exact hI (Ideal.mem_map_of_mem _ hf)

theorem continuous_adicTopology_of_map_le {S : Type*} [CommRing S] (J : Ideal S) (φ : A →+* S)
    (h : I.map φ ≤ J) : @Continuous A S I.adicTopology J.adicTopology φ := by
  letI : WithIdeal A := ⟨I⟩
  letI : WithIdeal S := ⟨J⟩
  exact (WithIdeal.uniformContinuous_of_map_le (f := φ) h).continuous

end Complete

end GlobalTheory.ChartRing
