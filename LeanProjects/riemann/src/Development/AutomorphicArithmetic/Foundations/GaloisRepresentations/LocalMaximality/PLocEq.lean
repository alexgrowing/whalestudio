import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverRingLocalizationChart

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section LocEqAux
variable {L : Type} [Field L] [Algebra ℂ L]

private def locRes {R B : Subalgebra ℂ L} (h : R ≤ B) (e : B →ₐ[ℂ] ℂ) : R →ₐ[ℂ] ℂ :=
  e.comp (Subalgebra.inclusion h)

private lemma loc_val_eq {R B : Subalgebra ℂ L} (h : R ≤ B) (e : B →ₐ[ℂ] ℂ)
    (hB : B ≤ loc R (locRes h e)) :
    loc B e = loc R (locRes h e) ∧ ∀ v c, Val B e v c ↔ Val R (locRes h e) v c := by
  have key : ∀ {b v : L} (hb : b ∈ B) (hbv : b * v ∈ B),
      ∃ t : L, ∃ (ht : t ∈ B), e ⟨t, ht⟩ ≠ 0 ∧ t * b ∈ R ∧ t * b * v ∈ R := by
    intro b v hb hbv
    obtain ⟨⟨r, hr⟩, hr0, hrb⟩ := hB hb
    obtain ⟨⟨r', hr'⟩, hr'0, hr'bv⟩ := hB hbv
    refine ⟨r' * r, B.mul_mem (h hr') (h hr), ?_, ?_, ?_⟩
    · rw [show (⟨r' * r, B.mul_mem (h hr') (h hr)⟩ : B) = ⟨r', h hr'⟩ * ⟨r, h hr⟩ from rfl, map_mul]
      exact mul_ne_zero hr'0 hr0
    · rw [mul_assoc]
      exact R.mul_mem hr' hrb
    · have hre : r' * r * b * v = r * (r' * (b * v)) := by ring
      rw [hre]
      exact R.mul_mem hr hr'bv
  refine ⟨le_antisymm ?_ ?_, fun v c => ⟨?_, ?_⟩⟩
  · rintro v ⟨⟨b, hb⟩, hb0, hbv⟩
    obtain ⟨t, ht, ht0, htb, htbv⟩ := key hb hbv
    refine ⟨⟨t * b, htb⟩, ?_, htbv⟩
    show e ⟨t * b, h htb⟩ ≠ 0
    rw [show (⟨t * b, h htb⟩ : B) = ⟨t, ht⟩ * ⟨b, hb⟩ from rfl, map_mul]
    exact mul_ne_zero ht0 hb0
  · rintro v ⟨⟨r, hr⟩, hr0, hrv⟩
    exact ⟨⟨r, h hr⟩, hr0, h hrv⟩
  · rintro ⟨b, hb, hbv, hb0, hval⟩
    obtain ⟨t, ht, ht0, htb, htbv⟩ := key hb hbv
    refine ⟨t * b, htb, htbv, ?_, ?_⟩
    · show e ⟨t * b, h htb⟩ ≠ 0
      rw [show (⟨t * b, h htb⟩ : B) = ⟨t, ht⟩ * ⟨b, hb⟩ from rfl, map_mul]
      exact mul_ne_zero ht0 hb0
    · show e ⟨t * b * v, h htbv⟩ = e ⟨t * b, h htb⟩ * c
      rw [show (⟨t * b * v, h htbv⟩ : B) = ⟨t, ht⟩ * ⟨b * v, hbv⟩ from Subtype.ext (mul_assoc _ _ _),
        show (⟨t * b, h htb⟩ : B) = ⟨t, ht⟩ * ⟨b, hb⟩ from rfl, map_mul, map_mul, hval, mul_assoc]
  · rintro ⟨r, hr, hrv, hr0, hval⟩
    exact ⟨r, h hr, h hrv, hr0, hval⟩

end LocEqAux

section LocEqAux2

private lemma mem_rB_of {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L]
    [IsScalarTower ℂ F L] {d : ℕ} (x : Fin (d + 1) → F) (I : Finset (Fin (d + 1))) {f : F}
    (hf : f ∈ rA ℂ x I) : algebraMap F L f ∈ rB ℂ L x I := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  have hx : algebraMap F L f = algebraMap (rA ℂ x I) L ⟨f, hf⟩ := rfl
  rw [hx]
  exact isIntegral_algebraMap

private lemma div_mem_rA {F : Type} [Field F] [Algebra ℂ F] {d : ℕ} (x : Fin (d + 1) → F)
    {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (j : Fin (d + 1)) :
    x j / x i ∈ rA ℂ x I :=
  Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

end LocEqAux2

theorem UpperTheory.Gal.productCup_of_system.locEq_of :
    ValBasic → RYBasic → LocEq := by
  intro hV hY F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY0 I J i hi e
  obtain ⟨hRY0, -, hmono, h4, h5⟩ := hY F K K' d x j2 hY0
  have hRB : rB ℂ K' (xv x) {i} ≤ RY (xv x) j2 I J := by
    have hle := hmono {i} I ∅ J (Finset.singleton_subset_iff.mpr hi) (Finset.empty_subset _)
    rwa [hRY0] at hle
  obtain ⟨hRloc, -, -, hinv⟩ := hV K' (rB ℂ K' (xv x) {i}) (locRes hRB e)
  obtain ⟨j, hj⟩ := hY0.cov i (locRes hRB e)
  have hIB : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J := le_sup_left
  have hR2B : R2 (xv x) j2 J ≤ RY (xv x) j2 I J := le_sup_right
  have unit_lemma : ∀ {y w w' : K'}, w ∈ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) →
      w' ∈ RY (xv x) j2 I J → w * w' = 1 → y * w ∈ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) →
      y ∈ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    intro y w w' hw hw' hww hyw
    obtain ⟨⟨b, hbR⟩, hb0, hbw⟩ := hw
    have hne : locRes hRB e ⟨b * w, hbw⟩ ≠ 0 := by
      intro h0
      have hprod : e ⟨b * w, hRB hbw⟩ * e ⟨w', hw'⟩ = e ⟨b, hRB hbR⟩ := by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        show b * w * w' = b
        rw [mul_assoc, hww, mul_one]
      rw [show e ⟨b * w, hRB hbw⟩ = 0 from h0, zero_mul] at hprod
      exact hb0 hprod.symm
    have hval : Val (rB ℂ K' (xv x) {i}) (locRes hRB e) w
        (locRes hRB e ⟨b * w, hbw⟩ / locRes hRB e ⟨b, hbR⟩) := by
      refine ⟨b, hbR, hbw, hb0, ?_⟩
      field_simp
    obtain ⟨hw0, hwinv⟩ := hinv w _ hval (div_ne_zero hne hb0)
    have hy : y = (y * w) * w⁻¹ := by field_simp
    rw [hy]
    exact Subalgebra.mul_mem _ hyw hwinv
  have hI : rB ℂ K' (xv x) I ≤ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    intro y hy
    obtain ⟨N, hN⟩ := ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K' d (xv x) hY0.covY I i hi).2 y).1 hy
    refine unit_lemma (w := algebraMap F K' (∏ a ∈ I, xv x a / xv x i) ^ N)
      (w' := algebraMap F K' (∏ a ∈ I, xv x i / xv x a) ^ N) ?_ ?_ ?_ (hRloc hN)
    · exact hRloc (Subalgebra.pow_mem _ (mem_rB_of (L := K') (xv x) {i}
        (Subalgebra.prod_mem _ (fun a _ => div_mem_rA (xv x) (Finset.mem_singleton_self i) a))) N)
    · exact hIB (Subalgebra.pow_mem _ (mem_rB_of (L := K') (xv x) I
        (Subalgebra.prod_mem _ (fun a ha => div_mem_rA (xv x) ha i))) N)
    · rw [← mul_pow, ← map_mul, ← Finset.prod_mul_distrib]
      rw [Finset.prod_eq_one (fun a _ => by
        rw [div_mul_div_comm, mul_comm (xv x a), div_self (mul_ne_zero (x i).ne_zero (x a).ne_zero)])]
      rw [map_one, one_pow]
  have hR2 : ∀ S : Finset (Fin (d + 1)), S ⊆ J →
      R2 (xv x) j2 (insert j S) ≤ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.insert_empty]
      exact hj
    | insert m S hmS ih =>
      intro hS y hy
      rw [Finset.insert_comm] at hy
      obtain ⟨N, hN⟩ := h5 (insert j S) j (Finset.mem_insert_self _ _) m y hy
      have hmJ : m ∈ J := hS (Finset.mem_insert_self _ _)
      refine unit_lemma (w := j2 (algebraMap F K (xv x m / xv x j)) ^ N)
        (w' := j2 (algebraMap F K (xv x j / xv x m)) ^ N) ?_ ?_ ?_
        (ih (fun a ha => hS (Finset.mem_insert_of_mem ha)) hN)
      · exact Subalgebra.pow_mem _ (hj (h4 {j} _ (mem_rB_of (L := K) (xv x) {j}
          (div_mem_rA (xv x) (Finset.mem_singleton_self j) m))).2) N
      · exact Subalgebra.pow_mem _ (hR2B (h4 J _ (mem_rB_of (L := K) (xv x) J
          (div_mem_rA (xv x) hmJ j))).2) N
      · rw [← mul_pow, ← map_mul, ← map_mul, div_mul_div_comm, mul_comm (xv x m),
          div_self (mul_ne_zero (x j).ne_zero (x m).ne_zero), map_one, map_one, one_pow]
  have hB : RY (xv x) j2 I J ≤ loc (rB ℂ K' (xv x) {i}) (locRes hRB e) := by
    refine le_trans (hmono I I J (insert j J) (subset_refl _) (Finset.subset_insert _ _)) ?_
    exact sup_le hI (hR2 J (subset_refl _))
  obtain ⟨h1, h2⟩ := loc_val_eq hRB e hB
  exact ⟨locRes hRB e, h1, h2⟩
