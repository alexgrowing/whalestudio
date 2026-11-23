import Mathlib
open NumberField

namespace PositivityTheory.Xgn.MonogenicSeparating

open Polynomial TensorProduct

private theorem ringHom_aeval_int_eq_eval_map_lemma {O B : Type} [CommRing O] [CommRing B] (φ : O →+* B)
    (a : O) (h : ℤ[X]) : φ (aeval a h) = (h.map (Int.castRingHom B)).eval (φ a) := by
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval_map]
  congr 1
  exact RingHom.ext_int _ _

private theorem exists_finite_subalgebra_pi_of_ringHom_lemma_2 {O V S : Type} [CommRing O] [Module.Finite ℤ O]
    [CommRing V] (F : O →+* (S → V)) :
    ∃ R : Subalgebra V (S → V), Module.Finite V R ∧ (∀ a, F a ∈ R) ∧
      ∀ x ∈ R, x ∈ Submodule.span V (Set.range F) := by
  let L : V ⊗[ℤ] O →ₐ[V] (S → V) :=
    Algebra.TensorProduct.lift (Algebra.ofId V (S → V)) F.toIntAlgHom (fun _ _ => Commute.all _ _)
  refine ⟨L.range, Module.Finite.of_surjective L.rangeRestrict.toLinearMap
    L.rangeRestrict_surjective, fun a => (AlgHom.mem_range L).mpr ⟨1 ⊗ₜ[ℤ] a, ?_⟩, ?_⟩
  · simp only [L]
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    all_goals rfl
  · intro x hx
    obtain ⟨t, rfl⟩ := (AlgHom.mem_range L).mp hx
    clear hx
    induction t using TensorProduct.induction_on with
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | tmul v a =>
      simp only [L]
      rw [Algebra.TensorProduct.lift_tmul]
      show algebraMap V (S → V) v * F a ∈ _
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ v (Submodule.subset_span ⟨a, rfl⟩)
    | add t₁ t₂ h₁ h₂ =>
      rw [map_add]
      exact Submodule.add_mem _ h₁ h₂

theorem sep_poly (E : Type) [Field E] [NumberField E] (P : Ideal (𝓞 E)) (hP : P.IsPrime)
    (a : 𝓞 E) : ∃ h : ℤ[X], aeval a h ∈ P ∧ aeval a (derivative h) ∉ P := by
  by_cases hbot : P = ⊥
  · subst hbot
    have hint : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral (R := ℤ) a
    refine ⟨minpoly ℤ a, by rw [minpoly.aeval]; exact Ideal.zero_mem _, ?_⟩
    rw [Ideal.mem_bot]
    intro h0
    have hdvd := minpoly.isIntegrallyClosed_dvd hint h0
    have hpos := minpoly.natDegree_pos hint
    have hne : derivative (minpoly ℤ a) ≠ 0 := by
      intro hd
      have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hd
      omega
    have hle := Polynomial.natDegree_le_of_dvd hdvd hne
    have hlt := Polynomial.natDegree_derivative_lt (p := minpoly ℤ a) (by omega)
    omega
  · haveI : P.IsMaximal := hP.isMaximal hbot
    letI : Field (𝓞 E ⧸ P) := Ideal.Quotient.field P
    haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hbot
    letI : Fintype (𝓞 E ⧸ P) := Fintype.ofFinite _
    refine ⟨X ^ Fintype.card (𝓞 E ⧸ P) - X, ?_, ?_⟩
    · rw [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_X, ← Ideal.Quotient.eq_zero_iff_mem,
        map_sub, map_pow, FiniteField.pow_card, sub_self]
    · rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.derivative_sub,
        Polynomial.derivative_X_pow, Polynomial.derivative_X]
      simp only [map_sub, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, map_one,
        map_natCast]
      rw [FiniteField.cast_card_eq_zero, zero_mul, zero_sub, neg_eq_zero]
      exact one_ne_zero

theorem ex_unif (E : Type) [Field E] [NumberField E] (P : Ideal (𝓞 E)) (hP : P.IsPrime) :
    ∃ π ∈ P, ∀ b ∈ P, ∃ t, t ∉ P ∧ π ∣ t * b := by
  by_cases hbot : P = ⊥
  · subst hbot
    refine ⟨0, Ideal.zero_mem _, fun b hb => ⟨1, ?_, ?_⟩⟩
    · rw [Ideal.mem_bot]
      exact one_ne_zero
    · rw [Ideal.mem_bot] at hb
      rw [hb, mul_zero]
  · obtain ⟨π, hπ1, hπ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ P hbot hP.ne_top 1
    rw [pow_one] at hπ1
    have hle : Ideal.span {π} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hπ1
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
    have hJP : ¬ J ≤ P := by
      intro hJ'
      apply hπ2
      have h2 : P ^ (1 + 1) = P * P := by rw [pow_succ, pow_one]
      have hmem : π ∈ Ideal.span {π} := Ideal.mem_span_singleton_self π
      rw [hJ] at hmem
      rw [h2]
      exact Ideal.mul_mono_right hJ' hmem
    obtain ⟨t, htJ, htP⟩ := SetLike.not_le_iff_exists.mp hJP
    refine ⟨π, hπ1, fun b hb => ⟨t, htP, ?_⟩⟩
    have hbt : b * t ∈ Ideal.span {π} := by
      rw [hJ]
      exact Ideal.mul_mem_mul hb htJ
    rw [Ideal.mem_span_singleton, mul_comm] at hbt
    exact hbt

theorem hom_eq {O B : Type} [CommRing O] [CommRing B] (P : Ideal O) (π : O)
    (hsep : ∀ a : O, ∃ h : ℤ[X], aeval a h ∈ P ∧ aeval a (derivative h) ∉ P)
    (hπ : ∀ b ∈ P, ∃ t, t ∉ P ∧ π ∣ t * b)
    (φ ψ : O →+* B) (h0 : φ π = 0) (h1 : ∀ b ∈ P, ψ b = 0) (h2 : ∀ b, b ∉ P → IsUnit (ψ b))
    (h3 : ∀ a, IsNilpotent (φ a - ψ a)) (a : O) : φ a = ψ a := by
  have hunit : ∀ b, b ∉ P → IsUnit (φ b) := by
    intro b hb
    have := (h3 b).isUnit_add_left_of_commute (h2 b hb) (Commute.all _ _)
    rwa [add_sub_cancel] at this
  have hP : ∀ b ∈ P, φ b = 0 := by
    intro b hb
    obtain ⟨t, ht, s, hs⟩ := hπ b hb
    have hts : φ t * φ b = 0 := by rw [← map_mul, hs, map_mul, h0, zero_mul]
    exact ((hunit t ht).mul_right_eq_zero).mp hts
  obtain ⟨h, hha, hhd⟩ := hsep a
  have e1 : (h.map (Int.castRingHom B)).eval (φ a) = 0 := by
    rw [← ringHom_aeval_int_eq_eval_map_lemma]
    exact hP _ hha
  have e2 : (h.map (Int.castRingHom B)).eval (ψ a) = 0 := by
    rw [← ringHom_aeval_int_eq_eval_map_lemma]
    exact h1 _ hha
  have hu : IsUnit ((derivative (h.map (Int.castRingHom B))).eval (ψ a)) := by
    rw [Polynomial.derivative_map, ← ringHom_aeval_int_eq_eval_map_lemma]
    exact h2 _ hhd
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  obtain ⟨w, hw⟩ := Polynomial.binomExpansion (h.map (Int.castRingHom B)) (ψ a) (φ a - ψ a)
  rw [add_sub_cancel, e1, e2, zero_add] at hw
  have hδ : φ a - ψ a = (φ a - ψ a) * (-(v * w) * (φ a - ψ a)) := by
    linear_combination (-v) * hw - (φ a - ψ a) * hv
  have key : ∀ k : ℕ, φ a - ψ a = (φ a - ψ a) * (-(v * w) * (φ a - ψ a)) ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, mul_one]
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ← ih]
      exact hδ
  obtain ⟨n, hn⟩ := h3 a
  have hkey := key n
  rw [mul_pow, hn, mul_zero, mul_zero] at hkey
  exact sub_eq_zero.mp hkey

theorem adjoin_top {O V R : Type} [CommRing O] [CommRing V] [IsLocalRing V] [CommRing R]
    [Algebra V R] [Module.Finite V R] (c : O →+* V) (φ : O →+* R)
    (hgen : Submodule.span V (Set.range φ) = ⊤) (π : O)
    (hπ0 : c π ∈ IsLocalRing.maximalIdeal V)
    (hsep : ∀ a : O, ∃ h : ℤ[X], aeval a h ∈ (IsLocalRing.maximalIdeal V).comap c ∧
      aeval a (derivative h) ∉ (IsLocalRing.maximalIdeal V).comap c)
    (hπ : ∀ b ∈ (IsLocalRing.maximalIdeal V).comap c, ∃ t,
      t ∉ (IsLocalRing.maximalIdeal V).comap c ∧ π ∣ t * b)
    (hnil : ∀ a, ∃ n, (φ a - algebraMap V R (c a)) ^ n ∈
      (IsLocalRing.maximalIdeal V).map (algebraMap V R)) :
    Algebra.adjoin V {φ π} = ⊤ := by
  have hgen1 : ∀ a : O, ∃ z : R, φ a - algebraMap V R (c a) - φ π * z ∈
      (IsLocalRing.maximalIdeal V).map (algebraMap V R) := by
    obtain ⟨I, hIdef⟩ : ∃ I : Ideal R,
        I = (IsLocalRing.maximalIdeal V).map (algebraMap V R) ⊔ Ideal.span {φ π} := ⟨_, rfl⟩
    have hJI : (IsLocalRing.maximalIdeal V).map (algebraMap V R) ≤ I := by
      rw [hIdef]
      exact le_sup_left
    have hπI : φ π ∈ I := by
      rw [hIdef]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    have hC0 : ((Ideal.Quotient.mk I).comp φ) π = 0 := by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hπI
    have hC1 : ∀ b ∈ (IsLocalRing.maximalIdeal V).comap c,
        ((Ideal.Quotient.mk I).comp ((algebraMap V R).comp c)) b = 0 := by
      intro b hb
      rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hJI (Ideal.mem_map_of_mem _ (Ideal.mem_comap.mp hb))
    have hC2 : ∀ b, b ∉ (IsLocalRing.maximalIdeal V).comap c →
        IsUnit (((Ideal.Quotient.mk I).comp ((algebraMap V R).comp c)) b) := by
      intro b hb
      have hcb : IsUnit (c b) := by
        by_contra hcon
        exact hb (Ideal.mem_comap.mpr
          ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hcon)))
      exact hcb.map ((Ideal.Quotient.mk I).comp (algebraMap V R))
    have hC3 : ∀ a, IsNilpotent (((Ideal.Quotient.mk I).comp φ) a -
        ((Ideal.Quotient.mk I).comp ((algebraMap V R).comp c)) a) := by
      intro a
      obtain ⟨n, hn⟩ := hnil a
      refine ⟨n, ?_⟩
      simp only [RingHom.comp_apply]
      rw [← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact hJI hn
    intro a
    have hI := PositivityTheory.Xgn.MonogenicSeparating.hom_eq
      ((IsLocalRing.maximalIdeal V).comap c) π hsep hπ _ _ hC0 hC1 hC2 hC3 a
    simp only [RingHom.comp_apply] at hI
    rw [Ideal.Quotient.eq, hIdef] at hI
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hI
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    refine ⟨w, ?_⟩
    have hw : φ a - algebraMap V R (c a) - φ π * w = y := by
      rw [← hyz]
      ring
    rw [hw]
    exact hy
  have hdecomp : ∀ y : R, ∃ v : V, ∃ z : R, y - algebraMap V R v - φ π * z ∈
      (IsLocalRing.maximalIdeal V).map (algebraMap V R) := by
    intro y
    have hy : y ∈ Submodule.span V (Set.range φ) := by
      rw [hgen]
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨z, hz⟩ := hgen1 a
      exact ⟨c a, z, hz⟩
    | zero => exact ⟨0, 0, by simp⟩
    | add x₁ x₂ _ _ hx₁ hx₂ =>
      obtain ⟨v₁, z₁, h₁⟩ := hx₁
      obtain ⟨v₂, z₂, h₂⟩ := hx₂
      refine ⟨v₁ + v₂, z₁ + z₂, ?_⟩
      have h₁₂ := Ideal.add_mem _ h₁ h₂
      convert h₁₂ using 1
      rw [map_add]
      ring
    | smul r x _ hx =>
      obtain ⟨v, z, h⟩ := hx
      refine ⟨r * v, algebraMap V R r * z, ?_⟩
      have h' := Ideal.mul_mem_left _ (algebraMap V R r) h
      convert h' using 1
      rw [Algebra.smul_def, map_mul]
      ring
  obtain ⟨n, hn⟩ := hnil π
  have hπn : (φ π) ^ n ∈ (IsLocalRing.maximalIdeal V).map (algebraMap V R) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
    have he : Ideal.Quotient.mk ((IsLocalRing.maximalIdeal V).map (algebraMap V R)) (φ π) =
        Ideal.Quotient.mk ((IsLocalRing.maximalIdeal V).map (algebraMap V R))
          (φ π - algebraMap V R (c π)) := by
      rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hπ0), sub_zero]
    rw [he, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hn
  obtain ⟨S, hSdef⟩ : ∃ S : Submodule V R, S = Subalgebra.toSubmodule (Algebra.adjoin V {φ π}) ⊔
      (IsLocalRing.maximalIdeal V) • (⊤ : Submodule V R) := ⟨_, rfl⟩
  have hJS : ∀ x ∈ (IsLocalRing.maximalIdeal V).map (algebraMap V R), x ∈ S := by
    intro x hx
    rw [hSdef]
    refine Submodule.mem_sup_right ?_
    rw [Ideal.smul_top_eq_map]
    exact hx
  have hAS : ∀ x ∈ Algebra.adjoin V {φ π}, x ∈ S := by
    intro x hx
    rw [hSdef]
    exact Submodule.mem_sup_left ((Subalgebra.mem_toSubmodule _).mpr hx)
  have hstep : ∀ k : ℕ, ∀ x : R, ∃ s ∈ S, ∃ y : R, x = s + (φ π) ^ k * y := by
    intro k
    induction k with
    | zero =>
      intro x
      exact ⟨0, S.zero_mem, x, by rw [pow_zero, one_mul, zero_add]⟩
    | succ k ih =>
      intro x
      obtain ⟨s, hs, y, rfl⟩ := ih x
      obtain ⟨v, z, hvz⟩ := hdecomp y
      refine ⟨s + (φ π) ^ k * algebraMap V R v +
        (φ π) ^ k * (y - algebraMap V R v - φ π * z), ?_, z, by ring⟩
      refine S.add_mem (S.add_mem hs (hAS _ ?_)) (hJS _ (Ideal.mul_mem_left _ _ hvz))
      exact Subalgebra.mul_mem _
        (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton V _) _)
        (Subalgebra.algebraMap_mem _ _)
  have htop : (⊤ : Submodule V R) ≤ Subalgebra.toSubmodule (Algebra.adjoin V {φ π}) ⊔
      (IsLocalRing.maximalIdeal V) • (⊤ : Submodule V R) := by
    rw [← hSdef]
    intro x _
    obtain ⟨s, hs, y, rfl⟩ := hstep n x
    exact S.add_mem hs (hJS _ (Ideal.mul_mem_right _ _ hπn))
  have hjac : IsLocalRing.maximalIdeal V ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac htop
  rw [eq_top_iff]
  intro x _
  exact (Subalgebra.mem_toSubmodule _).mp (hle Submodule.mem_top)

theorem ex_poly (E : Type) [Field E] [NumberField E] (V : Type) [CommRing V] [IsLocalRing V]
    (S : Type) [Fintype S] (e : S → (𝓞 E →+* V)) (c : 𝓞 E →+* V)
    (hS : ∀ s a, ¬ IsUnit (e s a - c a)) :
    ∃ π : 𝓞 E, ∀ a : 𝓞 E, ∃ g : V[X], ∀ s, e s a = g.eval (e s π) := by
  have hP : ((IsLocalRing.maximalIdeal V).comap c).IsPrime := Ideal.comap_isPrime c _
  obtain ⟨π, hπP, hπ⟩ := PositivityTheory.Xgn.MonogenicSeparating.ex_unif E _ hP
  obtain ⟨R, hRfin, hFR, hRspan⟩ := exists_finite_subalgebra_pi_of_ringHom_lemma_2 (Pi.ringHom e)
  haveI := hRfin
  obtain ⟨φ, hφ⟩ : ∃ φ : 𝓞 E →+* R, ∀ a s, (φ a : S → V) s = e s a :=
    ⟨(Pi.ringHom e).codRestrict R hFR, fun a s => rfl⟩
  have hgen : Submodule.span V (Set.range φ) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have key : ∀ y (hy : y ∈ Submodule.span V (Set.range (Pi.ringHom e))),
        ∃ h : y ∈ R, (⟨y, h⟩ : R) ∈ Submodule.span V (Set.range φ) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hy
        exact ⟨hFR a, Submodule.subset_span ⟨a, Subtype.ext (funext fun s => hφ a s)⟩⟩
      | zero => exact ⟨R.zero_mem, Submodule.zero_mem _⟩
      | add y₁ y₂ _ _ h₁ h₂ =>
        obtain ⟨m₁, s₁⟩ := h₁
        obtain ⟨m₂, s₂⟩ := h₂
        exact ⟨R.add_mem m₁ m₂, Submodule.add_mem _ s₁ s₂⟩
      | smul r y _ h =>
        obtain ⟨m, s⟩ := h
        exact ⟨R.smul_mem m r, Submodule.smul_mem _ r s⟩
    obtain ⟨_, h⟩ := key x (hRspan x hx)
    exact h
  have hprod : ∀ a, ∏ s', (φ a - algebraMap V R (e s' a)) = 0 := by
    intro a
    apply Subtype.ext
    funext s
    rw [SubmonoidClass.coe_finset_prod, Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hφ])
  have hnil : ∀ a, ∃ n, (φ a - algebraMap V R (c a)) ^ n ∈
      (IsLocalRing.maximalIdeal V).map (algebraMap V R) := by
    intro a
    refine ⟨Fintype.card S, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Finset.card_univ, ← Finset.prod_const, map_prod,
      ← map_zero (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal V).map (algebraMap V R))),
      ← hprod a, map_prod]
    apply Finset.prod_congr rfl
    intro s _
    rw [Ideal.Quotient.eq]
    have hd : φ a - algebraMap V R (c a) - (φ a - algebraMap V R (e s a)) =
        algebraMap V R (e s a - c a) := by
      rw [map_sub]
      ring
    rw [hd]
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hS s a
  have hadj := PositivityTheory.Xgn.MonogenicSeparating.adjoin_top c φ hgen π
    (Ideal.mem_comap.mp hπP) (fun a => PositivityTheory.Xgn.MonogenicSeparating.sep_poly E _ hP a)
    hπ hnil
  refine ⟨π, fun a => ?_⟩
  have ha : φ a ∈ Algebra.adjoin V {φ π} := by
    rw [hadj]
    exact Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨g, hg⟩ := (AlgHom.mem_range _).mp ha
  refine ⟨g, fun s => ?_⟩
  have key := Polynomial.aeval_algHom_apply ((Pi.evalAlgHom V (fun _ : S => V) s).comp R.val)
    (φ π) g
  rw [hg] at key
  simp only [AlgHom.comp_apply, Subalgebra.coe_val, Pi.evalAlgHom_apply, hφ,
    Polynomial.coe_aeval_eq_eval] at key
  exact key.symm

theorem ex_idem {O V ι : Type} [CommRing O] [CommRing V] [IsLocalRing V] [Fintype ι]
    (e : ι → (O →+* V)) (σ : ι) (T : Subalgebra V (ι → V)) (hT : ∀ a, (fun s => e s a) ∈ T) :
    ∃ u ∈ T, (∀ s, (∀ a, ¬ IsUnit (e s a - e σ a)) → u s = 1) ∧
      ∀ s, (∃ a, IsUnit (e s a - e σ a)) → u s = 0 := by
  classical
  have hA0 : ∀ s, ∃ a, (∃ b, IsUnit (e s b - e σ b)) → IsUnit (e s a - e σ a) := by
    intro s
    by_cases h : ∃ b, IsUnit (e s b - e σ b)
    · obtain ⟨b, hb⟩ := h
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose A hA using hA0
  obtain ⟨K, hK⟩ : ∃ K : Finset ι, ∀ t, t ∈ K ↔ ∀ a, ¬ IsUnit (e t a - e σ a) :=
    ⟨Finset.univ.filter (fun t => ∀ a, ¬ IsUnit (e t a - e σ a)), fun t => by simp⟩
  obtain ⟨y, hyT, hy⟩ : ∃ y : ι → (ι → V), (∀ s, y s ∈ T) ∧
      ∀ s r, y s r = ∏ t ∈ K, (e r (A s) - e t (A s)) :=
    ⟨fun s => ∏ t ∈ K, ((fun r => e r (A s)) - algebraMap V (ι → V) (e t (A s))),
      fun s => prod_mem fun t _ => T.sub_mem (hT (A s)) (T.algebraMap_mem _),
      fun s r => by simp [Finset.prod_apply]⟩
  have hy0 : ∀ s r, r ∈ K → y s r = 0 := by
    intro s r hr
    rw [hy]
    exact Finset.prod_eq_zero hr (sub_self _)
  have hyu : ∀ r, r ∉ K → IsUnit (y r r) := by
    intro r hr
    have hex : ∃ a, IsUnit (e r a - e σ a) := by
      by_contra hcon
      push_neg at hcon
      exact hr ((hK r).mpr hcon)
    have hu := hA r hex
    rw [hy, IsUnit.prod_iff]
    intro t ht
    have htK := (hK t).mp ht (A r)
    have hsum : (e r (A r) - e t (A r)) + (e t (A r) - e σ (A r)) = e r (A r) - e σ (A r) := by
      ring
    rw [← hsum] at hu
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h | h
    · exact h
    · exact absurd h htK
  refine ⟨∏ s ∈ Finset.univ.filter (fun s => s ∉ K), (1 - Ring.inverse (y s s) • y s),
    prod_mem fun s _ => T.sub_mem T.one_mem (T.smul_mem (hyT s) _), ?_, ?_⟩
  · intro r hr
    have hrK : r ∈ K := (hK r).mpr hr
    rw [Finset.prod_apply]
    apply Finset.prod_eq_one
    intro s _
    simp [hy0 s r hrK]
  · intro r hr
    have hrK : r ∉ K := fun h => by
      obtain ⟨a, ha⟩ := hr
      exact (hK r).mp h a ha
    rw [Finset.prod_apply]
    apply Finset.prod_eq_zero (i := r) (by simp [hrK])
    simp [Ring.inverse_mul_cancel _ (hyu r hrK)]

end PositivityTheory.Xgn.MonogenicSeparating

theorem PositivityTheory.Xgn.exists_monogenic_separating : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (emb : (E →+* C) → (𝓞 E →+* V)), (∀ s (a : 𝓞 E), algebraMap V C (emb s a) = s (a : E)) → Nat.card (E →+* C) = Module.finrank ℚ E → ∀ σ : E →+* C, ∃ π : 𝓞 E, (∀ s s' : E →+* C, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → (∀ a, ¬ IsUnit (emb s' a - emb σ a)) → emb s π = emb s' π → s = s') ∧ ∀ f : (E →+* C) → V, (∀ s, (∃ a, IsUnit (emb s a - emb σ a)) → f s = 0) → ((∃ g : Polynomial V, ∀ s, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span V (Set.range fun a : 𝓞 E => fun s => emb s a)) := by
  intro E _ _ V C _ _ _ _ _ _ _ emb hemb hcard σ
  classical
  haveI : IsLocalRing V := ValuationRing.isLocalRing V
  haveI : Finite (E →+* C) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact (Module.finrank_pos (R := ℚ) (M := E)).ne')
  letI : Fintype (E →+* C) := Fintype.ofFinite _
  obtain ⟨π, hπ⟩ := PositivityTheory.Xgn.MonogenicSeparating.ex_poly E V
    {s : E →+* C // ∀ a, ¬ IsUnit (emb s a - emb σ a)} (fun s => emb s.1) (emb σ)
    (fun s a => s.2 a)
  refine ⟨π, ?_, ?_⟩
  · intro s s' hs hs' heq
    have hagree : ∀ a : 𝓞 E, s (a : E) = s' (a : E) := by
      intro a
      obtain ⟨g, hg⟩ := hπ a
      have h₁ := hg ⟨s, hs⟩
      have h₂ := hg ⟨s', hs'⟩
      simp only at h₁ h₂
      rw [← hemb, ← hemb, h₁, h₂, heq]
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => hagree a)
  · intro f hf
    have hTspan : ∀ x ∈ Algebra.adjoin V (Set.range fun a : 𝓞 E => fun s => emb s a),
        x ∈ Submodule.span V (Set.range fun a : 𝓞 E => fun s => emb s a) := by
      intro x hx
      have hx' : x ∈ Subalgebra.toSubmodule
          (Algebra.adjoin V (Set.range fun a : 𝓞 E => fun s => emb s a)) := hx
      rw [Algebra.adjoin_eq_span] at hx'
      have hcl : ∀ y ∈ Submonoid.closure (Set.range fun a : 𝓞 E => fun s => emb s a),
          y ∈ Set.range fun a : 𝓞 E => fun s => emb s a := by
        intro y hy
        induction hy using Submonoid.closure_induction with
        | mem z hz => exact hz
        | one => exact ⟨1, funext fun s => map_one (emb s)⟩
        | mul z w _ _ hz hw =>
          obtain ⟨a, rfl⟩ := hz
          obtain ⟨b, rfl⟩ := hw
          exact ⟨a * b, funext fun s => map_mul (emb s) a b⟩
      exact Submodule.span_mono (fun y hy => hcl y hy) hx'
    have haeval : ∀ (g : Polynomial V) (s : E →+* C),
        (Polynomial.aeval (fun s => emb s π) g) s = g.eval (emb s π) := by
      intro g s
      have h := Polynomial.aeval_algHom_apply (Pi.evalAlgHom V (fun _ : E →+* C => V) s)
        (fun s => emb s π) g
      simp only [Pi.evalAlgHom_apply, Polynomial.coe_aeval_eq_eval] at h
      exact h.symm
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨u, huT, hu1, hu0⟩ := PositivityTheory.Xgn.MonogenicSeparating.ex_idem emb σ
        (Algebra.adjoin V (Set.range fun a : 𝓞 E => fun s => emb s a))
        (fun a => Algebra.subset_adjoin ⟨a, rfl⟩)
      have hxπ : (fun s => emb s π) ∈
          Algebra.adjoin V (Set.range fun a : 𝓞 E => fun s => emb s a) :=
        Algebra.subset_adjoin ⟨π, rfl⟩
      have hgT : Polynomial.aeval (fun s => emb s π) g ∈
          Algebra.adjoin V (Set.range fun a : 𝓞 E => fun s => emb s a) :=
        Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxπ)
          (Polynomial.aeval_mem_adjoin_singleton V _)
      have hfu : f = u * Polynomial.aeval (fun s => emb s π) g := by
        funext s
        rw [Pi.mul_apply]
        by_cases hs : ∀ a, ¬ IsUnit (emb s a - emb σ a)
        · rw [hu1 s hs, one_mul, hg s hs, haeval]
        · push_neg at hs
          rw [hu0 s hs, zero_mul, hf s hs]
      rw [hfu]
      exact hTspan _ (Subalgebra.mul_mem _ huT hgT)
    · intro hfspan
      have key : ∀ x (hx : x ∈ Submodule.span V (Set.range fun a : 𝓞 E => fun s => emb s a)),
          ∃ g : Polynomial V, ∀ s, (∀ a, ¬ IsUnit (emb s a - emb σ a)) →
            x s = g.eval (emb s π) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨a, rfl⟩ := hx
          obtain ⟨g, hg⟩ := hπ a
          exact ⟨g, fun s hs => hg ⟨s, hs⟩⟩
        | zero => exact ⟨0, fun s _ => by simp⟩
        | add x y _ _ hx hy =>
          obtain ⟨g₁, h₁⟩ := hx
          obtain ⟨g₂, h₂⟩ := hy
          exact ⟨g₁ + g₂, fun s hs => by rw [Pi.add_apply, h₁ s hs, h₂ s hs, Polynomial.eval_add]⟩
        | smul r x _ hx =>
          obtain ⟨g, hg⟩ := hx
          exact ⟨r • g, fun s hs => by rw [Pi.smul_apply, hg s hs, Polynomial.eval_smul]⟩
      exact key f hfspan
