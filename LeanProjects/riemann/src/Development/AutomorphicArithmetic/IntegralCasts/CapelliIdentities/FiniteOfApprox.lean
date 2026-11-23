import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing Polynomial

namespace UpperTheory.Reformulated.B.Ra2

private lemma split_low {O : Type} [CommRing O] (ϖ : O) (n : ℕ) :
    ∀ Q : O[X], (∀ i < n, ϖ ∣ Q.coeff i) →
      ∃ A B : O[X], Q = C ϖ * A + X ^ n * B ∧ B.coeff 0 = Q.coeff n := by
  induction n with
  | zero => intro Q _; exact ⟨0, Q, by simp, rfl⟩
  | succ n ih =>
    intro Q hQ
    obtain ⟨c, hc⟩ := hQ 0 (Nat.succ_pos n)
    obtain ⟨A, B, hAB, hB⟩ := ih Q.divX (fun i hi => by
      rw [coeff_divX]; exact hQ _ (Nat.succ_lt_succ hi))
    refine ⟨A * X + C c, B, ?_, by rw [hB, coeff_divX]⟩
    conv_lhs => rw [← divX_mul_X_add Q, hAB, hc]
    simp only [C_mul]
    ring

private lemma pow_mem_of_alg {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra O R] [IsLocalHom (algebraMap O R)]
    (hinj : Function.Injective (algebraMap O R)) {ϖ : O} (hϖ : Irreducible ϖ)
    {x : R} (hx : x ∈ maximalIdeal R) {P : O[X]} (hP : P ≠ 0) (hPx : aeval x P = 0) :
    ∃ n, x ^ n ∈ Ideal.span {algebraMap O R ϖ} := by
  classical
  have hp0 : algebraMap O R ϖ ≠ 0 := fun h =>
    hϖ.ne_zero (hinj (by rw [h, map_zero]))
  have hfin : FiniteMultiplicity (C ϖ) P :=
    FiniteMultiplicity.of_not_isUnit (fun h => hϖ.not_isUnit (Polynomial.isUnit_C.mp h)) hP
  obtain ⟨Q, hPQ, hQ⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hQx : aeval x Q = 0 := by
    rw [hPQ, map_mul, map_pow, aeval_C] at hPx
    exact (mul_eq_zero.mp hPx).resolve_left (pow_ne_zero _ hp0)
  have hex : ∃ i, ¬ ϖ ∣ Q.coeff i := by
    by_contra hcon
    push_neg at hcon
    exact hQ ((Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hcon)
  have hn : ¬ ϖ ∣ Q.coeff (Nat.find hex) := Nat.find_spec hex
  have hlow : ∀ i < Nat.find hex, ϖ ∣ Q.coeff i := fun i hi =>
    not_not.mp (Nat.find_min hex hi)
  obtain ⟨A, B, hAB, hB⟩ := split_low ϖ _ Q hlow
  have hu : IsUnit (B.coeff 0) := by
    by_contra hcon
    have h1 : B.coeff 0 ∈ maximalIdeal O := hcon
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton, hB] at h1
    exact hn h1
  have hBu : IsUnit (aeval x B) := by
    by_contra hcon
    have h1 : aeval x B ∈ maximalIdeal R := hcon
    have h2 : aeval x B = aeval x B.divX * x + algebraMap O R (B.coeff 0) := by
      conv_lhs => rw [← divX_mul_X_add B]
      simp
    have h3 : algebraMap O R (B.coeff 0) ∈ maximalIdeal R := by
      have := Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ (aeval x B.divX) hx)
      rwa [h2, add_sub_cancel_left] at this
    exact h3 (hu.map _)
  refine ⟨Nat.find hex, ?_⟩
  rw [← Ideal.mul_unit_mem_iff_mem _ hBu]
  have h0 : algebraMap O R ϖ * aeval x A + x ^ Nat.find hex * aeval x B = 0 := by
    have := hQx
    rw [hAB] at this
    simpa using this
  rw [eq_neg_of_add_eq_zero_right h0]
  exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

private lemma approx_ideal {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [UpperTheory.V.Alg.IsCO O R] (I : Ideal R) :
    ∃ M : Submodule O R, M.FG ∧ ∀ z ∈ I, ∃ w ∈ M, z - w ∈ maximalIdeal R * I := by
  obtain ⟨s, hs⟩ : I.FG := IsNoetherian.noetherian I
  subst hs
  refine ⟨Submodule.span O s, Submodule.fg_span s.finite_toSet, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem y hy => exact ⟨y, Submodule.subset_span hy, by simp⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨u, hu, hu'⟩ := ha
    obtain ⟨v, hv, hv'⟩ := hb
    refine ⟨u + v, add_mem hu hv, ?_⟩
    have := add_mem hu' hv'
    convert this using 1
    ring
  | smul r a ha' ha =>
    obtain ⟨u, hu, hu'⟩ := ha
    obtain ⟨c, hc⟩ := UpperTheory.V.Alg.IsCO.res_surj (O := O) r
    refine ⟨c • u, Submodule.smul_mem _ _ hu, ?_⟩
    have h1 : (r - algebraMap O R c) * a ∈ maximalIdeal R * Ideal.span (s : Set R) :=
      Ideal.mul_mem_mul hc ha'
    have h2 := Ideal.mul_mem_left _ (algebraMap O R c) hu'
    convert add_mem h1 h2 using 1
    rw [smul_eq_mul, Algebra.smul_def]
    ring

private lemma approx_pow {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [UpperTheory.V.Alg.IsCO O R] (N : ℕ) :
    ∃ M : Submodule O R, M.FG ∧ ∀ z : R, ∃ w ∈ M, z - w ∈ maximalIdeal R ^ N := by
  induction N with
  | zero => exact ⟨⊥, Submodule.fg_bot, fun z => ⟨0, zero_mem _, by simp⟩⟩
  | succ N ih =>
    obtain ⟨M, hM, h⟩ := ih
    obtain ⟨M', hM', h'⟩ := approx_ideal (O := O) (maximalIdeal R ^ N)
    refine ⟨M ⊔ M', hM.sup hM', fun z => ?_⟩
    obtain ⟨w, hw, hzw⟩ := h z
    obtain ⟨w', hw', hzw'⟩ := h' _ hzw
    refine ⟨w + w', add_mem (Submodule.mem_sup_left hw) (Submodule.mem_sup_right hw'), ?_⟩
    rw [pow_succ', ← sub_sub]
    exact hzw'

private lemma finite_of_approx {O R : Type} [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [IsLocalRing R] [Algebra O R]
    [IsLocalHom (algebraMap O R)] [IsHausdorff (maximalIdeal R) R]
    {ϖ : O} (hϖ : maximalIdeal O = Ideal.span {ϖ}) {M : Submodule O R} (hM : M.FG)
    (h : ∀ z : R, ∃ w ∈ M, z - w ∈ Ideal.span {algebraMap O R ϖ}) : Module.Finite O R := by
  obtain ⟨s, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hM
  have hϖI : ϖ ∈ maximalIdeal O := hϖ ▸ Ideal.mem_span_singleton_self ϖ
  let G : (Fin s → O) →ₗ[O] R := Fintype.linearCombination O g
  have hstep : ∀ y : R, ∃ (c : Fin s → O) (y' : R), y = G c + algebraMap O R ϖ * y' := by
    intro y
    obtain ⟨w, hw, hyw⟩ := h y
    rw [← hg, ← Fintype.range_linearCombination] at hw
    obtain ⟨c, rfl⟩ := hw
    obtain ⟨y', hy'⟩ := Ideal.mem_span_singleton'.mp hyw
    exact ⟨c, y', by rw [mul_comm, hy']; ring⟩
  choose φ ψ hφ using hstep
  have hmap : ∀ (n : ℕ) (a : O), a ∈ maximalIdeal O ^ n →
      algebraMap O R a ∈ maximalIdeal R ^ n := by
    intro n a ha
    have hle : maximalIdeal O ≤ (maximalIdeal R).comap (algebraMap O R) := fun b hb =>
      fun hu => hb (IsLocalHom.map_nonunit b hu)
    exact Ideal.le_comap_pow _ n (Ideal.pow_right_mono hle n ha)
  refine Module.Finite.of_surjective G fun z => ?_
  let y : ℕ → R := fun k => ψ^[k] z
  let S : ℕ → Fin s → O := fun n j => ∑ k ∈ Finset.range n, ϖ ^ k * φ (y k) j
  have hSsucc : ∀ n, S (n + 1) = S n + ϖ ^ n • φ (y n) := by
    intro n
    funext j
    simp [S, Finset.sum_range_succ]
  have hS : ∀ n, z = G (S n) + algebraMap O R ϖ ^ n * y n := by
    intro n
    induction n with
    | zero =>
      have h0 : S 0 = 0 := by
        funext j
        simp [S]
      simp [h0, y]
    | succ n ih =>
      have hy : y (n + 1) = ψ (y n) := Function.iterate_succ_apply' ψ n z
      rw [hSsucc, map_add, map_smul, hy, Algebra.smul_def, map_pow]
      conv_lhs => rw [ih, hφ (y n)]
      ring
  have hcauchy : ∀ j, ∀ {m n : ℕ}, m ≤ n →
      S m j ≡ S n j [SMOD (maximalIdeal O ^ m • ⊤ : Submodule O O)] := by
    intro j m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact SModEq.refl _
    | succ n hmn ih =>
      refine ih.trans ?_
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hSsucc]
      have : S n j - (S n + ϖ ^ n • φ (y n)) j = -(ϖ ^ n * φ (y n) j) := by
        simp
      rw [this]
      exact neg_mem (Ideal.mul_mem_right _ _
        (Ideal.pow_le_pow_right hmn (Ideal.pow_mem_pow hϖI n)))
  have hL : ∀ j, ∃ L : O, ∀ n, S n j ≡ L [SMOD (maximalIdeal O ^ n • ⊤ : Submodule O O)] :=
    fun j => IsPrecomplete.prec' _ (hcauchy j)
  choose L hL using hL
  refine ⟨L, ?_⟩
  refine (IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)).mpr fun n => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  have hd : G L - z = G (L - S n) - algebraMap O R ϖ ^ n * y n := by
    conv_lhs => rw [hS n]
    rw [map_sub]
    ring
  rw [hd]
  refine sub_mem ?_ (Ideal.mul_mem_right _ _ ?_)
  · have hG : G (L - S n) = ∑ j, (L - S n) j • g j := Fintype.linearCombination_apply O g _
    rw [hG]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ (hmap n _ ?_)
    have h1 := (hL j n).symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
    exact h1
  · rw [← map_pow]
    exact hmap n _ (Ideal.pow_mem_pow hϖI n)

end UpperTheory.Reformulated.B.Ra2

open UpperTheory.Reformulated.B.Ra2 in
theorem UpperTheory.Reformulated.B.Ra2.finite_of_alg :
    ∀ {O R : Type} [inst : CommRing O] [inst_1 : IsDomain O] [inst_2 : IsDiscreteValuationRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [inst_4 : CommRing R] [IsDomain R] [inst_6 : Algebra O R]
      [UpperTheory.V.Alg.IsCO O R],
      Function.Injective (⇑(Algebra.algebraMap O R) : O → R) →
        (∀ (a : R), ∃ (P : Polynomial O), P ≠ (0 : Polynomial O) ∧ (Polynomial.aeval a : Polynomial O → R) P = (0 : R)) →
          Module.Finite O R := by
  intro O R _ _ _ _ _ _ _ _ hinj halg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hrad : maximalIdeal R ≤ (Ideal.span {algebraMap O R ϖ}).radical := fun x hx => by
    obtain ⟨P, hP, hPx⟩ := halg x
    exact pow_mem_of_alg hinj hϖ hx hP hPx
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  obtain ⟨M, hM, h⟩ := approx_pow (O := O) (R := R) N
  exact finite_of_approx hϖ.maximalIdeal_eq hM fun z => by
    obtain ⟨w, hw, hzw⟩ := h z
    exact ⟨w, hw, hN hzw⟩
