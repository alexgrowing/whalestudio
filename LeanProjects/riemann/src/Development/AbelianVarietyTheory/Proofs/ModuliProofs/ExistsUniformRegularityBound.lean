import Mathlib

open Filter Module MvPolynomial

namespace GlobalTheory.RegBound

variable {σ K : Type} [Field K]

noncomputable abbrev piece (I : Ideal (MvPolynomial σ K)) (e : ℕ) : Submodule K (MvPolynomial σ K) :=
  homogeneousSubmodule σ K e ⊓ I.restrictScalars K

noncomputable abbrev genIn (I : Ideal (MvPolynomial σ K)) (e : ℕ) : Ideal (MvPolynomial σ K) :=
  Ideal.span {G | G ∈ I ∧ G.IsHomogeneous e}

instance finite_forms [Finite σ] (e : ℕ) : Module.Finite K (homogeneousSubmodule σ K e) :=
  Module.Finite.iff_fg.2 (homogeneousSubmodule_fg σ K e)

instance finite_piece [Finite σ] (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    Module.Finite K (piece I e) :=
  Submodule.finiteDimensional_of_le (S₂ := homogeneousSubmodule σ K e) inf_le_left

theorem comp_succ_mul {h : MvPolynomial σ K} (hh : h.IsHomogeneous 1) (e : ℕ)
    (B : MvPolynomial σ K) :
    homogeneousComponent (e + 1) (h * B) = h * homogeneousComponent e B := by
  induction B using MvPolynomial.induction_on' with
  | monomial d c =>
    have h1 := isHomogeneous_monomial (d := d) c rfl
    rw [homogeneousComponent_of_mem (hh.mul h1), homogeneousComponent_of_mem h1]
    by_cases he : e = d.degree
    · rw [if_pos he, if_pos (by omega)]
    · rw [if_neg he, if_neg (by omega), mul_zero]
  | add p q hp hq => simp [mul_add, hp, hq]

theorem comp_zero_mul {h : MvPolynomial σ K} (hh : h.IsHomogeneous 1)
    (B : MvPolynomial σ K) : homogeneousComponent 0 (h * B) = 0 := by
  induction B using MvPolynomial.induction_on' with
  | monomial d c =>
    have h1 := isHomogeneous_monomial (d := d) c rfl
    rw [homogeneousComponent_of_mem (hh.mul h1), if_neg (by omega)]
  | add p q hp hq => rw [mul_add, map_add, hp, hq, add_zero]

theorem mem_sup_span {I : Ideal (MvPolynomial σ K)} {h F : MvPolynomial σ K} :
    F ∈ I ⊔ Ideal.span {h} ↔ ∃ A ∈ I, ∃ B, F = A + h * B := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨A, hA, B, hB, rfl⟩
    obtain ⟨C, rfl⟩ := Ideal.mem_span_singleton.1 hB
    exact ⟨A, hA, C, rfl⟩
  · rintro ⟨A, hA, B, rfl⟩
    exact ⟨A, hA, _, Ideal.mem_span_singleton.2 ⟨B, rfl⟩, rfl⟩

theorem exists_regular_form [Finite σ] [Infinite K] {I : Ideal (MvPolynomial σ K)}
    (hsat : ∀ F, (∀ i, X i * F ∈ I) → F ∈ I) :
    ∃ h : MvPolynomial σ K, h.IsHomogeneous 1 ∧ ∀ F, h * F ∈ I → F ∈ I := by
  classical
  by_contra hcon
  push Not at hcon
  have hfin := associatedPrimes.finite (MvPolynomial σ K) (MvPolynomial σ K ⧸ I)
  let W : Ideal (MvPolynomial σ K) → Subspace K (homogeneousSubmodule σ K 1) := fun P =>
    (P.restrictScalars K).comap (homogeneousSubmodule σ K 1).subtype
  have hcov : ⋃ p ∈ hfin.toFinset.image W, (p : Set (homogeneousSubmodule σ K 1)) = Set.univ := by
    refine Set.eq_univ_of_forall fun h => ?_
    obtain ⟨F, hF, hF'⟩ := hcon h.1 h.2
    have : h.1 ∈ ⋃ p ∈ associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I),
        (p : Set (MvPolynomial σ K)) := by
      rw [biUnion_associatedPrimes_eq_zero_divisors]
      exact ⟨Ideal.Quotient.mk I F, mt Ideal.Quotient.eq_zero_iff_mem.1 hF',
        Ideal.Quotient.eq_zero_iff_mem.2 hF⟩
    obtain ⟨P, hP, hh⟩ := Set.mem_iUnion₂.1 this
    exact Set.mem_iUnion₂.2 ⟨W P, Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hP), hh⟩
  obtain ⟨P, hP, hW⟩ := Finset.mem_image.1 (Subspace.top_mem_of_biUnion_eq_univ hcov)
  obtain ⟨hp, x, hx⟩ := isAssociatedPrime_iff.1 (hfin.mem_toFinset.1 hP)
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hF : F ∈ I := hsat F fun i => by
    have h1 : (⟨X i, isHomogeneous_X K i⟩ : homogeneousSubmodule σ K 1) ∈ W P := by
      rw [hW]; trivial
    have h2 : X i ∈ P := h1
    rw [hx, Submodule.mem_colon_singleton] at h2
    exact Ideal.Quotient.eq_zero_iff_mem.1 h2
  apply hp.ne_top
  rw [Ideal.eq_top_iff_one, hx, Submodule.mem_colon_singleton, one_smul]
  exact Ideal.Quotient.eq_zero_iff_mem.2 hF

theorem hom_sup_span {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) {h : MvPolynomial σ K}
    (hh : h.IsHomogeneous 1) :
    ∀ F ∈ I ⊔ Ideal.span {h}, ∀ e, homogeneousComponent e F ∈ I ⊔ Ideal.span {h} := by
  intro F hF e
  obtain ⟨A, hA, B, rfl⟩ := mem_sup_span.1 hF
  rw [map_add]
  cases e with
  | zero => exact mem_sup_span.2 ⟨_, hI A hA 0, 0, by rw [comp_zero_mul hh, mul_zero]⟩
  | succ e => exact mem_sup_span.2 ⟨_, hI A hA _, _, by rw [comp_succ_mul hh]⟩

theorem finrank_section [Finite σ] {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) {h : MvPolynomial σ K}
    (hh : h.IsHomogeneous 1) (hreg : ∀ F, h * F ∈ I → F ∈ I) (hne : I ≠ ⊤) (e : ℕ) :
    finrank K (piece (I ⊔ Ideal.span {h}) (e + 1)) + finrank K (piece I e) =
      finrank K (piece I (e + 1)) + finrank K (homogeneousSubmodule σ K e) := by
  have h0 : h ≠ 0 := by
    rintro rfl
    exact hne ((Ideal.eq_top_iff_one _).2 (hreg 1 (by simp)))
  let μ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K := LinearMap.mulLeft K h
  have hμ : Function.Injective μ := fun a b hab => mul_left_cancel₀ h0 hab
  have e1 : piece (I ⊔ Ideal.span {h}) (e + 1) =
      piece I (e + 1) ⊔ (homogeneousSubmodule σ K e).map μ := by
    apply le_antisymm
    · rintro F ⟨hF1, hF2⟩
      obtain ⟨A, hA, B, hAB⟩ := mem_sup_span.1 hF2
      have : F = homogeneousComponent (e + 1) A + h * homogeneousComponent e B := by
        rw [← comp_succ_mul hh, ← map_add, ← hAB, homogeneousComponent_eq_self hF1]
      rw [this]
      exact Submodule.add_mem_sup ⟨homogeneousComponent_isHomogeneous _ _, hI A hA _⟩
        ⟨_, homogeneousComponent_isHomogeneous _ _, rfl⟩
    · refine sup_le (fun F hF => ⟨hF.1, mem_sup_span.2 ⟨F, hF.2, 0, by simp⟩⟩) ?_
      rintro _ ⟨B, hB, rfl⟩
      refine ⟨?_, mem_sup_span.2 ⟨0, I.zero_mem, B, by simp [μ]⟩⟩
      have := hh.mul hB
      rwa [add_comm] at this
  have e2 : piece I (e + 1) ⊓ (homogeneousSubmodule σ K e).map μ = (piece I e).map μ := by
    apply le_antisymm
    · rintro _ ⟨hF, B, hB, rfl⟩
      exact ⟨B, ⟨hB, hreg B hF.2⟩, rfl⟩
    · rintro _ ⟨B, hB, rfl⟩
      refine ⟨⟨?_, I.mul_mem_left h hB.2⟩, B, hB.1, rfl⟩
      have := hh.mul hB.1
      rwa [add_comm] at this
  have := Submodule.finrank_sup_add_finrank_inf_eq (piece I (e + 1))
    ((homogeneousSubmodule σ K e).map μ)
  rw [← e1, e2, ← (Submodule.equivMapOfInjective μ hμ _).finrank_eq,
    ← (Submodule.equivMapOfInjective μ hμ _).finrank_eq] at this
  exact this

theorem hom_genIn (I : Ideal (MvPolynomial σ K)) (d : ℕ) :
    ∀ F ∈ genIn I d, ∀ e, homogeneousComponent e F ∈ genIn I d := by
  intro F hF e
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := K)
  exact homogeneousComponent_mem_of_mem
    (Ideal.homogeneous_span (homogeneousSubmodule σ K) _ fun G hG => ⟨d, hG.2⟩) hF e

theorem gen_of_section {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) {h : MvPolynomial σ K}
    (hh : h.IsHomogeneous 1) (hreg : ∀ F, h * F ∈ I → F ∈ I) {e : ℕ} {F : MvPolynomial σ K}
    (hF : F ∈ I) (hFe : F.IsHomogeneous (e + 1)) (hg : F ∈ genIn (I ⊔ Ideal.span {h}) e) :
    F ∈ genIn I e := by
  have h1 : genIn (I ⊔ Ideal.span {h}) e ≤ genIn I e ⊔ Ideal.span {h} := by
    refine Ideal.span_le.2 ?_
    rintro G ⟨hG, hGe⟩
    obtain ⟨A, hA, B, hAB⟩ := mem_sup_span.1 hG
    have : G = homogeneousComponent e A + homogeneousComponent e (h * B) := by
      rw [← map_add, ← hAB, homogeneousComponent_eq_self hGe]
    rw [this]
    refine Submodule.add_mem_sup
      (Ideal.subset_span ⟨hI A hA _, homogeneousComponent_isHomogeneous _ _⟩) ?_
    cases e with
    | zero => rw [comp_zero_mul hh]; exact Submodule.zero_mem _
    | succ e => rw [comp_succ_mul hh]; exact Ideal.mem_span_singleton.2 ⟨_, rfl⟩
  obtain ⟨A, hA, B, hAB⟩ := mem_sup_span.1 (h1 hg)
  have hAI : A ∈ I := (Ideal.span_le.2 fun G hG => hG.1 : genIn I e ≤ I) hA
  have hB : B ∈ I := hreg B (by simpa [hAB] using I.sub_mem hF hAI)
  have : F = homogeneousComponent (e + 1) A + h * homogeneousComponent e B := by
    rw [← comp_succ_mul hh, ← map_add, ← hAB, homogeneousComponent_eq_self hFe]
  rw [this]
  exact Ideal.add_mem _ (hom_genIn I e A hA _) (Ideal.mul_mem_left _ _
    (Ideal.subset_span ⟨hI B hB _, homogeneousComponent_isHomogeneous _ _⟩))

theorem gen_top {e : ℕ} {F : MvPolynomial σ K} (hFe : F.IsHomogeneous (e + 1)) :
    F ∈ genIn (⊤ : Ideal (MvPolynomial σ K)) e := by
  have : F ∈ homogeneousSubmodule σ K e * homogeneousSubmodule σ K 1 := by
    have h1 : F ∈ homogeneousSubmodule σ K 1 ^ (e + 1) := by
      rw [homogeneousSubmodule_one_pow]; exact hFe
    rwa [pow_succ, homogeneousSubmodule_one_pow] at h1
  refine Submodule.mul_induction_on this (fun a ha b _ => ?_) (fun a b => Ideal.add_mem _)
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨trivial, ha⟩)

theorem eventually_mem_of_X_mul [Finite σ] {J L : Ideal (MvPolynomial σ K)}
    (hJ : ∀ F ∈ J, ∀ e, homogeneousComponent e F ∈ J) (hL : ∀ F ∈ L, ∀ i, X i * F ∈ J) :
    ∀ᶠ e in atTop, ∀ F ∈ L, F.IsHomogeneous e → F ∈ J := by
  obtain ⟨T, hT⟩ := IsNoetherian.noetherian L
  have key : ∀ A G, G ∈ L → (A - C (coeff 0 A)) * G ∈ J := by
    intro A G hG
    induction A using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq =>
      convert J.add_mem hp hq using 1
      simp only [coeff_add, map_add]; ring
    | mul_X p i _ =>
      have : coeff 0 (p * X i) = 0 := by
        have := map_mul (constantCoeff (σ := σ) (R := K)) p (X i)
        simpa [constantCoeff_eq] using this
      rw [this, map_zero, sub_zero, mul_assoc]
      exact J.mul_mem_left _ (hL G hG i)
  have key2 : ∀ F ∈ Submodule.span (MvPolynomial σ K) (T : Set (MvPolynomial σ K)),
      ∃ G ∈ L, G.totalDegree ≤ T.sup totalDegree ∧ F - G ∈ J := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem x hx => exact ⟨x, hT ▸ Submodule.subset_span hx, Finset.le_sup hx, by simp⟩
    | zero => exact ⟨0, L.zero_mem, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨G, h1, h2, h3⟩ := hx
      obtain ⟨G', h1', h2', h3'⟩ := hy
      refine ⟨G + G', L.add_mem h1 h1', (totalDegree_add _ _).trans (max_le h2 h2'), ?_⟩
      convert J.add_mem h3 h3' using 1
      ring
    | smul A x _ hx =>
      obtain ⟨G, h1, h2, h3⟩ := hx
      refine ⟨C (coeff 0 A) * G, L.mul_mem_left _ h1, ?_, ?_⟩
      · exact (totalDegree_mul _ _).trans (by simpa using h2)
      · convert J.add_mem (J.mul_mem_left A h3) (key A G h1) using 1
        rw [smul_eq_mul]; ring
  filter_upwards [eventually_gt_atTop (T.sup totalDegree)] with e he F hF hFe
  obtain ⟨G, -, h2, h3⟩ := key2 F (hT ▸ hF)
  have := hJ _ h3 e
  rwa [map_sub, homogeneousComponent_eq_self hFe,
    homogeneousComponent_eq_zero _ _ (h2.trans_lt he), sub_zero] at this

theorem exists_saturation [Finite σ] {J : Ideal (MvPolynomial σ K)}
    (hJ : ∀ F ∈ J, ∀ e, homogeneousComponent e F ∈ J) :
    ∃ J' : Ideal (MvPolynomial σ K), J ≤ J' ∧ (∀ F ∈ J', ∀ e, homogeneousComponent e F ∈ J') ∧
      (∀ F, (∀ i, X i * F ∈ J') → F ∈ J') ∧
      ∀ᶠ e in atTop, ∀ F ∈ J', F.IsHomogeneous e → F ∈ J := by
  obtain ⟨J', ⟨h1, h2, h3⟩, hmax⟩ := (set_has_maximal_iff_noetherian.2
    (inferInstance : IsNoetherian (MvPolynomial σ K) (MvPolynomial σ K)))
    {J' | J ≤ J' ∧ (∀ F ∈ J', ∀ e, homogeneousComponent e F ∈ J') ∧
      ∀ᶠ e in atTop, ∀ F ∈ J', F.IsHomogeneous e → F ∈ J}
    ⟨J, le_rfl, hJ, Eventually.of_forall fun _ _ h _ => h⟩
  refine ⟨J', h1, h2, ?_, h3⟩
  let L : Ideal (MvPolynomial σ K) :=
    { carrier := {F | ∀ i, X i * F ∈ J'}
      add_mem' := fun ha hb i => by rw [mul_add]; exact J'.add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      smul_mem' := fun c x hx i => by
        rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left J' _ (hx i) }
  have hle : J' ≤ L := fun F hF i => Ideal.mul_mem_left J' _ hF
  have hL := hmax L ⟨h1.trans hle, fun F hF e i => by
      rw [← comp_succ_mul (isHomogeneous_X K i)]; exact h2 _ (hF i) _, by
      filter_upwards [h3, eventually_mem_of_X_mul (L := L) h2 fun F hF => hF] with e a b F hF hFe
      exact a F (b F hF hFe) hFe⟩
  have : J' = L := by
    by_contra hne
    exact hL (lt_of_le_of_ne hle hne)
  intro F hF
  rw [this]; exact hF

noncomputable def nmon (σ : Type) (e : ℕ) : ℕ := Nat.card {d : σ →₀ ℕ | d.degree = e}

theorem finrank_forms (e : ℕ) : finrank K (homogeneousSubmodule σ K e) = nmon σ e := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact finrank_eq_nat_card_basis (basisRestrictSupport K _)

theorem numeric {g : ℕ → ℚ} {δ : ℕ → ℕ} {d B : ℕ} (h1 : ∀ e ≥ d, g (e + 1) = g e - δ (e + 1))
    (h2 : ∀ᶠ e in atTop, g e = 0) (h3 : g d ≤ B) (h4 : ∀ e ≥ d, δ e = 0 → δ (e + 1) = 0) :
    ∀ e ≥ d + B + 1, δ e = 0 ∧ g e = 0 := by
  have mono : ∀ e ≥ d, ∀ e' ≥ e, g e' ≤ g e := by
    intro e he e' he'
    induction e', he' using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
      rw [h1 n (he.trans hn)]
      have : (0 : ℚ) ≤ δ (n + 1) := Nat.cast_nonneg _
      linarith
  have nonneg : ∀ e ≥ d, 0 ≤ g e := by
    intro e he
    obtain ⟨e', h, h'⟩ := (h2.and (eventually_ge_atTop e)).exists
    exact h ▸ mono e he e' h'
  have prop : ∀ e ≥ d, δ e = 0 → ∀ e' ≥ e, δ e' = 0 := by
    intro e he h e' he'
    induction e', he' using Nat.le_induction with
    | base => exact h
    | succ n hn ih => exact h4 n (he.trans hn) ih
  have dec : ∀ k : ℕ, δ (d + k) ≠ 0 → g (d + k) ≤ g d - k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      have h5 := ih fun h => hk (h4 (d + k) (Nat.le_add_right _ _) h)
      have h6 : (1 : ℚ) ≤ δ (d + k + 1) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
      rw [← add_assoc, h1 _ (by omega)]
      push_cast
      linarith
  have z : δ (d + (B + 1)) = 0 := by
    by_contra h
    have := dec _ h
    have := nonneg (d + (B + 1)) (by omega)
    push_cast at *
    linarith
  intro e he
  refine ⟨prop _ (by omega) z e (by omega), ?_⟩
  have const : ∀ e' ≥ e, g e' = g e := by
    intro e' he'
    induction e', he' using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [h1 n (by omega), prop _ (by omega) z (n + 1) (by omega), ih]; simp
  obtain ⟨e', h, h'⟩ := (h2.and (eventually_ge_atTop e)).exists
  rw [← const e' h', h]

theorem piece_mono {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J) (e : ℕ) :
    piece I e ≤ piece J e := fun _ hF => ⟨hF.1, h hF.2⟩

theorem bound_infinite (σ : Type) [Finite σ] (k : ℕ) : ∀ q : ℕ → ℚ, ∃ d : ℕ,
    ∀ (K : Type) [Field K] [Infinite K] (I : Ideal (MvPolynomial σ K)),
      (∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) → (∀ F, (∀ i, X i * F ∈ I) → F ∈ I) →
      nmon σ 1 ≤ finrank K (piece I 1) + k →
      (∀ᶠ e in atTop, (finrank K (piece I e) : ℚ) = q e) →
      ∀ e ≥ d, (finrank K (piece I e) : ℚ) = q e ∧
        ∀ F ∈ I, F.IsHomogeneous (e + 1) → F ∈ genIn I e := by
  have htop : ∀ (K : Type) [Field K] (e : ℕ),
      finrank K (piece (⊤ : Ideal (MvPolynomial σ K)) e) = nmon σ e := by
    intro K _ e
    have : piece (⊤ : Ideal (MvPolynomial σ K)) e = homogeneousSubmodule σ K e := by simp [piece]
    rw [this, finrank_forms]
  induction k with
  | zero =>
    intro q
    have : ∃ d : ℕ, (∀ᶠ e in atTop, (nmon σ e : ℚ) = q e) → ∀ e ≥ d, (nmon σ e : ℚ) = q e := by
      by_cases h : ∀ᶠ e in atTop, (nmon σ e : ℚ) = q e
      · obtain ⟨d, hd⟩ := eventually_atTop.1 h
        exact ⟨d, fun _ => hd⟩
      · exact ⟨0, fun h' => absurd h' h⟩
    obtain ⟨d, hd⟩ := this
    refine ⟨d, fun K _ _ I _ hsat hk hq e he => ?_⟩
    have h1 : piece I 1 = homogeneousSubmodule σ K 1 :=
      Submodule.eq_of_le_of_finrank_le inf_le_left (by rwa [finrank_forms])
    have h2 : I = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      refine hsat 1 fun i => ?_
      have : X i ∈ piece I 1 := h1 ▸ isHomogeneous_X K i
      simpa using this.2
    subst h2
    simp only [htop] at hq ⊢
    exact ⟨hd hq e he, fun F _ hF => gen_top hF⟩
  | succ k ih =>
    intro q
    obtain ⟨d₀, hd₀⟩ := ih q
    obtain ⟨d₁, hd₁⟩ := ih fun e => q e + nmon σ (e - 1) - q (e - 1)
    refine ⟨max d₀ (d₁ + ⌈(nmon σ d₁ : ℚ) - q d₁⌉₊ + 1), fun K _ _ I hI hsat hk hq e he => ?_⟩
    by_cases hne : I = ⊤
    · exact hd₀ K I hI hsat (by rw [hne, htop]; omega) hq e (le_of_max_le_left he)
    obtain ⟨h, hh, hreg⟩ := exists_regular_form hsat
    obtain ⟨J', hJJ, hJ'h, hJ's, hJ'e⟩ := exists_saturation (hom_sup_span hI hh)
    have hdim := finrank_section hI hh hreg hne
    simp only [finrank_forms] at hdim
    set J := I ⊔ Ideal.span {h} with hJ
    have hhJ : h ∈ J := mem_sup_span.2 ⟨0, I.zero_mem, 1, by simp⟩
    have hlt : finrank K (piece I 1) < finrank K (piece J' 1) := by
      refine Submodule.finrank_lt_finrank_of_lt
        (lt_of_le_of_ne (piece_mono (le_sup_left.trans hJJ) 1) fun heq => hne ?_)
      have : h ∈ piece I 1 := heq ▸ (⟨hh, hJJ hhJ⟩ : h ∈ piece J' 1)
      exact (Ideal.eq_top_iff_one _).2 (hreg 1 (by simpa using this.2))
    have hle : ∀ e, finrank K (piece J e) ≤ finrank K (piece J' e) := fun e =>
      Submodule.finrank_mono (piece_mono hJJ e)
    have hgood := hd₁ K J' hJ'h hJ's (by omega) (by
      obtain ⟨N, hN⟩ := eventually_atTop.1 hq
      filter_upwards [hJ'e, eventually_ge_atTop (N + 1)] with e h1 h2
      obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      have : piece J' (e + 1) = piece J (e + 1) :=
        le_antisymm (fun F hF => ⟨hF.1, h1 F hF.2 hF.1⟩) (piece_mono hJJ _)
      rw [this, Nat.add_sub_cancel, ← hN (e + 1) (by omega), ← hN e (by omega)]
      have := congrArg (Nat.cast : ℕ → ℚ) (hdim e)
      push_cast at this
      linarith)
    have hz : ∀ e, finrank K (piece J' e) - finrank K (piece J e) = 0 →
        genIn J' e ≤ genIn J e := by
      intro e h0
      have : piece J e = piece J' e :=
        Submodule.eq_of_le_of_finrank_le (piece_mono hJJ e) (by omega)
      refine Ideal.span_mono fun G hG => ⟨?_, hG.2⟩
      have h1 : G ∈ piece J e := this ▸ (⟨hG.2, hG.1⟩ : G ∈ piece J' e)
      exact h1.2
    have hnum := numeric (g := fun e => (finrank K (piece I e) : ℚ) - q e)
      (δ := fun e => finrank K (piece J' e) - finrank K (piece J e)) (d := d₁)
      (B := ⌈(nmon σ d₁ : ℚ) - q d₁⌉₊)
      (fun e he => by
        have h1 := (hgood (e + 1) (by omega)).1
        have h2 := congrArg (Nat.cast : ℕ → ℚ) (hdim e)
        rw [Nat.add_sub_cancel] at h1
        simp only [Nat.cast_sub (hle _)]
        push_cast at h2
        linarith)
      (hq.mono fun e he => sub_eq_zero.2 he)
      (by
        refine le_trans ?_ (Nat.le_ceil _)
        have : finrank K (piece I d₁) ≤ nmon σ d₁ := by
          rw [← finrank_forms (K := K)]
          exact Submodule.finrank_mono inf_le_left
        have : (finrank K (piece I d₁) : ℚ) ≤ nmon σ d₁ := by exact_mod_cast this
        linarith)
      (fun e he h0 => by
        refine Nat.sub_eq_zero_of_le (Submodule.finrank_mono fun F hF => ⟨hF.1, ?_⟩)
        exact (Ideal.span_le.2 fun G hG => hG.1 : genIn J e ≤ J)
          (hz e h0 ((hgood e he).2 F hF.2 hF.1)))
      e (le_of_max_le_right he)
    refine ⟨sub_eq_zero.1 hnum.2, fun F hF hFe => gen_of_section hI hh hreg hF hFe ?_⟩
    have he' : d₁ ≤ e := by have := le_of_max_le_right he; omega
    exact hz e hnum.1 ((hgood e he').2 F (hJJ (Ideal.mem_sup_left hF)) hFe)

section BaseChange

variable {L : Type} [Field L] [Algebra K L]

noncomputable def contr (φ : L →ₗ[K] K) (F : MvPolynomial σ L) : MvPolynomial σ K :=
  ∑ m ∈ F.support, monomial m (φ (coeff m F))

@[simp] theorem coeff_contr (φ : L →ₗ[K] K) (F : MvPolynomial σ L) (m : σ →₀ ℕ) :
    coeff m (contr φ F) = φ (coeff m F) := by
  classical
  simp only [contr, coeff_sum, coeff_monomial, Finset.sum_ite_eq', MvPolynomial.mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not.1 h, map_zero]

theorem contr_add (φ : L →ₗ[K] K) (F G : MvPolynomial σ L) :
    contr φ (F + G) = contr φ F + contr φ G := by ext; simp

theorem contr_zero (φ : L →ₗ[K] K) : contr φ (0 : MvPolynomial σ L) = 0 := by ext; simp

theorem contr_X_mul (φ : L →ₗ[K] K) (i : σ) (F : MvPolynomial σ L) :
    contr φ (X i * F) = X i * contr φ F := by
  classical
  ext m
  simp only [coeff_contr, coeff_X_mul']
  split_ifs <;> simp

theorem contr_smul (φ : L →ₗ[K] K) (c : L) (F : MvPolynomial σ L) :
    contr φ (c • F) = contr (φ ∘ₗ LinearMap.mulLeft K c) F := by ext; simp

theorem contr_comp (φ : L →ₗ[K] K) (e : ℕ) (F : MvPolynomial σ L) :
    contr φ (homogeneousComponent e F) = homogeneousComponent e (contr φ F) := by
  classical
  ext m
  simp only [coeff_contr, coeff_homogeneousComponent]
  split_ifs <;> simp

theorem contr_smul_map (φ : L →ₗ[K] K) (c : L) (F : MvPolynomial σ K) :
    contr φ (c • map (algebraMap K L) F) = φ c • F := by
  ext m
  rw [coeff_contr, coeff_smul, coeff_smul, coeff_map, smul_eq_mul, mul_comm, ← Algebra.smul_def,
    map_smul, smul_eq_mul, smul_eq_mul, mul_comm]

theorem contr_map (φ : L →ₗ[K] K) (F : MvPolynomial σ K) :
    contr φ (map (algebraMap K L) F) = φ 1 • F := by
  rw [← contr_smul_map, one_smul]

def extSub (L : Type) [Field L] [Algebra K L] (W : Submodule K (MvPolynomial σ K)) :
    Submodule L (MvPolynomial σ L) where
  carrier := {F | ∀ φ : L →ₗ[K] K, contr φ F ∈ W}
  add_mem' ha hb φ := by rw [contr_add]; exact W.add_mem (ha φ) (hb φ)
  zero_mem' φ := by rw [contr_zero]; exact W.zero_mem
  smul_mem' c F hF φ := by rw [contr_smul]; exact hF _

def extIdeal (L : Type) [Field L] [Algebra K L] (I : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial σ L) where
  carrier := {F | ∀ φ : L →ₗ[K] K, contr φ F ∈ I}
  add_mem' ha hb φ := by rw [contr_add]; exact I.add_mem (ha φ) (hb φ)
  zero_mem' φ := by rw [contr_zero]; exact I.zero_mem
  smul_mem' A F hF := by
    rw [smul_eq_mul]
    induction A using MvPolynomial.induction_on generalizing F with
    | C a => intro φ; rw [C_mul', contr_smul]; exact hF _
    | add p q hp hq => intro φ; rw [add_mul, contr_add]; exact I.add_mem (hp _ hF φ) (hq _ hF φ)
    | mul_X p i hp =>
      rw [mul_assoc]
      exact hp _ fun φ => by rw [contr_X_mul]; exact I.mul_mem_left _ (hF φ)

theorem eq_of_contr {F G : MvPolynomial σ L} (h : ∀ φ : L →ₗ[K] K, contr φ F = contr φ G) :
    F = G := by
  ext m
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  rw [map_sub, sub_eq_zero, ← coeff_contr, ← coeff_contr, h]

theorem finrank_extSub (W : Submodule K (MvPolynomial σ K)) [Module.Finite K W] :
    finrank L (extSub L W) = finrank K W := by
  classical
  let w := Module.finBasis K W
  let v : Fin (finrank K W) → MvPolynomial σ L := fun i => map (algebraMap K L) (w i)
  have hli : LinearIndependent L v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    rw [← Module.forall_dual_apply_eq_zero_iff K]
    intro φ
    have hw : LinearIndependent K fun i => (w i : MvPolynomial σ K) :=
      w.linearIndependent.map' W.subtype W.ker_subtype
    refine Fintype.linearIndependent_iff.1 hw (fun i => φ (c i)) ?_ i
    ext m
    have := congrArg (fun F => φ (coeff m F)) hc
    simp only [coeff_sum, map_sum, coeff_zero, map_zero] at this ⊢
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← coeff_contr, contr_smul_map]
  have hsp : extSub L W = Submodule.span L (Set.range v) := by
    apply le_antisymm
    · intro F hF
      let b := Basis.ofVectorSpace K L
      have : F = ∑ j ∈ F.support.biUnion fun m => (b.repr (coeff m F)).support,
          b j • map (algebraMap K L) (contr (b.coord j) F) := by
        ext m
        simp only [coeff_sum, coeff_smul, coeff_map, coeff_contr, smul_eq_mul]
        conv_lhs => rw [← b.linearCombination_repr (coeff m F), Finsupp.linearCombination_apply]
        rw [Finsupp.sum_of_support_subset (s := F.support.biUnion
          fun m => (b.repr (coeff m F)).support) _ _ _ (by simp)]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [Algebra.smul_def, mul_comm, Basis.coord_apply]
        · by_cases hm : m ∈ F.support
          · exact Finset.subset_biUnion_of_mem (fun m => (b.repr (coeff m F)).support) hm
          · simp [notMem_support_iff.1 hm]
      rw [this]
      refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
      have h1 := congrArg W.subtype (w.sum_repr ⟨_, hF (b.coord j)⟩)
      simp only [map_sum, map_smul, Submodule.subtype_apply] at h1
      rw [← h1, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smul_eq_C_mul, map_mul, map_C, C_mul']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩ φ
      rw [contr_map]
      exact W.smul_mem _ (w i).2
  rw [hsp, finrank_span_eq_card hli, Fintype.card_fin]

theorem contr_isHomogeneous (φ : L →ₗ[K] K) {e : ℕ} {F : MvPolynomial σ L}
    (hF : F.IsHomogeneous e) : (contr φ F).IsHomogeneous e := by
  rw [← homogeneousComponent_eq_self hF, contr_comp]
  exact homogeneousComponent_isHomogeneous _ _

theorem piece_extIdeal (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    piece (extIdeal L I) e = extSub L (piece I e) := by
  ext F
  refine ⟨fun hF φ => ⟨contr_isHomogeneous φ hF.1, hF.2 φ⟩, fun hF => ⟨?_, fun φ => (hF φ).2⟩⟩
  have : F = homogeneousComponent e F := eq_of_contr (K := K) fun φ => by
    rw [contr_comp, homogeneousComponent_eq_self (hF φ).1]
  rw [this]
  exact homogeneousComponent_isHomogeneous _ _

theorem mem_genIn_of_map {I : Ideal (MvPolynomial σ K)} {e : ℕ} {F : MvPolynomial σ K}
    (h : map (algebraMap K L) F ∈ genIn (extIdeal L I) e) : F ∈ genIn I e := by
  have h1 : genIn (extIdeal L I) e ≤ extIdeal L (genIn I e) :=
    Ideal.span_le.2 fun G hG φ => Ideal.subset_span ⟨hG.1 φ, contr_isHomogeneous φ hG.2⟩
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : L) ≠ 0)
  have := h1 h φ
  rwa [contr_map, hφ, one_smul] at this

end BaseChange

end GlobalTheory.RegBound

namespace GlobalTheory

open RegBound in

theorem exists_uniform_regularity_bound :
    ∀ (σ : Type) [Finite σ] (Q : Polynomial ℚ), ∃ d₀ : ℕ, ∀ (K : Type) [Field K] (I : Ideal (MvPolynomial σ K)), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → (∀ F, (∀ i, MvPolynomial.X i * F ∈ I) → F ∈ I) → (∀ᶠ e in Filter.atTop, (Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e ⊓ I.restrictScalars K) : ℚ) = Q.eval (e : ℚ)) → ∀ e ≥ d₀, (Module.finrank K ↥(MvPolynomial.homogeneousSubmodule σ K e ⊓ I.restrictScalars K) : ℚ) = Q.eval (e : ℚ) ∧ ∀ F ∈ I, F.IsHomogeneous e → F ∈ Ideal.span {G | G ∈ I ∧ G.IsHomogeneous d₀} := by
  intro σ _ Q
  obtain ⟨d, hd⟩ := bound_infinite σ (nmon σ 1) fun e => Q.eval (e : ℚ)
  refine ⟨d, fun K _ I hI hsat hq => ?_⟩
  haveI : Infinite (AlgebraicClosure K) := IsAlgClosed.instInfinite
  have hdim : ∀ e, finrank (AlgebraicClosure K) (piece (extIdeal (AlgebraicClosure K) I) e) =
      finrank K (piece I e) := fun e => by rw [piece_extIdeal, finrank_extSub]
  have h := hd (AlgebraicClosure K) (extIdeal (AlgebraicClosure K) I)
    (fun F hF e φ => by rw [contr_comp]; exact hI _ (hF φ) e)
    (fun F hF φ => hsat _ fun i => by rw [← contr_X_mul]; exact hF i φ)
    (Nat.le_add_left _ _) (by simpa only [hdim] using hq)
  simp only [hdim] at h
  intro e he
  refine ⟨(h e he).1, ?_⟩
  induction e, he using Nat.le_induction with
  | base => exact fun F hF hFe => Ideal.subset_span ⟨hF, hFe⟩
  | succ n hn ih =>
    intro F hF hFe
    refine (Ideal.span_le.2 fun G hG => ih G hG.1 hG.2 : genIn I n ≤ genIn I d) ?_
    refine mem_genIn_of_map (L := AlgebraicClosure K) ((h n hn).2 _ (fun φ => ?_) (hFe.map _))
    rw [contr_map, smul_eq_C_mul]
    exact I.mul_mem_left _ hF

end GlobalTheory
