import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAffineOpenRingPolynomialEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureProjectiveOverStandardOpenRingStatement

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open RingTheory.Sequence
open scoped TensorProduct

section LocRegAux

variable {L : Type} [Field L] [Algebra ℂ L]

private lemma le_loc (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) : B ≤ loc B e := fun b hb =>
  ⟨1, by simp, by simpa using hb⟩

end LocRegAux

private theorem isWeaklyRegular_mvPolynomial_X (k : Type) [Field k] (d : ℕ) :
    IsWeaklyRegular (MvPolynomial (Fin d) k)
      (List.ofFn (MvPolynomial.X : Fin d → MvPolynomial (Fin d) k)) := by
  rw [isWeaklyRegular_iff_Fin]
  intro i
  have hlen : i.val < d := by simpa using i.isLt
  have hI : (Ideal.ofList ((List.ofFn (MvPolynomial.X : Fin d → MvPolynomial (Fin d) k)).take i) •
      (⊤ : Submodule (MvPolynomial (Fin d) k) (MvPolynomial (Fin d) k))) =
      Ideal.span (MvPolynomial.X '' {j : Fin d | j.val < i.val}) := by
    rw [smul_eq_mul, Ideal.mul_top, Ideal.ofList]
    congr 1
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_image, List.mem_take_iff_getElem, List.getElem_ofFn,
      List.length_ofFn]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, by omega⟩, by simp; omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.val, by omega, rfl⟩
  have hget : (List.ofFn (MvPolynomial.X : Fin d → MvPolynomial (Fin d) k))[i] =
      MvPolynomial.X ⟨i.val, hlen⟩ := by
    rw [Fin.getElem_fin, List.getElem_ofFn]
  rw [hI, hget]
  refine isSMulRegular_iff_right_eq_zero_of_smul.mpr ?_
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H p =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    rw [smul_eq_mul, MvPolynomial.mem_ideal_span_X_image] at hq
    rw [MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have hm' : m + Finsupp.single (⟨i.val, hlen⟩ : Fin d) 1 ∈
        (MvPolynomial.X (⟨i.val, hlen⟩ : Fin d) * p).support := by
      rw [MvPolynomial.mem_support_iff, mul_comm, MvPolynomial.coeff_mul_X]
      exact MvPolynomial.mem_support_iff.mp hm
    obtain ⟨j, hj, hne⟩ := hq _ hm'
    refine ⟨j, hj, ?_⟩
    have hji : j ≠ ⟨i.val, hlen⟩ := by
      intro h
      subst h
      simp at hj
    simpa [Finsupp.single_apply, Ne.symm hji] using hne

private theorem mem_span_image_lt_iff_exists_sum {S : Type} [CommRing S] {d : ℕ} (τ : Fin d → S) (k : Fin d)
    (x : S) : x ∈ Ideal.span (τ '' {j | j < k}) ↔
      ∃ c : Fin d → S, x = ∑ j ∈ Finset.univ.filter (· < k), τ j * c j := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      refine ⟨Pi.single j 1, ?_⟩
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩) h
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c1, rfl⟩ := hy
      obtain ⟨c2, rfl⟩ := hz
      exact ⟨c1 + c2, by simp [mul_add, Finset.sum_add_distrib]⟩
    | smul r y _ hy =>
      obtain ⟨c, rfl⟩ := hy
      refine ⟨fun j => r * c j, ?_⟩
      rw [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  · rintro ⟨c, rfl⟩
    exact Ideal.sum_mem _ fun j hj =>
      Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, (Finset.mem_filter.mp hj).2, rfl⟩)

private theorem mem_span_image_lt_of_mul_mem_of_weaklyRegular {S : Type} [CommRing S] {d : ℕ} (τ : Fin d → S)
    (h : IsWeaklyRegular S (List.ofFn τ)) (k : Fin d) (a : S)
    (ha : τ k * a ∈ Ideal.span (τ '' {j | j < k})) : a ∈ Ideal.span (τ '' {j | j < k}) := by
  have h1 := (isWeaklyRegular_iff_Fin _ _).mp h ⟨k.val, by simp⟩
  have hI : (Ideal.ofList ((List.ofFn τ).take k.val) • (⊤ : Submodule S S)) =
      Ideal.span (τ '' {j | j < k}) := by
    rw [smul_eq_mul, Ideal.mul_top, Ideal.ofList]
    congr 1
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_image, List.mem_take_iff_getElem, List.getElem_ofFn,
      List.length_ofFn]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, by omega⟩, Fin.mk_lt_of_lt_val (by omega), rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.val, by rw [Fin.lt_def] at hj; omega, rfl⟩
  have hget : (List.ofFn τ)[(⟨k.val, by simp⟩ : Fin (List.ofFn τ).length)] = τ k := by
    rw [Fin.getElem_fin, List.getElem_ofFn]
  rw [hI, hget] at h1
  have hz := h1 (a₁ := Submodule.Quotient.mk a) (a₂ := 0) (by
    beta_reduce
    rw [smul_zero, ← Submodule.Quotient.mk_smul, smul_eq_mul, Submodule.Quotient.mk_eq_zero]
    exact ha)
  exact (Submodule.Quotient.mk_eq_zero _).mp hz

private theorem exists_integral_coeffs_of_algebraMap_mul_eq_sum {R0 L : Type} [CommRing R0] [Field L] [Algebra R0 L] {d : ℕ}
    (τ0 : Fin d → R0) (r0 : IsWeaklyRegular R0 (List.ofFn τ0))
    (hp : Module.Projective R0 (integralClosure R0 L)) (i : Fin d) (a : L)
    (ha : a ∈ integralClosure R0 L) (c : Fin d → L) (hc : ∀ j, c j ∈ integralClosure R0 L)
    (h : algebraMap R0 L (τ0 i) * a =
      ∑ j ∈ Finset.univ.filter (· < i), algebraMap R0 L (τ0 j) * c j) :
    ∃ b : Fin d → L, (∀ j, b j ∈ integralClosure R0 L) ∧
      a = ∑ j ∈ Finset.univ.filter (· < i), algebraMap R0 L (τ0 j) * b j := by
  haveI : Module.Flat R0 (integralClosure R0 L) := Module.Flat.of_projective
  have r1 := r0.of_flat (S := integralClosure R0 L)
  rw [List.map_ofFn] at r1
  let τ : Fin d → integralClosure R0 L := fun j => algebraMap R0 (integralClosure R0 L) (τ0 j)
  have hτ : ∀ j, (τ j : L) = algebraMap R0 L (τ0 j) := fun j => rfl
  have key := mem_span_image_lt_of_mul_mem_of_weaklyRegular τ r1 i ⟨a, ha⟩ ((mem_span_image_lt_iff_exists_sum τ i _).mpr
    ⟨fun j => ⟨c j, hc j⟩, Subtype.ext (by simpa [hτ] using h)⟩)
  obtain ⟨b, hb⟩ := (mem_span_image_lt_iff_exists_sum τ i _).mp key
  refine ⟨fun j => (b j : L), fun j => (b j).2, ?_⟩
  have := congrArg (fun y : integralClosure R0 L => (y : L)) hb
  simpa [hτ] using this

private theorem exists_rB_coeffs_of_tt_mul_eq_sum (k : Type) [Field k] [CharZero k] (F L : Type) [Field F] [Field L]
    [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L] (d : ℕ) (x : Fin (d + 1) → Fˣ)
    (hc : IsFinCover k L (xv x)) (i : Fin d) (a : L) (ha : a ∈ rB k L (xv x) {0})
    (c : Fin d → L) (hc' : ∀ j, c j ∈ rB k L (xv x) {0})
    (h : tt L x i * a = ∑ j ∈ Finset.univ.filter (· < i), tt L x j * c j) :
    ∃ b : Fin d → L, (∀ j, b j ∈ rB k L (xv x) {0}) ∧
      a = ∑ j ∈ Finset.univ.filter (· < i), tt L x j * b j := by
  obtain ⟨e0, he0⟩ := GlobalTheory.T.standardAffineOpen_ring_polynomialEquiv k F d (xv x) hc.pd 0
  let τ0 : Fin d → rA k (xv x) {0} := fun j => e0 (MvPolynomial.X j)
  have r0 : IsWeaklyRegular (rA k (xv x) {0}) (List.ofFn τ0) := by
    have hl : List.ofFn τ0 = (List.ofFn MvPolynomial.X).map e0 := by
      rw [List.map_ofFn]
      rfl
    rw [hl]
    refine (e0.toAddEquiv.isWeaklyRegular_congr ?_).mp (isWeaklyRegular_mvPolynomial_X k d)
    refine List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun r _ y => ?_)
    show e0 (r * y) = e0 r * e0 y
    exact map_mul e0 r y
  have hτ : ∀ j, algebraMap (rA k (xv x) {0}) L (τ0 j) = tt L x j := by
    intro j
    show algebraMap F L ((e0 (MvPolynomial.X j) : F)) = _
    rw [he0 j, Fin.succAbove_zero]
    rfl
  obtain ⟨b, hb, hab⟩ := exists_integral_coeffs_of_algebraMap_mul_eq_sum τ0 r0 (GlobalTheory.T.integralClosure_projective_over_standardOpenRing k F L d (xv x) hc 0) i a ha c hc'
    (by simpa [hτ] using h)
  exact ⟨b, hb, by simpa [hτ] using hab⟩

private theorem exists_loc_coeffs_of_mul_eq_sum {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    (e : B →ₐ[ℂ] ℂ) {d : ℕ} (t : Fin d → L) (i : Fin d)
    (hB : ∀ a : L, a ∈ B → ∀ c : Fin d → L, (∀ j, c j ∈ B) →
      t i * a = ∑ j ∈ Finset.univ.filter (· < i), t j * c j →
      ∃ b : Fin d → L, (∀ j, b j ∈ B) ∧ a = ∑ j ∈ Finset.univ.filter (· < i), t j * b j)
    (a : L) (ha : a ∈ loc B e) (c : Fin d → L) (hc : ∀ j, c j ∈ loc B e)
    (h : t i * a = ∑ j ∈ Finset.univ.filter (· < i), t j * c j) :
    ∃ b : Fin d → L, (∀ j, b j ∈ loc B e) ∧
      a = ∑ j ∈ Finset.univ.filter (· < i), t j * b j := by
  have ha' : ∃ u : B, e u ≠ 0 ∧ (u : L) * a ∈ B := ha
  have hc' : ∀ j, ∃ u : B, e u ≠ 0 ∧ (u : L) * c j ∈ B := hc
  obtain ⟨u0, hu0, hau⟩ := ha'
  choose u hu hcu using hc'
  set s : B := u0 * ∏ j, u j with hs
  have hes : e s ≠ 0 := by
    rw [hs, map_mul, map_prod]
    exact mul_ne_zero hu0 (Finset.prod_ne_zero_iff.mpr fun j _ => hu j)
  have hs0 : (s : L) ≠ 0 := by
    intro h0
    apply hes
    have : s = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hsa : (s : L) * a ∈ B := by
    have : (s : L) * a = ((∏ j, u j : B) : L) * ((u0 : L) * a) := by
      rw [hs]
      push_cast
      ring
    rw [this]
    exact B.mul_mem (∏ j, u j).2 hau
  have hsc : ∀ j, (s : L) * c j ∈ B := by
    intro j
    have : (s : L) * c j = ((u0 * ∏ l ∈ Finset.univ.erase j, u l : B) : L) * ((u j : L) * c j) := by
      rw [hs, ← Finset.mul_prod_erase Finset.univ u (Finset.mem_univ j)]
      push_cast
      ring
    rw [this]
    exact B.mul_mem (u0 * ∏ l ∈ Finset.univ.erase j, u l).2 (hcu j)
  have hsh : t i * ((s : L) * a) = ∑ j ∈ Finset.univ.filter (· < i), t j * ((s : L) * c j) := by
    have := congrArg (fun y => (s : L) * y) h
    simp only [Finset.mul_sum] at this
    rw [show t i * ((s : L) * a) = (s : L) * (t i * a) by ring, this]
    exact Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨b, hb, hab⟩ := hB _ hsa _ hsc hsh
  refine ⟨fun j => b j * (s : L)⁻¹, fun j => ?_, ?_⟩
  · show ∃ u : B, e u ≠ 0 ∧ (u : L) * (b j * (s : L)⁻¹) ∈ B
    refine ⟨s, hes, ?_⟩
    rw [show (s : L) * (b j * (s : L)⁻¹) = b j by field_simp]
    exact hb j
  · have : a = (s : L)⁻¹ * ((s : L) * a) := by field_simp
    rw [this, hab, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem UpperTheory.Gal.productCup_of_system.locReg_of :
    LocForms → DtBasic → ValBasic → LocReg := by
  intro hLF _ _ F L _ _ _ _ _ _ d x hcov hred e
  have hM : ∀ m : DR ℂ L, m ∈ omB ℂ L (loc (rB ℂ L (xv x) {0}) e.1) d ↔
      ∃ a ∈ loc (rB ℂ L (xv x) {0}) e.1, m = a • dtS L x Finset.univ := by
    intro m
    have hp : Finset.powersetCard d (Finset.univ : Finset (Fin d)) = {Finset.univ} := by
      simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin d))
    rw [hLF F L d x hcov hred e d m]
    simp only [hp, Finset.sum_singleton]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c Finset.univ, hc _, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨fun _ => a, fun _ => ha, rfl⟩
  intro k m hm hkm
  have hadd : ∀ y1 y2 : DR ℂ L,
      (∃ c : Fin d → L, (∀ j, c j ∈ loc (rB ℂ L (xv x) {0}) e.1) ∧
        y1 = (∑ j ∈ Finset.univ.filter (· < k), tt L x j * c j) • dtS L x Finset.univ) →
      (∃ c : Fin d → L, (∀ j, c j ∈ loc (rB ℂ L (xv x) {0}) e.1) ∧
        y2 = (∑ j ∈ Finset.univ.filter (· < k), tt L x j * c j) • dtS L x Finset.univ) →
      (∃ c : Fin d → L, (∀ j, c j ∈ loc (rB ℂ L (xv x) {0}) e.1) ∧
        y1 + y2 = (∑ j ∈ Finset.univ.filter (· < k), tt L x j * c j) • dtS L x Finset.univ) := by
    rintro y1 y2 ⟨c1, hc1, rfl⟩ ⟨c2, hc2, rfl⟩
    exact ⟨c1 + c2, fun j => Subalgebra.add_mem _ (hc1 j) (hc2 j),
      by simp [mul_add, Finset.sum_add_distrib, add_smul]⟩
  have hsm : ∀ w ∈ sm (Algebra.lsmul ℂ ℂ (DR ℂ L)) (omB ℂ L (loc (rB ℂ L (xv x) {0}) e.1) d)
      (tt L x '' {j | j < k}), ∃ c : Fin d → L, (∀ j, c j ∈ loc (rB ℂ L (xv x) {0}) e.1) ∧
        w = (∑ j ∈ Finset.univ.filter (· < k), tt L x j * c j) • dtS L x Finset.univ := by
    intro w hw
    unfold sm at hw
    refine Submodule.iSup_induction (motive := fun y => ∃ c : Fin d → L, (∀ j, c j ∈ loc (rB ℂ L (xv x) {0}) e.1) ∧
        y = (∑ j ∈ Finset.univ.filter (· < k), tt L x j * c j) • dtS L x Finset.univ) _ hw (fun r y hy => ?_)
      ⟨0, fun _ => Subalgebra.zero_mem _, by simp⟩ hadd
    refine Submodule.iSup_induction (motive := fun y => ∃ c : Fin d → L, (∀ j, c j ∈ loc (rB ℂ L (xv x) {0}) e.1) ∧
        y = (∑ j ∈ Finset.univ.filter (· < k), tt L x j * c j) • dtS L x Finset.univ) _ hy (fun hr z hz => ?_)
      ⟨0, fun _ => Subalgebra.zero_mem _, by simp⟩ hadd
    obtain ⟨j0, hj0, rfl⟩ := hr
    obtain ⟨m', hm', rfl⟩ := hz
    obtain ⟨a, ha, rfl⟩ := (hM m').mp hm'
    refine ⟨Pi.single j0 a, fun j => ?_, ?_⟩
    · by_cases hj : j = j0
      · subst hj
        simpa using ha
      · simp only [Pi.single_apply, hj, if_false]
        exact Subalgebra.zero_mem _
    · rw [Finset.sum_eq_single j0]
      · simp only [Pi.single_eq_same]
        exact smul_smul _ _ _
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0⟩) h
  obtain ⟨a, ha, rfl⟩ := (hM m).mp hm
  obtain ⟨c, hc, hcw⟩ := hsm _ hkm
  by_cases hω : dtS L x Finset.univ = 0
  · rw [hω, smul_zero]
    exact Submodule.zero_mem _
  have heq : tt L x k * a = ∑ j ∈ Finset.univ.filter (· < k), tt L x j * c j := by
    have h2 : (tt L x k * a) • dtS L x Finset.univ =
        (∑ j ∈ Finset.univ.filter (· < k), tt L x j * c j) • dtS L x Finset.univ := by
      rw [← smul_smul]
      exact hcw
    exact smul_left_injective L hω h2
  obtain ⟨b, hb, hab⟩ := exists_loc_coeffs_of_mul_eq_sum _ _ (tt L x) k
    (fun a' ha' c' hc' h' => exists_rB_coeffs_of_tt_mul_eq_sum ℂ F L d x hcov k a' ha' c' hc' h') a ha c hc heq
  rw [hab, Finset.sum_smul]
  refine Submodule.sum_mem _ fun j hj => ?_
  unfold sm
  refine Submodule.mem_iSup_of_mem (tt L x j)
    (Submodule.mem_iSup_of_mem ⟨j, (Finset.mem_filter.mp hj).2, rfl⟩ ?_)
  exact ⟨b j • dtS L x Finset.univ, (hM _).mpr ⟨b j, hb j, rfl⟩, smul_smul _ _ _⟩
