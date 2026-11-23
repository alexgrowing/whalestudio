import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IntegralFiniteAdeleCompactClosedMultiples
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSumIntegralBasis
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CoordDivisible
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.AdeleFree

section Abstract

variable {A : Type} [CommRing A]

def intClosure (O : Subring A) : Subring A where
  carrier := {r | ∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : A), c ∈ O ∧ r = (z : A) + (M : A) * c}
  mul_mem' := by
    intro a b ha hb M hM
    obtain ⟨z, c, hc, rfl⟩ := ha M hM
    obtain ⟨z', c', hc', rfl⟩ := hb M hM
    refine ⟨z * z', z * c' + c * z' + M * (c * c'), ?_, by push_cast; ring⟩
    exact add_mem (add_mem (mul_mem (intCast_mem _ _) hc') (mul_mem hc (intCast_mem _ _)))
      (mul_mem (natCast_mem _ _) (mul_mem hc hc'))
  one_mem' := fun M _ => ⟨1, 0, zero_mem _, by simp⟩
  add_mem' := by
    intro a b ha hb M hM
    obtain ⟨z, c, hc, rfl⟩ := ha M hM
    obtain ⟨z', c', hc', rfl⟩ := hb M hM
    exact ⟨z + z', c + c', add_mem hc hc', by push_cast; ring⟩
  zero_mem' := fun M _ => ⟨0, 0, zero_mem _, by simp⟩
  neg_mem' := by
    intro a ha M hM
    obtain ⟨z, c, hc, rfl⟩ := ha M hM
    exact ⟨-z, -c, neg_mem hc, by push_cast; ring⟩

theorem intClosure_le (O : Subring A) {a : A} (ha : a ∈ intClosure O) : a ∈ O := by
  obtain ⟨z, c, hc, rfl⟩ := ha 1 one_pos
  exact add_mem (intCast_mem _ _) (by simpa using hc)

def ratSpan (Z : Subring A) : Subring A where
  carrier := {a | ∃ M : ℕ, 0 < M ∧ (M : A) * a ∈ Z}
  mul_mem' := by
    rintro a b ⟨M, hM, ha⟩ ⟨N, hN, hb⟩
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    have : ((M * N : ℕ) : A) * (a * b) = (M * a) * (N * b) := by push_cast; ring
    rw [this]; exact mul_mem ha hb
  one_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro a b ⟨M, hM, ha⟩ ⟨N, hN, hb⟩
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    have : ((M * N : ℕ) : A) * (a + b) = N * (M * a) + M * (N * b) := by push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ _) ha) (mul_mem (natCast_mem _ _) hb)
  zero_mem' := ⟨1, one_pos, by simp⟩
  neg_mem' := by
    rintro a ⟨M, hM, ha⟩
    exact ⟨M, hM, by rw [mul_neg]; exact neg_mem ha⟩

theorem mem_ratSpan {Z : Subring A} {a : A} (ha : a ∈ Z) : a ∈ ratSpan Z :=
  ⟨1, one_pos, by simpa using ha⟩

theorem den_mul (φ : ℚ →+* A) (q : ℚ) : (q.den : A) * φ q = (q.num : A) := by
  rw [← map_natCast φ q.den, ← map_mul, Rat.den_mul_eq_num, map_intCast]

theorem rat_mem (φ : ℚ →+* A) (Z : Subring A) (q : ℚ) : φ q ∈ ratSpan Z :=
  ⟨q.den, q.den_pos, by rw [den_mul]; exact intCast_mem _ _⟩

theorem inv_mul (φ : ℚ →+* A) {N : ℕ} (hN : 0 < N) : φ (N : ℚ)⁻¹ * (N : A) = 1 := by
  rw [← map_natCast φ N, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]

theorem cancel (φ : ℚ →+* A) {N : ℕ} (hN : 0 < N) {a b : A} (h : (N : A) * a = N * b) :
    a = b :=
  calc a = (φ (N : ℚ)⁻¹ * N) * a := by rw [inv_mul φ hN, one_mul]
    _ = φ (N : ℚ)⁻¹ * (N * a) := mul_assoc _ _ _
    _ = φ (N : ℚ)⁻¹ * (N * b) := by rw [h]
    _ = b := by rw [← mul_assoc, inv_mul φ hN, one_mul]

theorem mem_of_mul (φ : ℚ →+* A) (O : Subring A)
    (hint : ∀ (z : ℤ) (N : ℕ), 0 < N → ∀ e ∈ O, (z : A) = N * e → (N : ℤ) ∣ z)
    {N : ℕ} (hN : 0 < N) {c : A} (hc : c ∈ O) (h : (N : A) * c ∈ intClosure O) :
    c ∈ intClosure O := by
  intro M hM
  obtain ⟨z, d, hd, hzd⟩ := h (N * M) (Nat.mul_pos hN hM)
  have hz : (z : A) = N * (c - M * d) := by rw [mul_sub, hzd]; push_cast; ring
  obtain ⟨y, rfl⟩ := hint z N hN (c - M * d) (sub_mem hc (mul_mem (natCast_mem _ _) hd)) hz
  refine ⟨y, d, hd, cancel φ hN ?_⟩
  rw [hzd]; push_cast; ring

theorem exists_basis (φ : ℚ →+* A) (O : Subring A) [IsReduced A] {β : Type} [Fintype β]
    (w : β → A) (hw : ∀ i, w i ∈ O)
    (hint : ∀ (z : ℤ) (N : ℕ), 0 < N → ∀ e ∈ O, (z : A) = N * e → (N : ℤ) ∣ z)
    (h0 : ∀ a : A, (∀ M : ℕ, 0 < M → ∃ c, c ∈ O ∧ a = (M : A) * c) → a = 0)
    (hden : ∀ a : A, ∃ M : ℕ, 0 < M ∧ (M : A) * a ∈ O)
    (hspan : ∀ a ∈ O, ∃ r : β → A, (∀ i, r i ∈ intClosure O) ∧ a = ∑ i, r i * w i)
    (hdiv : ∀ (r : β → A) (N : ℕ), 0 < N → (∀ i, r i ∈ intClosure O) →
      (∃ e, e ∈ O ∧ ∑ i, r i * w i = (N : A) * e) →
        ∀ i, ∃ s, s ∈ intClosure O ∧ r i = (N : A) * s) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℚ R) (R₀ : Subring R) (_ : Algebra R A)
      (b : Module.Basis β R A), AdelicPair R R₀ ∧ IsReduced R ∧ (∀ i, b i = w i) ∧
        ∀ a : A, a ∈ O ↔ ∀ i, b.repr a i ∈ R₀ := by
  classical

  set Z := intClosure O with hZdef
  set R := ratSpan Z with hRdef
  have hZO : ∀ x ∈ Z, x ∈ O := fun x hx => intClosure_le O hx
  have hZR : ∀ x ∈ Z, x ∈ R := fun x hx => mem_ratSpan hx
  let φR : ℚ →+* R := φ.codRestrict R (rat_mem φ Z)
  let _ : Algebra ℚ R := φR.toAlgebra
  let _ : Algebra R A := (Subring.subtype R).toAlgebra
  have hsmul : ∀ (c : R) (x : A), c • x = (c : A) * x := fun _ _ => rfl
  let R₀ : Subring R := Z.comap (Subring.subtype R)
  have hmemR : ∀ c : R, ∃ M : ℕ, 0 < M ∧ (M : A) * c ∈ Z := fun c => c.2

  have hli : LinearIndependent R w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    choose M hM hMc using fun j => hmemR (c j)
    set K := ∏ j, M j with hKdef
    have hK : 0 < K := Finset.prod_pos fun j _ => hM j
    have hr : ∀ j, (K : A) * c j ∈ Z := by
      intro j
      have hsplit : (K : A) * c j = ((∏ k ∈ Finset.univ.erase j, M k : ℕ) : A) * ((M j : A) * c j) := by
        rw [← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
      rw [hsplit]
      exact mul_mem (natCast_mem _ _) (hMc j)
    have hc' : ∑ j, (c j : A) * w j = 0 := by simpa only [hsmul] using hc
    have hsum : ∑ j, ((K : A) * c j) * w j = 0 := by
      simp only [mul_assoc]
      rw [← Finset.mul_sum, hc', mul_zero]
    have hzero : (K : A) * c i = 0 := by
      apply h0
      intro N hN
      obtain ⟨s, hs, hrs⟩ := hdiv (fun j => (K : A) * c j) N hN hr
        ⟨0, zero_mem _, by rw [hsum, mul_zero]⟩ i
      exact ⟨s, hZO s hs, hrs⟩
    exact Subtype.ext (cancel φ hK (by rw [hzero]; simp))

  have hsp : ⊤ ≤ Submodule.span R (Set.range w) := by
    rintro a -
    obtain ⟨M, hM, hMa⟩ := hden a
    obtain ⟨r, hr, hra⟩ := hspan _ hMa
    have hmem : ∀ i, φ (M : ℚ)⁻¹ * r i ∈ R := fun i =>
      ⟨M, hM, by rw [← mul_assoc, mul_comm (M : A) (φ _), inv_mul φ hM, one_mul]; exact hr i⟩
    have ha : a = ∑ i, (⟨φ (M : ℚ)⁻¹ * r i, hmem i⟩ : R) • w i := by
      simp only [hsmul]
      apply cancel φ hM
      rw [hra, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← mul_assoc, mul_comm (M : A) (φ _), inv_mul φ hM, one_mul]
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b : Module.Basis β R A := Module.Basis.mk hli hsp
  have hb : ∀ i, b i = w i := fun i => Module.Basis.mk_apply hli hsp i
  refine ⟨R, inferInstance, inferInstance, R₀, inferInstance, b, ?_, ?_, hb, ?_⟩
  ·
    refine ⟨?_, ?_⟩
    · intro q hq
      have hq' : φ q ∈ Z := hq
      obtain ⟨z, c, hc, hzc⟩ := hq' q.den q.den_pos
      have h1 : ((q.num - q.den * z : ℤ) : A) = (q.den : A) * ((q.den : A) * c) := by
        push_cast
        rw [← den_mul φ q, hzc]
        ring
      have h2 := hint _ q.den q.den_pos _ (mul_mem (natCast_mem _ _) hc) h1
      have h3 : (q.den : ℤ) ∣ q.num := by
        have h4 := dvd_add h2 (dvd_mul_right (q.den : ℤ) z)
        simpa using h4
      have h5 : q.den = 1 :=
        Nat.eq_one_of_dvd_coprimes q.reduced.symm dvd_rfl (Int.natCast_dvd.mp h3)
      exact ⟨q.num, ((Rat.den_eq_one_iff q).mp h5).symm⟩
    · intro M hM r
      obtain ⟨K, hK, hKr⟩ := hmemR r
      obtain ⟨z, c, hc, hzc⟩ := hKr (K * M) (Nat.mul_pos hK hM)
      have hcZ : c ∈ Z := by
        apply mem_of_mul φ O hint (Nat.mul_pos hK hM) hc
        have hkm : ((K * M : ℕ) : A) * c = (K : A) * r - z := by rw [hzc]; ring
        rw [hkm]
        exact sub_mem hKr (intCast_mem _ _)
      refine ⟨(z : ℚ) / K, ⟨c, hZR c hcZ⟩, hcZ, ?_⟩
      apply Subtype.ext
      have hk : (K : A) * φ ((z : ℚ) / K) = z := by
        rw [← map_natCast φ K, ← map_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hK.ne'),
          map_intCast]
      change (r : A) = φ ((z : ℚ) / K) + (M : A) * c
      apply cancel φ hK
      rw [hzc, mul_add, hk]
      push_cast
      ring
  · exact isReduced_of_injective (Subring.subtype R) Subtype.val_injective
  · intro a
    have hrep : a = ∑ i, (b.repr a i : A) * w i := by
      conv_lhs => rw [← b.sum_repr a]
      simp only [hsmul, hb]
    constructor
    · intro ha i
      obtain ⟨r, hr, hra⟩ := hspan a ha
      let c : β → R := fun j => ⟨r j, hZR _ (hr j)⟩
      have hdiff : ∑ j, (b.repr a j - c j) • b j = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, b.sum_repr]
        rw [sub_eq_zero]
        simp only [hsmul, hb]
        exact hra
      have h := Fintype.linearIndependent_iff.1 b.linearIndependent _ hdiff i
      rw [sub_eq_zero.1 h]
      exact hr i
    · intro h
      rw [hrep]
      exact Subring.sum_mem _ fun i _ => mul_mem (hZO _ (h i)) (hw i)

end Abstract

theorem finiteAdele_free : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)), ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℚ R) (R₀ : Subring R) (_ : Algebra R (FiniteAdeleRing (𝓞 F) F)) (b : Module.Basis β R (FiniteAdeleRing (𝓞 F) F)), AdelicPair R R₀ ∧ IsReduced R ∧ (∀ i, b i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F)) ∧ ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ↔ ∀ i, b.repr a i ∈ R₀ := by
  intro F _ _ β _ ω
  classical
  obtain ⟨-, -, hz0, -, hden, hred⟩ := GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F
  have : IsReduced (FiniteAdeleRing (𝓞 F) F) := hred
  let O : Subring (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.CoordDiv.intAdeles F
  have hint : ∀ (z : ℤ) (N : ℕ), 0 < N → ∀ e ∈ O,
      (z : FiniteAdeleRing (𝓞 F) F) = N * e → (N : ℤ) ∣ z := by
    intro z N hN e he h
    obtain ⟨a, ha⟩ := GlobalTheory.CoordDiv.dvd_of_eq F (z : 𝓞 F) N hN e he (by simpa using h)
    exact GlobalTheory.CoordDiv.int_dvd F z N a ha
  obtain ⟨R, i1, i2, R₀, i3, b, hP, hR, hb, hmem⟩ :=
    exists_basis ((algebraMap F (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap ℚ F)) O
      (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F))
      (fun i => GlobalTheory.CoordDiv.algebraMap_mem F (ω i)) hint (fun a ha => hz0 a ha) (fun a => hden a)
      (fun a ha => GlobalTheory.ClassFin.exists_sum_integralBasis F β ω a ha)
      (fun r N hN hr he => GlobalTheory.CoordDiv.coord_divisible F β ω r N hN hr he)
  exact ⟨R, i1, i2, R₀, i3, b, hP, hR, hb, fun a => hmem a⟩

end GlobalTheory.AdeleFree
