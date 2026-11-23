import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsPowReductionCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

open Polynomial IsLocalRing

namespace PrincipalReductionOfBoundedGens

section Relation

variable {S : Type*} [CommRing S]

theorem mem_radical_of_relation (y z : S) (α D : ℕ) (c : ℕ → S) (hc0 : IsUnit (c 0))
    (h : y ^ α * ∑ i ∈ Finset.range (D + 1), c i * y ^ i * z ^ (D - i) = 0) :
    y ∈ (Ideal.span {y ^ (D + 1) + z * ∑ i ∈ Finset.range (D + 1), c i * y ^ i * z ^ (D - i)}).radical ∧
    z ∈ (Ideal.span {y ^ (D + 1) + z * ∑ i ∈ Finset.range (D + 1), c i * y ^ i * z ^ (D - i)}).radical := by
  set G := ∑ i ∈ Finset.range (D + 1), c i * y ^ i * z ^ (D - i) with hG
  obtain ⟨H, hH⟩ : ∃ H, G = c 0 * z ^ D + y * H := by
    refine ⟨∑ i ∈ Finset.range D, c (i + 1) * y ^ i * z ^ (D - (i + 1)), ?_⟩
    rw [hG, Finset.sum_range_succ', Finset.mul_sum, add_comm]
    congr 1
    · simp
    · exact Finset.sum_congr rfl fun i _ => by ring
  have key : ∀ P : Ideal S, P.IsPrime → y ^ (D + 1) + z * G ∈ P → y ∈ P ∧ z ∈ P := by
    intro P hP hw
    have hy : y ∈ P := by
      by_contra hy
      have hGP : G ∈ P := by
        have : y ^ α * G ∈ P := by rw [h]; exact P.zero_mem
        exact (hP.mem_or_mem this).resolve_left fun h' => hy (hP.mem_of_pow_mem _ h')
      have : y ^ (D + 1) ∈ P := by
        have := P.sub_mem hw (P.mul_mem_left z hGP)
        simpa using this
      exact hy (hP.mem_of_pow_mem _ this)
    refine ⟨hy, ?_⟩
    have h1 : z * G ∈ P := by
      have := P.sub_mem hw (P.pow_mem_of_mem hy (D + 1) (Nat.succ_pos _))
      simpa using this
    have h2 : c 0 * z ^ (D + 1) ∈ P := by
      have : c 0 * z ^ (D + 1) = z * G - y * (z * H) := by rw [hH]; ring
      rw [this]
      exact P.sub_mem h1 (P.mul_mem_right _ hy)
    have h3 : z ^ (D + 1) ∈ P := by
      obtain ⟨v, hv⟩ := hc0
      have := P.mul_mem_left (↑v⁻¹ : S) h2
      rwa [← mul_assoc, ← hv, Units.inv_mul, one_mul] at this
    exact hP.mem_of_pow_mem _ h3
  rw [Ideal.radical_eq_sInf]
  constructor
  · exact Submodule.mem_sInf.2 fun P hP => (key P hP.2 (hP.1 (Ideal.mem_span_singleton_self _))).1
  · exact Submodule.mem_sInf.2 fun P hP => (key P hP.2 (hP.1 (Ideal.mem_span_singleton_self _))).2

theorem exists_radical_of_relation (y z : S) : ∀ (D α : ℕ) (c : ℕ → S), (∀ i, IsUnit (c i) ∨ c i = 0) →
    (∃ i ≤ D, IsUnit (c i)) →
    y ^ α * ∑ i ∈ Finset.range (D + 1), c i * y ^ i * z ^ (D - i) = 0 →
    ∃ D' s : ℕ, D' + s = D ∧
      y ∈ (Ideal.span {y ^ (D' + 1) +
        z * ∑ i ∈ Finset.range (D' + 1), c (i + s) * y ^ i * z ^ (D' - i)}).radical ∧
      z ∈ (Ideal.span {y ^ (D' + 1) +
        z * ∑ i ∈ Finset.range (D' + 1), c (i + s) * y ^ i * z ^ (D' - i)}).radical := by
  intro D
  induction D with
  | zero =>
    intro α c _ hex h
    obtain ⟨i, hi, hu⟩ := hex
    obtain rfl : i = 0 := by omega
    exact ⟨0, 0, rfl, mem_radical_of_relation y z α 0 c hu h⟩
  | succ D ih =>
    intro α c hc hex h
    by_cases h0 : IsUnit (c 0)
    · exact ⟨D + 1, 0, rfl, mem_radical_of_relation y z α (D + 1) c h0 h⟩
    · have hc0 : c 0 = 0 := (hc 0).resolve_left h0
      have hex' : ∃ i ≤ D, IsUnit (c (i + 1)) := by
        obtain ⟨i, hi, hu⟩ := hex
        rcases i with _ | i
        · exact absurd hu h0
        · exact ⟨i, by omega, hu⟩
      have h' : y ^ (α + 1) * ∑ i ∈ Finset.range (D + 1), c (i + 1) * y ^ i * z ^ (D - i) = 0 := by
        rw [← h, Finset.sum_range_succ' (fun i => c i * y ^ i * z ^ (D + 1 - i)), hc0, pow_succ, mul_assoc,
          Finset.mul_sum]
        simp only [zero_mul, add_zero]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show D + 1 - (i + 1) = D - i by omega]
        ring
      obtain ⟨D', s, hD, h1, h2⟩ := ih (α + 1) (fun i => c (i + 1)) (fun i => hc _) hex' h'
      exact ⟨D', s + 1, by omega, h1, h2⟩

end Relation

section Cone

variable {A : Type u} [CommRing A] [IsLocalRing A] (I : Ideal A)

def FibreCone : Type u :=
  reesAlgebra I ⧸ Ideal.map (algebraMap A (reesAlgebra I)) (maximalIdeal A)

noncomputable instance : CommRing (FibreCone I) :=
  inferInstanceAs (CommRing (reesAlgebra I ⧸ Ideal.map (algebraMap A (reesAlgebra I)) (maximalIdeal A)))

noncomputable instance : Algebra A (FibreCone I) :=
  inferInstanceAs (Algebra A (reesAlgebra I ⧸ Ideal.map (algebraMap A (reesAlgebra I)) (maximalIdeal A)))

instance [IsNoetherianRing A] : IsNoetherianRing (FibreCone I) :=
  inferInstanceAs (IsNoetherianRing (reesAlgebra I ⧸ Ideal.map (algebraMap A (reesAlgebra I)) (maximalIdeal A)))

noncomputable def toFC : reesAlgebra I →+* FibreCone I :=
  Ideal.Quotient.mk (Ideal.map (algebraMap A (reesAlgebra I)) (maximalIdeal A))

theorem toFC_surjective : Function.Surjective (toFC I) := Ideal.Quotient.mk_surjective

theorem toFC_eq_zero_iff {g : reesAlgebra I} :
    toFC I g = 0 ↔ g ∈ Ideal.map (algebraMap A (reesAlgebra I)) (maximalIdeal A) :=
  Ideal.Quotient.eq_zero_iff_mem

theorem toFC_eq_iff {g h : reesAlgebra I} :
    toFC I g = toFC I h ↔ g - h ∈ Ideal.map (algebraMap A (reesAlgebra I)) (maximalIdeal A) :=
  Ideal.Quotient.eq

theorem algebraMap_fibreCone (r : A) :
    algebraMap A (FibreCone I) r = toFC I (algebraMap A (reesAlgebra I) r) := rfl

noncomputable def cls (n : ℕ) (x : A) : FibreCone I := by
  classical
  exact if h : x ∈ I ^ n then toFC I ⟨monomial n x, reesAlgebra.monomial_mem.2 h⟩ else 0

variable {I}

theorem cls_of_mem {n : ℕ} {x : A} (h : x ∈ I ^ n) :
    cls I n x = toFC I ⟨monomial n x, reesAlgebra.monomial_mem.2 h⟩ := by
  classical
  exact dif_pos h

theorem cls_mul {m n : ℕ} {x y : A} (hx : x ∈ I ^ m) (hy : y ∈ I ^ n) :
    cls I m x * cls I n y = cls I (m + n) (x * y) := by
  rw [cls_of_mem hx, cls_of_mem hy, cls_of_mem (by rw [pow_add]; exact Ideal.mul_mem_mul hx hy), ← map_mul]
  congr 1
  apply Subtype.ext
  simp [monomial_mul_monomial]

theorem cls_add {n : ℕ} {x y : A} (hx : x ∈ I ^ n) (hy : y ∈ I ^ n) :
    cls I n (x + y) = cls I n x + cls I n y := by
  rw [cls_of_mem hx, cls_of_mem hy, cls_of_mem (Ideal.add_mem _ hx hy), ← map_add]
  congr 1
  apply Subtype.ext
  simp

theorem cls_zero (n : ℕ) : cls I n 0 = 0 := by
  rw [cls_of_mem (Ideal.zero_mem _)]
  convert map_zero (toFC I)
  exact (map_zero (monomial (R := A) n)).trans rfl

theorem cls_one : cls I 0 1 = 1 := by
  rw [cls_of_mem (by simp)]
  convert map_one (toFC I)
  exact (monomial_zero_one (R := A)).trans rfl

theorem cls_smul {n : ℕ} {x : A} (r : A) (hx : x ∈ I ^ n) :
    cls I n (r * x) = algebraMap A (FibreCone I) r * cls I n x := by
  rw [cls_of_mem hx, cls_of_mem (Ideal.mul_mem_left _ r hx), algebraMap_fibreCone, ← map_mul]
  congr 1
  apply Subtype.ext
  simp [C_mul_monomial]

omit [IsLocalRing A] in
theorem pow_mem_pow_mul {d : ℕ} {x : A} (hx : x ∈ I ^ d) (k : ℕ) : x ^ k ∈ I ^ (d * k) := by
  rw [pow_mul]
  exact Ideal.pow_mem_pow hx k

theorem cls_pow {d : ℕ} {x : A} (hx : x ∈ I ^ d) (k : ℕ) : cls I d x ^ k = cls I (d * k) (x ^ k) := by
  induction k with
  | zero => simp [cls_one]
  | succ k ih => rw [pow_succ, ih, cls_mul (pow_mem_pow_mul hx k) hx, pow_succ, mul_add, mul_one]

theorem cls_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → A) (hf : ∀ i ∈ s, f i ∈ I ^ n) :
    cls I n (∑ i ∈ s, f i) = ∑ i ∈ s, cls I n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cls_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      cls_add (hf j (Finset.mem_insert_self j s)) (Ideal.sum_mem _ fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem algebraMap_eq_zero {r : A} (hr : r ∈ maximalIdeal A) : algebraMap A (FibreCone I) r = 0 := by
  rw [algebraMap_fibreCone, toFC_eq_zero_iff]
  exact Ideal.mem_map_of_mem _ hr

variable (I) in

def clsPreimage (n : ℕ) (T : Ideal (FibreCone I)) : Ideal A where
  carrier := {x | x ∈ I ^ n ∧ cls I n x ∈ T}
  add_mem' ha hb := ⟨Ideal.add_mem _ ha.1 hb.1, by rw [cls_add ha.1 hb.1]; exact T.add_mem ha.2 hb.2⟩
  zero_mem' := ⟨Ideal.zero_mem _, by rw [cls_zero]; exact T.zero_mem⟩
  smul_mem' r x hx := ⟨Ideal.mul_mem_left _ r hx.1, by
    rw [smul_eq_mul, cls_smul r hx.1]; exact T.mul_mem_left _ hx.2⟩

theorem cls_eq_zero {n : ℕ} {x : A} (hx : x ∈ maximalIdeal A * I ^ n) : cls I n x = 0 := by
  have : maximalIdeal A * I ^ n ≤ clsPreimage I n ⊥ := Ideal.mul_le.2 fun r hr t ht =>
    ⟨Ideal.mul_mem_left _ r ht, by rw [cls_smul r ht, algebraMap_eq_zero hr, zero_mul]; exact Submodule.zero_mem _⟩
  exact (Submodule.mem_bot _).1 (this hx).2

theorem coeff_mem_of_mem_map {g : reesAlgebra I}
    (hg : g ∈ Ideal.map (algebraMap A (reesAlgebra I)) (maximalIdeal A)) (n : ℕ) :
    (g : A[X]).coeff n ∈ maximalIdeal A * I ^ n := by
  let K : Ideal (reesAlgebra I) :=
    { carrier := {g | ∀ n, (g : A[X]).coeff n ∈ maximalIdeal A * I ^ n}
      add_mem' := fun {a b} ha hb n => by
        simpa using Ideal.add_mem _ (ha n) (hb n)
      zero_mem' := fun n => by simp
      smul_mem' := fun r a ha n => by
        rw [smul_eq_mul, Subalgebra.coe_mul, coeff_mul]
        refine Ideal.sum_mem _ fun ij hij => ?_
        obtain rfl : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        have := Ideal.mul_mem_mul ((mem_reesAlgebra_iff I _).1 r.2 ij.1) (ha ij.2)
        exact (show I ^ ij.1 * (maximalIdeal A * I ^ ij.2) ≤ maximalIdeal A * I ^ (ij.1 + ij.2) from
          le_of_eq (by rw [pow_add, mul_left_comm])) this }
  have hle : Ideal.map (algebraMap A (reesAlgebra I)) (maximalIdeal A) ≤ K := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr k
    show ((algebraMap A (reesAlgebra I) r : reesAlgebra I) : A[X]).coeff k ∈ maximalIdeal A * I ^ k
    rw [Subalgebra.coe_algebraMap, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      coeff_C]
    split_ifs with hk
    · subst hk
      simpa using hr
    · exact Submodule.zero_mem _
  exact hle hg n

end Cone

section Dimension

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

theorem exists_relation {N : Ideal A} {e : ℕ} (hN : N.spanFinrank ≤ e) (v : Fin (e + 1) → A)
    (hv : ∀ i, v i ∈ N) :
    ∃ c : Fin (e + 1) → A, (∃ i, c i ∉ maximalIdeal A) ∧ ∑ i, c i * v i ∈ maximalIdeal A * N := by
  classical
  have hfg : N.FG := IsNoetherian.noetherian N
  have hrank := IsLocalRing.spanFinrank_eq_finrank_quotient N hfg
  let w : Fin (e + 1) → N ⧸ (maximalIdeal A • (⊤ : Submodule A N)) :=
    fun i => Submodule.Quotient.mk ⟨v i, hv i⟩
  have : Module.Finite A N := Module.Finite.iff_fg.mpr hfg
  have : Module.Finite (A ⧸ maximalIdeal A) (N ⧸ (maximalIdeal A • (⊤ : Submodule A N))) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have hnot : ¬ LinearIndependent (A ⧸ maximalIdeal A) w := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, ← hrank] at this
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hnot
  choose c hc using fun i => Ideal.Quotient.mk_surjective (I := maximalIdeal A) (g i)
  refine ⟨c, ⟨i, fun h => hi ?_⟩, ?_⟩
  · rw [← hc i]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h
  · have hsum : (maximalIdeal A • (⊤ : Submodule A N)).mkQ (∑ i, c i • (⟨v i, hv i⟩ : N)) = 0 := by
      rw [map_sum, ← hg]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hc i, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
      rfl
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff] at hsum
    simpa [Submodule.coe_sum, Ideal.smul_eq_mul] using hsum

end Dimension

section Reduction

variable {A : Type u} [CommRing A] [IsLocalRing A] {I : Ideal A}

omit [IsLocalRing A] in

theorem form_mem {d : ℕ} {x y : A} (hx : x ∈ I ^ d) (hy : y ∈ I ^ d) (D : ℕ) (r : ℕ → A) :
    ∑ i ∈ Finset.range (D + 1), r i * x ^ i * y ^ (D - i) ∈ I ^ (d * D) := by
  refine Ideal.sum_mem _ fun i hi => ?_
  have hi' : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [mul_assoc, show d * D = d * i + d * (D - i) by rw [← mul_add, Nat.add_sub_cancel' hi'], pow_add]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul (pow_mem_pow_mul hx i) (pow_mem_pow_mul hy (D - i)))

theorem cls_form {d : ℕ} {x y : A} (hx : x ∈ I ^ d) (hy : y ∈ I ^ d) (D : ℕ) (r : ℕ → A) :
    cls I (d * D) (∑ i ∈ Finset.range (D + 1), r i * x ^ i * y ^ (D - i)) =
      ∑ i ∈ Finset.range (D + 1),
        algebraMap A (FibreCone I) (r i) * cls I d x ^ i * cls I d y ^ (D - i) := by
  have hterm : ∀ i ∈ Finset.range (D + 1), x ^ i * y ^ (D - i) ∈ I ^ (d * D) ∧ d * i + d * (D - i) = d * D := by
    intro i hi
    have hi' : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hdeg : d * i + d * (D - i) = d * D := by rw [← mul_add, Nat.add_sub_cancel' hi']
    refine ⟨?_, hdeg⟩
    rw [← hdeg, pow_add]
    exact Ideal.mul_mem_mul (pow_mem_pow_mul hx i) (pow_mem_pow_mul hy (D - i))
  rw [cls_sum _ _ fun i hi => by rw [mul_assoc]; exact Ideal.mul_mem_left _ _ (hterm i hi).1]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mul_assoc, cls_smul _ (hterm i hi).1, mul_assoc, cls_pow hx, cls_pow hy,
    cls_mul (pow_mem_pow_mul hx i) (pow_mem_pow_mul hy _), (hterm i hi).2]

variable [IsNoetherianRing A]

theorem exists_common_radical {e : ℕ} (he : ∀ n : ℕ, (I ^ n).spanFinrank ≤ e) {p q : ℕ} (hp : 1 ≤ p)
    (hq : 1 ≤ q) {a b : A} (ha : a ∈ I ^ p) (hb : b ∈ I ^ q) :
    ∃ m, 1 ≤ m ∧ ∃ c ∈ I ^ m,
      cls I p a ∈ (Ideal.span {cls I m c}).radical ∧ cls I q b ∈ (Ideal.span {cls I m c}).radical := by
  classical
  have ha' : a ^ q ∈ I ^ (p * q) := pow_mem_pow_mul ha q
  have hb' : b ^ p ∈ I ^ (p * q) := by rw [mul_comm]; exact pow_mem_pow_mul hb p
  have hX : cls I (p * q) (a ^ q) = cls I p a ^ q := (cls_pow ha q).symm
  have hY : cls I (p * q) (b ^ p) = cls I q b ^ p := by rw [cls_pow hb p, Nat.mul_comm q p]
  obtain ⟨c, ⟨i0, hi0⟩, hrel⟩ := exists_relation (he (p * q * e))
    (fun i : Fin (e + 1) => (a ^ q) ^ (i : ℕ) * (b ^ p) ^ (e - i)) (fun i => by
      have := form_mem ha' hb' e (fun j => if j = (i : ℕ) then 1 else 0)
      rw [Finset.sum_eq_single (i : ℕ) (fun j _ hj => by simp [hj])
        (fun h => absurd (Finset.mem_range.2 i.2) h)] at this
      simpa using this)
  let r : ℕ → A := fun i => if h : i < e + 1 then c ⟨i, h⟩ else 0
  have hsum : ∑ i : Fin (e + 1), c i * ((a ^ q) ^ (i : ℕ) * (b ^ p) ^ (e - i)) =
      ∑ i ∈ Finset.range (e + 1), r i * (a ^ q) ^ i * (b ^ p) ^ (e - i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => r i * (a ^ q) ^ i * (b ^ p) ^ (e - i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [r, dif_pos i.2, Fin.eta]
    ring
  have hrelF : cls I (p * q) (a ^ q) ^ 0 * ∑ i ∈ Finset.range (e + 1), algebraMap A (FibreCone I) (r i) *
      cls I (p * q) (a ^ q) ^ i * cls I (p * q) (b ^ p) ^ (e - i) = 0 := by
    rw [pow_zero, one_mul, ← cls_form ha' hb' e r, ← hsum]
    exact cls_eq_zero hrel
  have hunit : ∀ i, IsUnit (algebraMap A (FibreCone I) (r i)) ∨ algebraMap A (FibreCone I) (r i) = 0 := by
    intro i
    by_cases h : r i ∈ maximalIdeal A
    · exact Or.inr (algebraMap_eq_zero h)
    · exact Or.inl ((IsLocalRing.notMem_maximalIdeal.1 h).map _)
  have hex : ∃ i ≤ e, IsUnit (algebraMap A (FibreCone I) (r i)) := by
    refine ⟨i0, Nat.lt_succ_iff.mp i0.2, ?_⟩
    have : r i0 = c i0 := by simp only [r, dif_pos i0.2, Fin.eta]
    rw [this]
    exact (IsLocalRing.notMem_maximalIdeal.1 hi0).map _
  obtain ⟨D', s, -, h1, h2⟩ := exists_radical_of_relation (cls I (p * q) (a ^ q))
    (cls I (p * q) (b ^ p)) e 0 _ hunit hex hrelF
  have hform := form_mem ha' hb' D' (fun i => r (i + s))
  have hw2 : b ^ p * ∑ i ∈ Finset.range (D' + 1), r (i + s) * (a ^ q) ^ i * (b ^ p) ^ (D' - i) ∈
      I ^ (p * q * (D' + 1)) := by
    rw [mul_add, mul_one, add_comm, pow_add]
    exact Ideal.mul_mem_mul hb' hform
  have hw : cls I (p * q * (D' + 1)) ((a ^ q) ^ (D' + 1) +
      b ^ p * ∑ i ∈ Finset.range (D' + 1), r (i + s) * (a ^ q) ^ i * (b ^ p) ^ (D' - i)) =
      cls I (p * q) (a ^ q) ^ (D' + 1) + cls I (p * q) (b ^ p) * ∑ i ∈ Finset.range (D' + 1),
        algebraMap A (FibreCone I) (r (i + s)) * cls I (p * q) (a ^ q) ^ i * cls I (p * q) (b ^ p) ^ (D' - i) := by
    rw [cls_add (pow_mem_pow_mul ha' _) hw2, ← cls_pow ha', show p * q * (D' + 1) = p * q + p * q * D' by ring,
      ← cls_mul hb' hform, cls_form ha' hb' D' (fun i => r (i + s))]
  refine ⟨p * q * (D' + 1), ?_, _, Ideal.add_mem _ (pow_mem_pow_mul ha' _) hw2, ?_, ?_⟩
  · have := Nat.mul_le_mul (Nat.mul_le_mul hp hq) (Nat.le_add_left 1 D')
    simpa using this
  · rw [hw]
    obtain ⟨k, hk⟩ := h1
    exact ⟨q * k, by rw [pow_mul, ← hX]; exact hk⟩
  · rw [hw]
    obtain ⟨k, hk⟩ := h2
    exact ⟨p * k, by rw [pow_mul, ← hY]; exact hk⟩

theorem exists_radical_of_finset {e : ℕ} (he : ∀ n : ℕ, (I ^ n).spanFinrank ≤ e) (s : Finset A)
    (hs : ∀ x ∈ s, x ∈ I) :
    ∃ m, 1 ≤ m ∧ ∃ c ∈ I ^ m, ∀ x ∈ s, cls I 1 x ∈ (Ideal.span {cls I m c}).radical := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, le_rfl, 0, Ideal.zero_mem _, by simp⟩
  | insert x s hx ih =>
    obtain ⟨m, hm, c, hc, hall⟩ := ih fun y hy => hs y (Finset.mem_insert_of_mem hy)
    obtain ⟨m', hm', c', hc', h1, h2⟩ := exists_common_radical he hm le_rfl hc
      (show x ∈ I ^ 1 by rw [pow_one]; exact hs x (Finset.mem_insert_self x s))
    refine ⟨m', hm', c', hc', fun y hy => ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact h2
    · exact Ideal.radical_le_radical_iff.2 ((Ideal.span_singleton_le_iff_mem _).2 h1) (hall y hy)

omit [IsNoetherianRing A] in

theorem cls_mem_pow (n : ℕ) {x : A} (hx : x ∈ I ^ n) :
    cls I n x ∈ (Ideal.span {u | ∃ x ∈ I, u = cls I 1 x}) ^ n := by
  induction n generalizing x with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
  | succ n ih =>
    have : I ^ n * I ≤ clsPreimage I (n + 1) ((Ideal.span {u | ∃ x ∈ I, u = cls I 1 x}) ^ (n + 1)) :=
      Ideal.mul_le.2 fun a ha b hb => by
        have hb1 : b ∈ I ^ 1 := by rwa [pow_one]
        refine ⟨by rw [pow_succ]; exact Ideal.mul_mem_mul ha hb, ?_⟩
        rw [← cls_mul ha hb1, pow_succ]
        exact Ideal.mul_mem_mul (ih ha) (Ideal.subset_span ⟨b, hb, rfl⟩)
    rw [pow_succ] at hx
    exact (this hx).2

end Reduction

theorem proof : PrincipalReductionOfBoundedGens.Statement.{u} := by
  intro A _ _ _ I ⟨e, he⟩
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  have hsI : ∀ x ∈ s, x ∈ I := fun x hx => hs ▸ Ideal.subset_span hx
  obtain ⟨m, hm, c, hc, hall⟩ := exists_radical_of_finset he s hsI
  have hJ : Ideal.span {u | ∃ x ∈ I, u = cls I 1 x} ≤ (Ideal.span {cls I m c}).radical := by
    rw [Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have : I ≤ clsPreimage I 1 (Ideal.span {cls I m c}).radical := by
      conv_lhs => rw [← hs]
      rw [Ideal.span_le]
      intro y hy
      exact ⟨by rw [pow_one]; exact hsI y hy, hall y hy⟩
    exact (this hx).2
  obtain ⟨L, hL⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ (IsNoetherian.noetherian _)
  refine ⟨m, hm, c, hc, L, le_antisymm ?_ ?_⟩
  · refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) fun x hx => ?_
    have h1 : cls I (L + m) x ∈ Ideal.span {cls I m c} :=
      hL (Ideal.pow_le_pow_right (by omega) (cls_mem_pow (L + m) hx))
    obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.1 h1
    obtain ⟨f', rfl⟩ := toFC_surjective I f
    rw [cls_of_mem hx, cls_of_mem hc, ← map_mul, toFC_eq_iff] at hf
    have h2 := coeff_mem_of_mem_map hf (L + m)
    simp only [AddSubgroupClass.coe_sub, Subalgebra.coe_mul, coeff_sub, coeff_mul_monomial,
      coeff_monomial, if_true] at h2
    refine Submodule.mem_sup.2 ⟨c * (f' : A[X]).coeff L,
      Ideal.mul_mem_mul (Ideal.mem_span_singleton_self c) ((mem_reesAlgebra_iff I _).1 f'.2 L), _, ?_,
      show c * (f' : A[X]).coeff L + (x - (f' : A[X]).coeff L * c) = x by ring⟩
    rw [Ideal.smul_eq_mul, show x - (f' : A[X]).coeff L * c = -((f' : A[X]).coeff L * c - x) by ring]
    exact neg_mem h2
  · calc Ideal.span {c} * I ^ L ≤ I ^ m * I ^ L :=
          Ideal.mul_mono_left ((Ideal.span_singleton_le_iff_mem _).2 hc)
      _ = I ^ (L + m) := by rw [pow_add, mul_comm]

end PrincipalReductionOfBoundedGens

end GroundTheory.Heights₂.Heights.NumbersDVR
