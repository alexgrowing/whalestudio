import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.UnitChoice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.QuadFiniteDimensional

noncomputable section

namespace PIW.AdelicOrbitU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

def QuadGen : Prop :=
  ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 →
    (∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) →
    ∃ (θ : E) (d : F), θ ^ 2 = algebraMap F E d ∧ σ θ = -θ ∧ d ≠ 0 ∧
      ∀ e : E, ∃ p q : F, e = algebraMap F E p + algebraMap F E q * θ

theorem glue_mul {S : Type} [CommRing S] {k : ℕ} (e : Fin k → S) (hid : ∀ i, e i * e i = e i)
    (hor : ∀ i j, i ≠ j → e i * e j = 0) (X Y : Fin k → S) :
    (∑ i, e i * X i) * (∑ j, e j * Y j) = ∑ i, e i * (X i * Y i) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · calc e i * X i * (e i * Y i) = (e i * e i) * (X i * Y i) := by ring
      _ = e i * (X i * Y i) := by rw [hid i]
  · intro j _ hji
    calc e i * X i * (e j * Y j) = (e i * e j) * (X i * Y j) := by ring
      _ = 0 := by rw [hor i j (Ne.symm hji), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem norm_id {S : Type} [CommRing S] (B p q a b D Θ : S) (h : Θ ^ 2 = D) :
    (B - (p - q * Θ) * (a + b * Θ)) * (B - (p + q * Θ) * (a - b * Θ)) =
      (B - p * a + q * b * D) ^ 2 - D * (q * a - p * b) ^ 2 := by
  linear_combination (2 * B * q * b - p ^ 2 * b ^ 2 - q ^ 2 * a ^ 2 + q ^ 2 * b ^ 2 * (Θ ^ 2 + D)) * h

theorem norm_one {S : Type} [CommRing S] (p q D Θ : S) (h : Θ ^ 2 = D) :
    (p + q * Θ) * (p - q * Θ) = p ^ 2 - D * q ^ 2 := by
  linear_combination (-q ^ 2) * h

theorem core {R S : Type} [CommRing R] [CommRing S] (ι : R →+* S) (s : S →+* S) (Θ : S) (D Bt P Q a b : R)
    (hΘ : Θ ^ 2 = ι D) (hsΘ : s Θ = -Θ) (hsι : ∀ r, s (ι r) = ι r) (hPQ : P ^ 2 - D * Q ^ 2 = 1)
    (Bi K i4 : R) (hB : Bt * Bi = 1) (hK : Q * D * K = 1) (h4 : (4 : R) * i4 = 1) (hU : UnitChoice R) :
    ∃ lam : S, lam * s lam = 1 ∧ IsUnit (ι Bt - s lam * (ι a + ι b * Θ)) := by
  let p : Fin 4 → R := ![1, -1, P, -P]
  let q : Fin 4 → R := ![0, 0, Q, -Q]
  have hnorm : ∀ i, p i ^ 2 - D * q i ^ 2 = 1 := by
    intro i
    fin_cases i <;> simp [p, q] <;> linear_combination hPQ
  obtain ⟨f, hf⟩ : ∃ f : Fin 4 → R, ∀ i,
      f i = (Bt - p i * a + q i * b * D) ^ 2 - D * (q i * a - p i * b) ^ 2 := ⟨_, fun _ => rfl⟩
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    set I := Ideal.span (Set.range f) with hI
    have hm : ∀ i, f i ∈ I := fun i => Ideal.subset_span ⟨i, rfl⟩
    have e0 : f 0 = (Bt - 1 * a + 0 * b * D) ^ 2 - D * (0 * a - 1 * b) ^ 2 := (hf 0).trans rfl
    have e1 : f 1 = (Bt - (-1) * a + 0 * b * D) ^ 2 - D * (0 * a - (-1) * b) ^ 2 := (hf 1).trans rfl
    have e2 : f 2 = (Bt - P * a + Q * b * D) ^ 2 - D * (Q * a - P * b) ^ 2 := (hf 2).trans rfl
    have e3 : f 3 = (Bt - (-P) * a + (-Q) * b * D) ^ 2 - D * ((-Q) * a - (-P) * b) ^ 2 :=
      (hf 3).trans rfl
    have ha : a ∈ I := by
      have h : a = (i4 * Bi) * (f 1 - f 0) := by
        rw [e0, e1]
        linear_combination (-a) * h4 + (-4 * a * i4) * hB
      rw [h]
      exact I.mul_mem_left _ (sub_mem (hm 1) (hm 0))
    have hx : P * a - Q * b * D ∈ I := by
      have h : P * a - Q * b * D = (i4 * Bi) * (f 3 - f 2) := by
        rw [e2, e3]
        linear_combination (-(P * a - Q * b * D)) * h4 + (-4 * (P * a - Q * b * D) * i4) * hB
      rw [h]
      exact I.mul_mem_left _ (sub_mem (hm 3) (hm 2))
    have hb : b ∈ I := by
      have h : b = K * (P * a - (P * a - Q * b * D)) := by
        linear_combination (-b) * hK
      rw [h]
      exact I.mul_mem_left _ (sub_mem (I.mul_mem_left _ ha) hx)
    have h1 : (1 : R) = Bi ^ 2 * f 0 + (Bi ^ 2 * (2 * Bt - a)) * a + (Bi ^ 2 * D * b) * b := by
      rw [e0]
      linear_combination (-(Bt * Bi + 1)) * hB
    have hmem : Bi ^ 2 * f 0 + (Bi ^ 2 * (2 * Bt - a)) * a + (Bi ^ 2 * D * b) * b ∈ I :=
      add_mem (add_mem (I.mul_mem_left _ (hm 0)) (I.mul_mem_left _ ha)) (I.mul_mem_left _ hb)
    rw [← h1] at hmem
    exact (Ideal.eq_top_iff_one _).mpr hmem
  obtain ⟨e, hid, hor, hsum1, hunit⟩ := hU 4 f hspan
  have hidS : ∀ i, ι (e i) * ι (e i) = ι (e i) := fun i => by rw [← map_mul, hid i]
  have horS : ∀ i j, i ≠ j → ι (e i) * ι (e j) = 0 := fun i j h => by
    rw [← map_mul, hor i j h, map_zero]
  have hE1 : ∑ i, ι (e i) = 1 := by rw [← map_sum, hsum1, map_one]
  have hsl : s (∑ i, ι (e i) * (ι (p i) + ι (q i) * Θ)) =
      ∑ i, ι (e i) * (ι (p i) - ι (q i) * Θ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_add, map_mul, hsι, hsι, hsι, hsΘ]
    ring
  have hn : ∀ i, (ι (p i) + ι (q i) * Θ) * (ι (p i) - ι (q i) * Θ) = 1 := fun i => by
    rw [norm_one _ _ _ _ hΘ, ← map_pow, ← map_pow, ← map_mul, ← map_sub, hnorm i, map_one]
  refine ⟨∑ i, ι (e i) * (ι (p i) + ι (q i) * Θ), ?_, ?_⟩
  · rw [hsl, glue_mul _ hidS horS]
    simp only [hn, mul_one]
    exact hE1
  · rw [hsl]
    set w := ι a + ι b * Θ with hw
    have hz : ι Bt - (∑ i, ι (e i) * (ι (p i) - ι (q i) * Θ)) * w =
        ∑ i, ι (e i) * (ι Bt - (ι (p i) - ι (q i) * Θ) * w) := by
      have h : ∑ i, ι (e i) * (ι Bt - (ι (p i) - ι (q i) * Θ) * w) =
          (∑ i, ι (e i)) * ι Bt - (∑ i, ι (e i) * (ι (p i) - ι (q i) * Θ)) * w := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [h, hE1, one_mul]
    rw [hz]
    have hsz : s (∑ i, ι (e i) * (ι Bt - (ι (p i) - ι (q i) * Θ) * w)) =
        ∑ i, ι (e i) * (ι Bt - (ι (p i) + ι (q i) * Θ) * (ι a - ι b * Θ)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hw, map_mul, map_sub, map_add, hsι, hsΘ]
      ring
    have hprod : (∑ i, ι (e i) * (ι Bt - (ι (p i) - ι (q i) * Θ) * w)) *
        s (∑ i, ι (e i) * (ι Bt - (ι (p i) - ι (q i) * Θ) * w)) = ι (∑ i, e i * f i) := by
      rw [hsz, glue_mul _ hidS horS, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hw, norm_id _ _ _ _ _ _ _ hΘ, hf i, map_mul]
      simp only [map_sub, map_add, map_mul, map_pow]
    have hu := hunit.map ι
    rw [← hprod] at hu
    exact isUnit_of_mul_isUnit_left hu

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
variable (R : Type) [CommRing R] [Algebra F R]

theorem sigR_algebraMap (r : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp [sigR]

theorem sigR_tmul (r : R) (x : E) : sigR R σ (r ⊗ₜ x) = r ⊗ₜ σ x := by
  simp [sigR]

theorem decomp (θ : E) (hspan : ∀ e : E, ∃ p q : F, e = algebraMap F E p + algebraMap F E q * θ)
    (z : R ⊗[F] E) : ∃ a b : R, z = algebraMap R (R ⊗[F] E) a + algebraMap R (R ⊗[F] E) b * (1 ⊗ₜ θ) := by
  have hidR : ∀ x : R, algebraMap R R x = x := fun _ => rfl
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul r x =>
    obtain ⟨p, q, rfl⟩ := hspan x
    refine ⟨p • r, q • r, ?_⟩
    simp only [Algebra.TensorProduct.algebraMap_apply, hidR,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_add]
    rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨a1, b1, rfl⟩ := hx
    obtain ⟨a2, b2, rfl⟩ := hy
    refine ⟨a1 + a2, b1 + b2, ?_⟩
    rw [map_add, map_add]
    ring

end Tensor

theorem stLam_of (hQ : QuadGen) : StLam := by
  intro F E _ _ _ _ σ hfin hfix R _ _ hU t β hβ
  obtain ⟨θ, d, hθ, hσθ, hd, hspan⟩ := hQ F E σ hfin hfix
  obtain ⟨a, b, rfl⟩ := decomp R θ hspan t
  obtain ⟨T, hT0, hTd⟩ : ∃ T : F, T ≠ 0 ∧ T ^ 2 - d ≠ 0 := by
    by_cases h1 : d = 1
    · refine ⟨2, two_ne_zero, ?_⟩
      rw [h1]
      norm_num
    · refine ⟨1, one_ne_zero, ?_⟩
      rw [one_pow]
      exact sub_ne_zero.mpr (Ne.symm h1)
  obtain ⟨P, Q, hPQ, hQ0⟩ : ∃ P Q : F, P ^ 2 - d * Q ^ 2 = 1 ∧ Q ≠ 0 := by
    refine ⟨(T ^ 2 + d) / (T ^ 2 - d), 2 * T / (T ^ 2 - d), ?_, ?_⟩
    · field_simp
      ring
    · exact div_ne_zero (mul_ne_zero two_ne_zero hT0) hTd
  have hidR : ∀ x : R, algebraMap R R x = x := fun _ => rfl
  have hβS : algebraMap F (R ⊗[F] E) β = algebraMap R (R ⊗[F] E) (algebraMap F R β) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      hidR]
  rw [hβS]
  refine core (algebraMap R (R ⊗[F] E)) (sigR R σ) (1 ⊗ₜ θ) (algebraMap F R d)
    (algebraMap F R β) (algebraMap F R P) (algebraMap F R Q) a b ?_ ?_ ?_ ?_
    (algebraMap F R β⁻¹) (algebraMap F R (Q * d)⁻¹) (algebraMap F R (1 / 4)) ?_ ?_ ?_ hU
  · rw [Algebra.TensorProduct.tmul_pow, one_pow, hθ, Algebra.TensorProduct.algebraMap_apply,
      hidR, Algebra.algebraMap_eq_smul_one d, Algebra.algebraMap_eq_smul_one d,
      TensorProduct.smul_tmul]
  · rw [sigR_tmul, hσθ, TensorProduct.tmul_neg]
  · exact fun r => sigR_algebraMap σ R r
  · rw [← map_pow, ← map_pow, ← map_mul, ← map_sub, hPQ, map_one]
  · rw [← map_mul, mul_inv_cancel₀ hβ, map_one]
  · rw [← map_mul, ← map_mul, mul_inv_cancel₀ (mul_ne_zero hQ0 hd), map_one]
  · have h4 : (4 : R) = algebraMap F R 4 := (map_ofNat (algebraMap F R) 4).symm
    rw [h4, ← map_mul]
    norm_num

end PIW.AdelicOrbitU

namespace PIW.AdelicOrbitU

theorem quadGen : QuadGen := by
  intro F E _ _ _ _ σ hfin hfix
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hfin
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨e, he⟩ : ∃ e : E, e ∉ (algebraMap F E).range := by
    by_contra h
    push_neg at h
    have hle : Module.finrank F E ≤ 1 := by
      refine finrank_le_one (1 : E) fun w => ?_
      obtain ⟨c, hc⟩ := h w
      exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩
    omega
  have hli : LinearIndependent F ![(1 : E), e] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply he
      refine RingHom.mem_range.mpr ⟨-s * t⁻¹, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      have hT : algebraMap F E t ≠ 0 := (map_ne_zero _).mpr ht
      have h' := mul_inv_cancel₀ hT
      rw [map_mul, map_neg, map_inv₀]
      linear_combination (-(algebraMap F E t)⁻¹) * hst + e * h'
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [hfin, Fintype.card_fin]
  obtain ⟨Bs, hBs⟩ : ∃ Bs : Module.Basis (Fin 2) F E, ⇑Bs = ![(1 : E), e] :=
    ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard,
      coe_basisOfLinearIndependentOfCardEqFinrank hli hcard⟩
  have hspan : ∀ x : E, ∃ c0 c1 : F, x = algebraMap F E c0 + algebraMap F E c1 * e := by
    intro x
    refine ⟨Bs.repr x 0, Bs.repr x 1, ?_⟩
    nth_rewrite 1 [← Bs.sum_repr x]
    rw [Fin.sum_univ_two, hBs]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Algebra.smul_def, mul_one]
  obtain ⟨v, u, hsq⟩ := hspan (e ^ 2)
  have hse : σ e ≠ e := fun h => he ((hfix e).mp h)
  have hσsq : σ e ^ 2 = algebraMap F E v + algebraMap F E u * σ e := by
    rw [← map_pow, hsq, map_add, map_mul, AlgHom.commutes, AlgHom.commutes]
  have hsum : σ e = algebraMap F E u - e := by
    have h0 : (σ e - e) * (σ e + e - algebraMap F E u) = 0 := by
      linear_combination hσsq - hsq
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd (sub_eq_zero.mp h) hse
    · linear_combination h
  have hθsq : (2 * e - algebraMap F E u) ^ 2 = algebraMap F E (4 * v + u ^ 2) := by
    simp only [map_add, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hsq
  refine ⟨2 * e - algebraMap F E u, 4 * v + u ^ 2, hθsq, ?_, ?_, ?_⟩
  · rw [map_sub, map_mul, map_ofNat, AlgHom.commutes, hsum]
    ring
  · intro hd0
    rw [hd0, map_zero] at hθsq
    have h2 : 2 * e - algebraMap F E u = 0 := (pow_eq_zero_iff two_ne_zero).mp hθsq
    apply hse
    rw [hsum]
    linear_combination -1 * h2
  · intro x
    obtain ⟨c0, c1, hx⟩ := hspan x
    refine ⟨c0 + c1 * u / 2, c1 / 2, ?_⟩
    rw [hx]
    simp only [map_add, map_mul, map_div₀, map_ofNat]
    ring

theorem stLam : StLam := stLam_of quadGen

end PIW.AdelicOrbitU
