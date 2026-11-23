import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicNormWeight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClassSumCompare

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
open scoped TensorProduct nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem tmul_eq (a : AdF E) (e : E) :
    (show AdE E from a ⊗ₜ[maximalRealSubfield E] e) = inclF E a * diagE E e := by
  show a ⊗ₜ[maximalRealSubfield E] e = (a ⊗ₜ[maximalRealSubfield E] (1 : E)) * ((1 : AdF E) ⊗ₜ[maximalRealSubfield E] e)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem incl_mem {a : AdF E} (ha : ∀ v : Plc E, a v ∈ v.adicCompletionIntegers (maximalRealSubfield E)) :
    inclF E a ∈ intAd E := Subring.subset_closure (Or.inl ⟨a, ha, rfl⟩)

theorem diag_int_mem (o : 𝓞 E) : diagE E (o : E) ∈ intAd E := Subring.subset_closure (Or.inr ⟨o, rfl⟩)

theorem mem_hat_of_mem {x : AdE E} (hx : x ∈ intAd E) :
    (show GlobalTheory.AdLat.RA (maximalRealSubfield E) E from x) ∈
      GlobalTheory.AdLat.hat1 (maximalRealSubfield E) ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  have h1 : (1 : E) ∈ ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := FractionalIdeal.one_mem_one _
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, ha, rfl⟩ | ⟨o, rfl⟩
    · exact GlobalTheory.AdLat.tmul_mem_adelicCompletion_of_integral _ ha h1
    · exact GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet _ ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
  | zero => exact zero_mem _
  | one => exact GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet _ h1
  | add x y _ _ hx hy => exact add_mem hx hy
  | neg x _ hx => exact neg_mem hx
  | mul x y _ _ hx hy =>
    refine GlobalTheory.AdLat.mul_mem_adelicCompletionOfElementSet_of_mul_mem _ (fun a ha b hb => ?_) hx hy
    have := FractionalIdeal.mul_mem_mul ha hb
    rwa [mul_one] at this

theorem diag_mem_iff (x : E) : diagE E x ∈ intAd E ↔ ∃ o : 𝓞 E, (o : E) = x := by
  refine ⟨fun h => ?_, ?_⟩
  · exact (FractionalIdeal.mem_one_iff _).1
      ((GlobalTheory.AdLat.one_tmul_mem_adelicCompletion_fractionalIdeal_iff (maximalRealSubfield E) 1 x).1 (mem_hat_of_mem h))
  · rintro ⟨o, rfl⟩; exact diag_int_mem o

theorem star_diag (x : E) : star (diagE E x) = diagE E (IsCMField.complexConj E x) := rfl

theorem star_incl (a : AdF E) : star (inclF E a) = inclF E a := by
  show adConj E (a ⊗ₜ 1) = a ⊗ₜ 1
  simp [adConj]

theorem conj_int (a : 𝓞 E) : ∃ b : 𝓞 E, (b : E) = IsCMField.complexConj E (a : E) :=
  ⟨RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv a, rfl⟩

theorem star_mem {x : AdE E} (hx : x ∈ intAd E) : star x ∈ intAd E := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, ha, rfl⟩ | ⟨o, rfl⟩
    · rw [star_incl]; exact incl_mem ha
    · show star (diagE E o) ∈ _
      rw [star_diag, diag_mem_iff]; exact conj_int o
  | zero => rw [star_zero]; exact zero_mem _
  | one => rw [star_one]; exact one_mem _
  | add x y _ _ hx hy => rw [star_add]; exact add_mem hx hy
  | neg x _ hx => rw [star_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [star_mul]; exact mul_mem hy hx

theorem exists_nat_mul_int (e : E) : ∃ k : ℕ, 0 < k ∧ ∃ o : 𝓞 E, (o : E) = k * e := by
  obtain ⟨k, hk, h⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
  refine ⟨k.natAbs, Int.natAbs_pos.2 hk, ?_⟩
  have h1 := h e (by simp)
  rcases Int.natAbs_eq k with h2 | h2
  · refine ⟨⟨k • e, h1⟩, ?_⟩
    show k • e = _
    conv_lhs => rw [h2]
    simp
  · refine ⟨⟨-(k • e), h1.neg⟩, ?_⟩
    show -(k • e) = _
    conv_lhs => rw [h2]
    simp

theorem diag_algebraMap (x : maximalRealSubfield E) :
    diagE E (algebraMap _ E x) = inclF E (algebraMap _ (AdF E) x) := by
  show (1 : AdF E) ⊗ₜ[maximalRealSubfield E] (algebraMap _ E x) = (algebraMap _ (AdF E) x) ⊗ₜ[maximalRealSubfield E] (1 : E)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem exists_tmul_int (a : AdF E) (e : E) : ∃ (t : maximalRealSubfield E) (o : 𝓞 E),
    inclF E a * diagE E e = inclF E (algebraMap _ (AdF E) t * a) * diagE E (o : E) := by
  obtain ⟨k, hk, o, ho⟩ := exists_nat_mul_int e
  refine ⟨(k : maximalRealSubfield E)⁻¹, o, ?_⟩
  have hk' : (k : E) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  rw [map_mul, ← diag_algebraMap, ho, mul_comm (diagE E _) (inclF E a), mul_assoc, ← map_mul]
  congr 2
  rw [map_inv₀, map_natCast]
  field_simp

theorem approx (m : ℕ) (hm : 0 < m) (x : AdE E) : ∃ e : E, ∃ u ∈ intAd E, x = diagE E e + (m : AdE E) * u := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by show (0 : AdE E) = _; simp⟩
  | tmul a e =>
    obtain ⟨t, o, h⟩ := exists_tmul_int a e
    obtain ⟨x, a', ha', h'⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul _ m hm (algebraMap _ (AdF E) t * a)
    refine ⟨algebraMap _ E x * o, inclF E a' * diagE E o, mul_mem (incl_mem ha') (diag_int_mem o), ?_⟩
    refine (tmul_eq a e).trans ?_
    rw [h, h', map_add, map_mul, diag_algebraMap, map_nsmul, nsmul_eq_mul]
    ring
  | add x y hx hy =>
    obtain ⟨e, u, hu, hx⟩ := hx
    obtain ⟨e', u', hu', hy⟩ := hy
    refine ⟨e + e', u + u', add_mem hu hu', ?_⟩
    show (show AdE E from x) + (show AdE E from y) = _
    rw [show (show AdE E from x) = _ from hx, show (show AdE E from y) = _ from hy, map_add]
    ring

end GlobalTheory.ClassSumCompare
