import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.IsSplitFrame

noncomputable section

open scoped TensorProduct
open NumberField Formalism.MainNotions.S Polynomial

namespace PI.UnitaryDimensionFormula

section JacE

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def jaR : Af F →+* E ⊗[F] Af F :=
  (Algebra.TensorProduct.includeRight : Af F →ₐ[F] E ⊗[F] Af F).toRingHom

theorem jaR_apply (a : Af F) : jaR F E a = (1 : E) ⊗ₜ[F] a := by
  rfl

theorem ja_genR (a : Af F) (ha : a ∈ Formalism.UG.intAd F) : jaR F E a ∈ IntAf F E := by
  apply Subring.subset_closure
  exact Set.mem_union_right _ (Set.mem_range.2 ⟨⟨a, ha⟩, rfl⟩)

theorem ja_genL (z : 𝓞 E) : ((z : E) ⊗ₜ[F] (1 : Af F)) ∈ IntAf F E := by
  apply Subring.subset_closure
  exact Set.mem_union_left _ (Set.mem_range.2 ⟨⟨(z : E), RingHom.mem_range.2 ⟨z, rfl⟩⟩, rfl⟩)

def jaT : Subring (IntAf F E) :=
  Subring.comap (IntAf F E).subtype ((Formalism.UG.intAd F).map (jaR F E))

def jaL : 𝓞 E →+* IntAf F E :=
  RingHom.codRestrict (((Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] Af F).toRingHom).comp
    (algebraMap (𝓞 E) E)) (IntAf F E) (fun z => by
      simpa [Algebra.TensorProduct.includeLeft_apply] using ja_genL F E z)

theorem ja_integral (m : IntAf F E) : IsIntegral (jaT F E) m := by

  let S : Subring (E ⊗[F] Af F) :=
    (integralClosure (jaT F E) (IntAf F E)).toSubring.map (IntAf F E).subtype
  have hle : IntAf F E ≤ S := by
    apply Subring.closure_le.2
    rintro x (⟨⟨y, hy⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨o, rfl⟩ := RingHom.mem_range.1 hy
      refine Subring.mem_map.2 ⟨jaL F E o, ?_, rfl⟩
      have h0 : IsIntegral ℤ o := by
        first
          | exact Algebra.IsIntegral.isIntegral o
          | exact NumberField.RingOfIntegers.isIntegral o
      have h1 : IsIntegral ℤ (jaL F E o) := h0.map (jaL F E).toIntAlgHom
      show jaL F E o ∈ integralClosure (jaT F E) (IntAf F E)
      exact h1.tower_top
    · have hw : (⟨(1 : E) ⊗ₜ[F] y, ja_genR F E y hy⟩ : IntAf F E) ∈ jaT F E :=
        Subring.mem_comap.2 (Subring.mem_map.2 ⟨y, hy, rfl⟩)
      refine Subring.mem_map.2 ⟨⟨(1 : E) ⊗ₜ[F] y, ja_genR F E y hy⟩, ?_, rfl⟩
      show _ ∈ integralClosure (jaT F E) (IntAf F E)
      exact isIntegral_algebraMap (x := (⟨_, hw⟩ : jaT F E))
  obtain ⟨x, hx, hxm⟩ := Subring.mem_map.1 (hle m.2)
  have hxm' : x = m := Subtype.ext hxm
  subst hxm'
  exact hx

set_option maxHeartbeats 400000 in

theorem ja_key (G : ℕ) (m : IntAf F E) :
    ∃ t : IntAf F E, ∃ c ∈ jaT F E, (1 + (G : IntAf F E) * m) * t = 1 + (G : IntAf F E) * c := by
  obtain ⟨p, hpm, hp⟩ := ja_integral F E m
  rw [Polynomial.eval₂_eq_sum_range] at hp
  obtain ⟨n, hn⟩ : ∃ n, p.natDegree = n := ⟨_, rfl⟩
  rw [hn] at hp
  have hpn : p.coeff n = 1 := hn ▸ hpm.coeff_natDegree
  obtain ⟨y, hy⟩ : ∃ y : IntAf F E, 1 + (G : IntAf F E) * m = y := ⟨_, rfl⟩
  rw [hy]

  have hw : ∀ i : ℕ, ∃ w : IntAf F E, (y - 1) ^ i = (-1) ^ i + y * w := by
    intro i
    obtain ⟨w, hw⟩ := sub_dvd_pow_sub_pow (y - 1) (-1) i
    refine ⟨w, ?_⟩
    have h1 : y - 1 - -1 = y := by ring
    rw [h1] at hw
    linear_combination hw
  choose w hw using hw
  have hym : y - 1 = (G : IntAf F E) * m := by rw [← hy]; ring

  have hE0 : ∑ i ∈ Finset.range (n + 1),
      algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * (y - 1) ^ i = 0 := by
    have h2 : ∑ i ∈ Finset.range (n + 1),
        algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * (y - 1) ^ i =
        (G : IntAf F E) ^ n * ∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * m ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [hym, mul_pow]
      calc algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * ((G : IntAf F E) ^ i * m ^ i)
          = algebraMap (jaT F E) (IntAf F E) (p.coeff i) * ((G : IntAf F E) ^ (n - i) * (G : IntAf F E) ^ i) * m ^ i := by ring
        _ = (G : IntAf F E) ^ n * (algebraMap (jaT F E) (IntAf F E) (p.coeff i) * m ^ i) := by
          rw [← pow_add, Nat.sub_add_cancel hin]; ring
    rw [h2, hp, mul_zero]
  have hE : ∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * (-1) ^ i +
      y * ∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * w i = 0 := by
    have h3 : ∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * (-1) ^ i +
        y * ∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * w i =
        ∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * (y - 1) ^ i := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hw i]; ring
    rw [h3, hE0]

  obtain ⟨c0, hc0⟩ : ∃ c0 : jaT F E,
      c0 = ∑ i ∈ Finset.range n, p.coeff i * (G : jaT F E) ^ (n - 1 - i) * (-1) ^ i := ⟨_, rfl⟩
  have hS : ∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * (-1) ^ i =
      (G : IntAf F E) * algebraMap (jaT F E) (IntAf F E) c0 + (-1) ^ n := by
    simp only [Finset.sum_range_succ, hpn, map_one, Nat.sub_self, pow_zero, one_mul]
    congr 1
    rw [hc0, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i < n := Finset.mem_range.1 hi
    have h4 : n - i = (n - 1 - i) + 1 := by omega
    simp only [map_mul, map_pow, map_natCast, map_neg, map_one]
    rw [h4, pow_succ]
    ring
  have hsq : ((-1 : IntAf F E) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  refine ⟨(-1) ^ n * -(∑ i ∈ Finset.range (n + 1), algebraMap (jaT F E) (IntAf F E) (p.coeff i) * (G : IntAf F E) ^ (n - i) * w i),
    algebraMap (jaT F E) (IntAf F E) ((-1) ^ n * c0), ((-1) ^ n * c0).2, ?_⟩
  rw [map_mul, map_pow, map_neg, map_one]
  linear_combination (-(-1 : IntAf F E) ^ n) * hE + (-1 : IntAf F E) ^ n * hS + hsq

end JacE

theorem idxDJacE : IdxDJacE := by
  intro F E _ _ _ _ _ g e he m hm
  obtain ⟨t, c, hc, htc⟩ := ja_key F E g ⟨m, hm⟩
  obtain ⟨c', hc', hcc⟩ := Subring.mem_map.1 (Subring.mem_comap.1 hc)
  obtain ⟨y', hy', hey⟩ := he.2.2.2 c' hc'
  refine ⟨(t : E ⊗[F] Af F) * jaR F E y', mul_mem t.2 (ja_genR F E y' hy'), ?_⟩
  have h1 : (1 + (g : E ⊗[F] Af F) * m) * (t : E ⊗[F] Af F) =
      1 + (g : E ⊗[F] Af F) * jaR F E c' := by
    have h2 := congrArg Subtype.val htc
    push_cast at h2
    rw [h2]
    exact congrArg (fun z => 1 + (g : E ⊗[F] Af F) * z) hcc.symm
  calc ((1 : E) ⊗ₜ[F] e) * (1 + (g : E ⊗[F] Af F) * m) * ((t : E ⊗[F] Af F) * jaR F E y')
      = jaR F E e * ((1 + (g : E ⊗[F] Af F) * m) * (t : E ⊗[F] Af F)) * jaR F E y' := by
        simp only [jaR_apply]; ring
    _ = jaR F E (e * (1 + (g : Af F) * c') * y') := by
        rw [h1]; simp only [map_mul, map_add, map_one, map_natCast]
    _ = (1 : E) ⊗ₜ[F] e := by rw [hey, jaR_apply]

end PI.UnitaryDimensionFormula
