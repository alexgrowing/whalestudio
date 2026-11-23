import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TensDeg

lemma zpow_mem_of_unit {Ω : Type} [Field Ω] (R : Subring Ω) {u : Ω} (h : u ∈ R) (h' : u⁻¹ ∈ R) (n : ℤ) :
    u ^ n ∈ R := by
  cases n with
  | ofNat n => simpa using pow_mem h n
  | negSucc n =>
    rw [zpow_negSucc, ← inv_pow]
    exact pow_mem h' _

lemma exists_unit_of_span_eq {Ω : Type} [Field Ω] (R : Subring Ω) {s t : Ω} (ht : t ≠ 0)
    (h : Submodule.span R {s} = Submodule.span R {t}) : ∃ u, u ∈ R ∧ u⁻¹ ∈ R ∧ s = u * t := by
  have h1 : s ∈ Submodule.span R {t} := h ▸ Submodule.mem_span_singleton_self s
  have h2 : t ∈ Submodule.span R {s} := h ▸ Submodule.mem_span_singleton_self t
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 h2
  have ha' : (a : Ω) * t = s := ha
  have hb' : (b : Ω) * s = t := hb
  have hba : (b : Ω) * a = 1 := by
    apply mul_right_cancel₀ ht
    rw [_root_.mul_assoc, ha', hb', _root_.one_mul]
  refine ⟨a, a.2, ?_, ha'.symm⟩
  rw [inv_eq_of_mul_eq_one_left hba]
  exact b.2

lemma zpow_finset_sum {Ω I : Type} [Field Ω] {x : Ω} (hx : x ≠ 0) (s : Finset I) (f : I → ℤ) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hx, ih]

end GlobalTheory.CompanionTheory.Ar.TensDeg

open GlobalTheory.CompanionTheory.Ar.TensDeg in

theorem GlobalTheory.CompanionTheory.Ar.Lat.tens_isDegOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)) (d : I → K → ℤ) (e : I → Ω), (∀ i, (Λ i).IsDegOn T y (d i) (e i)) → ∀ a : I → ℤ, (Lat.tens Λ a).IsDegOn T y (∑ i, a i • d i) (∏ i, e i ^ a i) := by
  intro X Ω _ ξ K _ J y I _ Λ T d e h a
  have he : ∀ i, e i ≠ 0 := fun i => (h i).1
  refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (he i), ?_⟩
  intro p hp c hc
  have hc0 : ∏ k, y ⟨k, c k⟩ ≠ 0 := hc.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc0 k (Finset.mem_univ k)
  let g : I → Ω := fun i => (∏ k, y ⟨k, c k⟩ ^ d i k) • e i
  have hg0 : ∀ i, g i ≠ 0 := fun i =>
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)) (he i)
  have hgen : ∀ i, (Λ i).IsGenAt p (g i) := fun i => ⟨hg0 i, (h i).2 p hp c hc⟩
  have hG : (∏ k, y ⟨k, c k⟩ ^ (∑ i, a i • d i) k) • (∏ i, e i ^ a i) = ∏ i, g i ^ a i := by
    simp only [g, smul_eq_mul, mul_zpow, Finset.prod_mul_distrib]
    congr 1
    simp_rw [← Finset.prod_zpow]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.sum_apply, zpow_finset_sum (hy k)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul]
  rw [hG]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨s, hs, rfl⟩
    choose u hu hu' hsu using fun i =>
      exists_unit_of_span_eq (regAt ξ p) (hg0 i) ((hs i).2.symm.trans (hgen i).2)
    have hm : ∏ i, u i ^ a i ∈ regAt ξ p :=
      prod_mem fun i _ => zpow_mem_of_unit _ (hu i) (hu' i) _
    refine Submodule.mem_span_singleton.2 ⟨⟨_, hm⟩, ?_⟩
    show (∏ i, u i ^ a i) * ∏ i, g i ^ a i = ∏ i, s i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hsu i, mul_zpow]
  · exact Submodule.span_le.2 (Set.singleton_subset_iff.2 (Submodule.subset_span ⟨g, hgen, rfl⟩))
