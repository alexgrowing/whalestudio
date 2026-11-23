import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf

noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.Pf.AllRowsConv

open Formalism.MainNotions.S Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.unitaryCongruence

variable (I : AutInst)

def coset (m : ℕ) (q : KSub I ⧸ KgN I m) : Set I.Gf := {y | ((q.out : KSub I) : I.Gf)⁻¹ * y ∈ I.Kg m}

theorem coset_sub (m : ℕ) (q : KSub I ⧸ KgN I m) : coset I m q ⊆ I.Kset := by
  intro y hy
  have h1 : ((q.out : KSub I) : I.Gf) * (((q.out : KSub I) : I.Gf)⁻¹ * y) ∈ I.Kset :=
    K_mul I (q.out : KSub I).2 hy.1
  simpa using h1

theorem mem_coset_iff (m : ℕ) {y : I.Gf} (hy : y ∈ I.Kset) (q : KSub I ⧸ KgN I m) :
    y ∈ coset I m q ↔ q = (QuotientGroup.mk (⟨y, hy⟩ : KSub I) : KSub I ⧸ KgN I m) := by
  constructor
  · intro h
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 h
  · intro h
    subst h
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk (⟨y, hy⟩ : KSub I) : KSub I ⧸ KgN I m))
    exact this

theorem isOpen_coset (m : ℕ) (hm : 1 ≤ m) (q : KSub I ⧸ KgN I m) : IsOpen (coset I m q) :=
  (I.topf_open m hm).preimage (continuous_const.mul continuous_id)

theorem measure_coset (μf : Measure I.Gf) [μf.IsMulLeftInvariant] (m : ℕ) (q : KSub I ⧸ KgN I m) :
    μf (coset I m q) = μf (I.Kg m) :=
  measure_preimage_mul μf _ (I.Kg m)

theorem term_eq {m : ℕ} {f₁ f₂ : I.Gf → ℂ} (h1N : ∀ y, ∀ n ∈ I.Kg m, f₁ (y * n) = f₁ y)
    (h2N : ∀ z, ∀ n ∈ I.Kg m, f₂ (n * z) = f₂ z) (x : I.Gf) (q : KSub I ⧸ KgN I m) {y : I.Gf}
    (hyq : y ∈ coset I m q) :
    f₁ y * f₂ (y⁻¹ * x) = f₁ ((q.out : KSub I) : I.Gf) * f₂ (((q.out : KSub I) : I.Gf)⁻¹ * x) := by
  have hn : ((q.out : KSub I) : I.Gf)⁻¹ * y ∈ I.Kg m := hyq
  generalize ((q.out : KSub I) : I.Gf) = c at hn ⊢
  have e1 : f₁ y = f₁ c := by
    have := h1N c (c⁻¹ * y) hn
    rwa [mul_inv_cancel_left] at this
  have e2 : f₂ (y⁻¹ * x) = f₂ (c⁻¹ * x) := by
    have := h2N (y⁻¹ * x) (c⁻¹ * y) hn
    rw [← this]
    congr 1
    group
  rw [e1, e2]

theorem convF_fin (μf : Measure I.Gf) [μf.IsMulLeftInvariant] {m : ℕ} (hm : 1 ≤ m) (hfin : μf (I.Kg m) < ⊤)
    [Fintype (KSub I ⧸ KgN I m)] {f₁ f₂ : I.Gf → ℂ} (h1K : ∀ y, f₁ y ≠ 0 → y ∈ I.Kset)
    (h1N : ∀ y, ∀ n ∈ I.Kg m, f₁ (y * n) = f₁ y) (h2N : ∀ z, ∀ n ∈ I.Kg m, f₂ (n * z) = f₂ z) (x : I.Gf) :
    I.convF μf f₁ f₂ x = (μf (I.Kg m)).toReal *
      ∑ q : KSub I ⧸ KgN I m, f₁ ((q.out : KSub I) : I.Gf) * f₂ (((q.out : KSub I) : I.Gf)⁻¹ * x) := by
  classical
  have key : (fun y => f₁ y * f₂ (y⁻¹ * x)) = fun y => ∑ q : KSub I ⧸ KgN I m,
      Set.indicator (coset I m q)
        (fun _ => f₁ ((q.out : KSub I) : I.Gf) * f₂ (((q.out : KSub I) : I.Gf)⁻¹ * x)) y := by
    funext y
    by_cases hy : y ∈ I.Kset
    · rw [Finset.sum_eq_single (QuotientGroup.mk (⟨y, hy⟩ : KSub I) : KSub I ⧸ KgN I m)]
      · have hmem := (mem_coset_iff I m hy (QuotientGroup.mk (⟨y, hy⟩ : KSub I) : KSub I ⧸ KgN I m)).2 rfl
        rw [Set.indicator_of_mem hmem]
        exact term_eq I h1N h2N x _ hmem
      · intro q _ hq
        rw [Set.indicator_of_notMem]
        intro hmem
        exact hq ((mem_coset_iff I m hy q).1 hmem)
      · intro h; exact absurd (Finset.mem_univ _) h
    · have h0 : f₁ y = 0 := by by_contra h; exact hy (h1K y h)
      rw [h0, zero_mul]
      symm
      refine Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (fun hmem => hy (coset_sub I m q hmem)) _
  unfold AutInst.convF
  rw [key, integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (isOpen_coset I m hm q).measurableSet, measureReal_def, measure_coset,
      Complex.real_smul]
  · intro q _
    refine (integrable_indicator_iff (isOpen_coset I m hm q).measurableSet).2 ?_
    refine integrableOn_const ?_
    rw [measure_coset]
    exact hfin.ne

end Formalism.L2.SG.Pf.AllRowsConv
