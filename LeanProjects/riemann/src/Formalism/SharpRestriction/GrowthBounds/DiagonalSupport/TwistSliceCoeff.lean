import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MemSupportSumMonomial

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G

section Sl

variable {ι : Type*} {n : ℕ} (T : Set ι)

def offT (mo : ι × Fin n →₀ ℕ) : ι × Fin n →₀ ℕ := mo.filter fun v => v.1 ∉ T

def onT (mo : ι × Fin n →₀ ℕ) : ι × Fin n →₀ ℕ := mo.filter fun v => v.1 ∈ T

theorem onT_add_offT (mo : ι × Fin n →₀ ℕ) : onT T mo + offT T mo = mo :=
  Finsupp.filter_add_filter_not mo _

theorem offT_support (mo : ι × Fin n →₀ ℕ) : ∀ v ∈ (offT T mo).support, v.1 ∉ T := by
  intro v hv
  rw [offT, Finsupp.support_filter, Finset.mem_filter] at hv
  exact hv.2

theorem onT_support (mo : ι × Fin n →₀ ℕ) : ∀ v ∈ (onT T mo).support, v.1 ∈ T := by
  intro v hv
  rw [onT, Finsupp.support_filter, Finset.mem_filter] at hv
  exact hv.2

theorem offT_add (a b : ι × Fin n →₀ ℕ) : offT T (a + b) = offT T a + offT T b := Finsupp.filter_add

theorem offT_eq_self (M : ι × Fin n →₀ ℕ) (h : ∀ v ∈ M.support, v.1 ∉ T) : offT T M = M :=
  (Finsupp.filter_eq_self_iff _ _).2 fun v hv => h v (Finsupp.mem_support_iff.2 hv)

theorem offT_eq_zero (m : ι × Fin n →₀ ℕ) (h : ∀ i, i ∉ T → multideg m i = 0) : offT T m = 0 := by
  ext v
  rw [offT, Finsupp.filter_apply]
  by_cases hv : v.1 ∉ T
  · rw [if_pos hv]
    have h1 := h v.1 hv
    unfold multideg at h1
    have h2 : m (v.1, v.2) ≤ ∑ c : Fin n, m (v.1, c) :=
      Finset.single_le_sum (f := fun c : Fin n => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)
    rw [h1] at h2
    exact Nat.le_zero.1 h2
  · rw [if_neg hv]
    rfl

theorem multideg_onT (mo : ι × Fin n →₀ ℕ) (i : ι) (hi : i ∉ T) : multideg (onT T mo) i = 0 := by
  unfold multideg
  apply Finset.sum_eq_zero
  intro c _
  rw [onT, Finsupp.filter_apply, if_neg hi]

end Sl

def sliceT {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (T : Set ι) (F : MvPolynomial (ι × Fin n) R)
    (M : ι × Fin n →₀ ℕ) : MvPolynomial (ι × Fin n) R :=
  ∑ mo ∈ F.support.filter (fun mo => offT T mo = M), monomial (onT T mo) (F.coeff mo)

section Sl2

variable {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (T : Set ι) (F : MvPolynomial (ι × Fin n) R)

theorem slice_sum : F = ∑ M ∈ F.support.image (offT T), sliceT T F M * monomial M 1 := by
  have h1 : ∀ M ∈ F.support.image (offT T), sliceT T F M * monomial M 1 =
      ∑ mo ∈ F.support.filter (fun mo => offT T mo = M), monomial mo (F.coeff mo) := by
    intro M _
    rw [sliceT, Finset.sum_mul]
    refine Finset.sum_congr rfl fun mo hmo => ?_
    rw [monomial_mul, mul_one, ← (Finset.mem_filter.1 hmo).2, onT_add_offT]
  rw [Finset.sum_congr rfl h1,
    Finset.sum_fiberwise_of_maps_to (fun mo hmo => Finset.mem_image_of_mem (offT T) hmo)]
  exact F.as_sum

theorem slice_support (M mo' : ι × Fin n →₀ ℕ) (h : mo' ∈ (sliceT T F M).support) :
    ∃ mo ∈ F.support, offT T mo = M ∧ onT T mo = mo' := by
  obtain ⟨mo, hmo, rfl⟩ := mem_support_sum_monomial _ _ _ _ h
  exact ⟨mo, (Finset.mem_filter.1 hmo).1, (Finset.mem_filter.1 hmo).2, rfl⟩

theorem slice_supported (M : ι × Fin n →₀ ℕ) : sliceT T F M ∈ supported R {v : ι × Fin n | v.1 ∈ T} := by
  refine Subalgebra.sum_mem _ fun mo hmo => ?_
  rw [mem_supported, vars_monomial (mem_support_iff.1 (Finset.mem_filter.1 hmo).1)]
  intro v hv
  exact onT_support T mo v hv

variable (LL : Letters ι) (S : Set ι) (j : Fin n)

theorem twist_slice_off (M m : ι × Fin n →₀ ℕ) (hm : m ∈ (twistSub LL S j (sliceT T F M)).support) :
    offT T m = 0 := by
  obtain ⟨u, hu, hmu⟩ := twistSub_support LL S j _ m hm
  obtain ⟨mo, _, _, rfl⟩ := slice_support T F M u hu
  exact offT_eq_zero T m fun i hi => (hmu i).trans (multideg_onT T mo i hi)

theorem twist_slice_coeff (hST : S ⊆ T) (M : ι × Fin n →₀ ℕ) (hM : M ∈ F.support.image (offT T))
    (m : ι × Fin n →₀ ℕ) (hm : m ∈ (twistSub LL S j (sliceT T F M)).support) :
    (twistSub LL S j F).coeff (m + M) = (twistSub LL S j (sliceT T F M)).coeff m := by
  have hoff : ∀ M' ∈ F.support.image (offT T), ∀ v ∈ M'.support, v.1 ∉ T := by
    intro M' hM'
    obtain ⟨mo, _, rfl⟩ := Finset.mem_image.1 hM'
    exact offT_support T mo
  have hsum : twistSub LL S j F =
      ∑ M' ∈ F.support.image (offT T), twistSub LL S j (sliceT T F M') * monomial M' 1 := by
    conv_lhs => rw [slice_sum T F]
    rw [map_sum]
    refine Finset.sum_congr rfl fun M' hM' => ?_
    rw [map_mul, twistSub_monomial_off LL S j M' fun v hv hvS => hoff M' hM' v hv (hST hvS)]
  rw [hsum, coeff_sum, Finset.sum_eq_single M]
  · rw [coeff_mul_monomial', if_pos le_add_self, add_tsub_cancel_right, mul_one]
  · intro M' hM' hne
    rw [coeff_mul_monomial']
    split_ifs with hle
    · by_contra hc
      have hc' : (twistSub LL S j (sliceT T F M')).coeff (m + M - M') ≠ 0 := left_ne_zero_of_mul hc
      have h1 := twist_slice_off T F LL S j M' _ (mem_support_iff.2 hc')
      have h2 := twist_slice_off T F LL S j M m hm
      have h3 : m + M - M' + M' = m + M := tsub_add_cancel_of_le hle
      have h4 := congrArg (offT T) h3
      rw [offT_add, offT_add, h1, h2, zero_add, zero_add, offT_eq_self T M' (hoff M' hM'),
        offT_eq_self T M (hoff M hM)] at h4
      exact hne h4
    · rfl
  · intro h
    exact absurd hM h

end Sl2

theorem valSlice : ValSlice := by
  intro R _ _ ι n _ LL T F
  refine ⟨F.support.image (offT T), sliceT T F, ?_, fun M _ => slice_supported T F M, slice_sum T F, ?_, ?_⟩
  · intro M hM
    obtain ⟨mo, _, rfl⟩ := Finset.mem_image.1 hM
    exact offT_support T mo
  · intro M _ mo' hmo'
    obtain ⟨mo, hmo, rfl, rfl⟩ := slice_support T F M mo' hmo'
    rw [onT_add_offT]
    exact hmo
  · intro M hM S hST
    refine val_lam_of_subset _ _ _ _ _ _ fun j => sDegs_subset_of _ _ _ _ _ _ _ fun k hk => ?_
    intro m
    by_cases hm : m ∈ (twistSub LL S j (sliceT T F M)).support
    · rw [← twist_slice_coeff T F LL S j hST M hM m hm]
      exact hk _
    · rw [notMem_support_iff.1 hm]
      simp

end Formalism.MainNotions.Proposition5Numerics
