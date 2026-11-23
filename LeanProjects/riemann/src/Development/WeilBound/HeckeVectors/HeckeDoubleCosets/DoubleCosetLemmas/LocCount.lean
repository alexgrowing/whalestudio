import Mathlib

open MeasureTheory Set

namespace CompanionTheory.D.Upq.DoubleCosetLemmas

variable {G M : Type} [Group G] [MeasurableSpace M]

def stab (J : Subgroup G) (g : G) : Set G := {k | k ∈ J ∧ g⁻¹ * k * g ∈ J}

def cos (J : Subgroup G) (g : G) (A : Set G) : Set (G ⧸ J) := {z | ∃ k ∈ A, z = ((k * g : G) : G ⧸ J)}

structure Meas (dx : Measure M) (φ : G → M) (J : Subgroup G) (g : G) : Prop where
  inj : Function.Injective φ
  meas : ∀ k ∈ J, MeasurableSet (φ '' ((k * ·) '' stab J g))
  vol : ∀ k ∈ J, dx (φ '' ((k * ·) '' stab J g)) = dx (φ '' stab J g)
  ne : dx (φ '' stab J g) ≠ 0
  fin : dx (φ '' (J : Set G)) ≠ ⊤

variable {dx : Measure M} {φ : G → M} {J : Subgroup G} {g : G}

theorem fibre_eq {k : G} (hk : k ∈ J) :
    {x | x ∈ J ∧ ((x * g : G) : G ⧸ J) = (k * g : G)} = (k * ·) '' stab J g := by
  ext x
  simp only [mem_setOf_eq, mem_image, stab, QuotientGroup.eq]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨k⁻¹ * x, ⟨J.mul_mem (J.inv_mem hk) hx, ?_⟩, by group⟩
    have := J.inv_mem h
    rwa [show ((x * g)⁻¹ * (k * g))⁻¹ = g⁻¹ * (k⁻¹ * x) * g by group] at this
  · rintro ⟨s, ⟨hs, hs'⟩, rfl⟩
    refine ⟨J.mul_mem hk hs, ?_⟩
    have := J.inv_mem hs'
    rwa [show (g⁻¹ * s * g)⁻¹ = (k * s * g)⁻¹ * (k * g) by group] at this

theorem Meas.finset (h : Meas dx φ J g) (t : Finset (G ⧸ J)) (ht : ↑t ⊆ cos J g J) :
    dx (φ '' {x | x ∈ J ∧ ((x * g : G) : G ⧸ J) ∈ t}) = t.card * dx (φ '' stab J g) := by
  have e : φ '' {x | x ∈ J ∧ ((x * g : G) : G ⧸ J) ∈ t} =
      ⋃ z ∈ t, φ '' {x | x ∈ J ∧ ((x * g : G) : G ⧸ J) = z} := by
    ext y; simp only [mem_image, mem_setOf_eq, mem_iUnion]
    exact ⟨fun ⟨x, ⟨h1, h2⟩, h3⟩ => ⟨_, h2, x, ⟨h1, rfl⟩, h3⟩,
      fun ⟨z, hz, x, ⟨h1, h2⟩, h3⟩ => ⟨x, ⟨h1, h2 ▸ hz⟩, h3⟩⟩
  rw [e, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl fun z hz => ?_, Finset.sum_const, nsmul_eq_mul]
    obtain ⟨k, hk, rfl⟩ := ht hz
    rw [fibre_eq hk, h.vol k hk]
  · intro a _ b _ hab
    refine (Set.disjoint_image_iff h.inj).2 (Set.disjoint_left.2 fun x h1 h2 => hab ?_)
    exact h1.2.symm.trans h2.2
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := ht hz
    rw [fibre_eq hk]; exact h.meas k hk

theorem Meas.finite (h : Meas dx φ J g) : (cos J g J).Finite := by
  by_contra hinf
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt h.ne h.fin
  obtain ⟨t, ht, rfl⟩ := Set.Infinite.exists_subset_card_eq hinf n
  rw [← h.finset t ht] at hn
  exact hn.not_ge (measure_mono (image_mono fun x hx => hx.1))

theorem Meas.card (h : Meas dx φ J g) {A : Set G} (hA : A ⊆ J)
    (hs : ∀ k ∈ A, ∀ s ∈ stab J g, k * s ∈ A) :
    ((cos J g A).ncard : ENNReal) * dx (φ '' stab J g) = dx (φ '' A) := by
  have hsub : cos J g A ⊆ cos J g J := fun z ⟨k, hk, e⟩ => ⟨k, hA hk, e⟩
  have hf := h.finite.subset hsub
  rw [Set.ncard_eq_toFinset_card _ hf, ← h.finset _ (by simpa using hsub)]
  congr 2
  ext x
  simp only [mem_setOf_eq, Finite.mem_toFinset]
  refine ⟨fun ⟨hx, k, hk, e⟩ => ?_, fun hx => ⟨hA hx, x, hx, rfl⟩⟩
  have : x ∈ (k * ·) '' stab J g := fibre_eq (hA hk) ▸ ⟨hx, e⟩
  obtain ⟨s, hs', rfl⟩ := this
  exact hs k hk s hs'

section Sum

variable {Y : Type} [AddCommGroup Y] [Module ℂ Y] {F : G → Y}

theorem out_eq (hR : ∀ z, ∀ k ∈ J, F (z * k) = F z) (x : G) : F ((x : G ⧸ J).out) = F x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul J x
  rw [hk, hR _ _ k.2]

theorem supp_sub (h0 : ∀ z, z ∉ DoubleCoset.doubleCoset g (J : Set G) J → F z = 0) :
    (Function.support fun z : G ⧸ J => F z.out) ⊆ cos J g J := by
  intro z hz
  by_contra hn
  refine hz (h0 _ fun hm => hn ?_)
  obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.1 hm
  exact ⟨a, ha, by rw [← z.out_eq', e]; exact QuotientGroup.mk_mul_of_mem _ hb⟩

open Classical in
theorem finsum_eq (hf : (cos J g J).Finite) (hR : ∀ z, ∀ k ∈ J, F (z * k) = F z)
    (h0 : ∀ z, z ∉ DoubleCoset.doubleCoset g (J : Set G) J → F z = 0) {A : Set G} (hA : A ⊆ J)
    {y : Y} (hF : ∀ k ∈ J, F (k * g) = if k ∈ A then y else 0)
    (hs : ∀ k ∈ A, ∀ s ∈ stab J g, k * s ∈ A) :
    ∑ᶠ z : G ⧸ J, F z.out = ((cos J g A).ncard : ℂ) • y := by
  have hsub : cos J g A ⊆ cos J g J := fun z ⟨k, hk, e⟩ => ⟨k, hA hk, e⟩
  have hf' := hf.subset hsub
  rw [finsum_eq_sum_of_support_subset (s := hf'.toFinset), Set.ncard_eq_toFinset_card _ hf',
    Finset.sum_congr rfl fun z hz => ?_, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  · obtain ⟨k, hk, rfl⟩ := hf'.mem_toFinset.1 hz
    rw [out_eq hR, hF k (hA hk), if_pos hk]
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := supp_sub h0 hz
    have := hz
    rw [Function.mem_support, out_eq hR, hF k hk] at this
    have hkA : k ∈ A := by by_contra hn; exact this (if_neg hn)
    simpa using ⟨k, hkA, rfl⟩

open Classical in

theorem Meas.sum (h : Meas dx φ J g) {F : G → ℂ} (hR : ∀ z, ∀ k ∈ J, F (z * k) = F z)
    (h0 : ∀ z, z ∉ DoubleCoset.doubleCoset g (J : Set G) J → F z = 0) {A : Set G} (hA : A ⊆ J)
    {y : ℂ} (hF : ∀ k ∈ J, F (k * g) = if k ∈ A then y else 0) :
    (∑ᶠ z : G ⧸ J, F z.out) * ((dx (φ '' stab J g)).toReal : ℂ) = y * ((dx (φ '' A)).toReal : ℂ) := by
  by_cases hy : y = 0
  · rw [finsum_eq h.finite hR h0 (A := J) subset_rfl (y := 0) (fun k hk => by simp [hF k hk, hy])
      fun k hk s hs => J.mul_mem hk hs.1, hy]
    simp
  have hs : ∀ k ∈ A, ∀ s ∈ stab J g, k * s ∈ A := fun k hk s hs => by
    have h1 := hF _ (J.mul_mem (hA hk) hs.1)
    rw [show k * s * g = k * g * (g⁻¹ * s * g) by group, hR _ _ hs.2, hF k (hA hk), if_pos hk] at h1
    by_contra hn
    exact hy (h1.trans (if_neg hn))
  rw [finsum_eq h.finite hR h0 hA hF hs, ← h.card hA hs, ENNReal.toReal_mul]
  simp only [smul_eq_mul, ENNReal.toReal_natCast]
  push_cast; ring

end Sum

end CompanionTheory.D.Upq.DoubleCosetLemmas
