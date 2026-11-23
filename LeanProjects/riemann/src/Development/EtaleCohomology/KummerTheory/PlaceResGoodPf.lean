import Development.EtaleCohomology.KummerTheory.PlaceStepPf

noncomputable section

open IsLocalRing

namespace LateralTheory.KummerTheory

attribute [local instance] Ideal.Quotient.field

section
variable {k K : Type} [Field k] [Field K] [Algebra k K] (A : LocalSubring K)

lemma good_sub_mem (hA : PlaceGood k K A) (a : K) (ha : a ∈ A.toSubring) :
    ∃ c : k, (⟨a - algebraMap k K c, sub_mem ha (hA.1 c)⟩ : A.toSubring) ∈ maximalIdeal A.toSubring := by
  obtain ⟨c, hc⟩ := hA.2 a ha
  refine ⟨c, ?_⟩
  rcases hc with h | h
  · have : (⟨a - algebraMap k K c, sub_mem ha (hA.1 c)⟩ : A.toSubring) = 0 := by
      ext; simp [h]
    rw [this]; exact zero_mem _
  · rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    apply h
    have hK : (a - algebraMap k K c) * (w : K) = 1 := by
      simpa using congrArg (fun z : A.toSubring => (z : K)) hw
    rw [inv_eq_of_mul_eq_one_right hK]; exact w.2

end

theorem PlaceResGood_of : PlaceResGood := by
  intro k K _ _ _ _ A hA y S hAS hS Q _ hQ
  let kS : k →+* S := (algebraMap k K).codRestrict S (fun c => hAS (hA.1 c))

  have stepA : ∀ a (ha : a ∈ A.toSubring), ∃ c : k, (⟨a, hAS ha⟩ : S) - kS c ∈ Q := by
    intro a ha
    obtain ⟨c, hc⟩ := good_sub_mem A hA a ha
    refine ⟨c, ?_⟩
    have := hQ (Ideal.mem_map_of_mem (Subring.inclusion hAS) hc)
    convert this using 1
    rfl

  let φ : k →+* S ⧸ Q := (Ideal.Quotient.mk Q).comp kS
  let _ : Algebra k (S ⧸ Q) := φ.toAlgebra
  have hSm : ∀ s, s ∈ Algebra.adjoin A.toSubring {y} → s ∈ S := fun s hs => by rw [hS]; exact hs
  let y' : S := ⟨y, hSm y (Algebra.subset_adjoin (Set.mem_singleton y))⟩
  have gen : ∀ s (hs : s ∈ Algebra.adjoin A.toSubring {y}),
      Ideal.Quotient.mk Q (⟨s, hSm s hs⟩ : S) ∈ Algebra.adjoin k {Ideal.Quotient.mk Q y'} := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx; subst hx
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    | algebraMap r =>
      obtain ⟨c, hc⟩ := stepA r.1 r.2
      have e : Ideal.Quotient.mk Q (⟨algebraMap A.toSubring K r, hSm _ (Subalgebra.algebraMap_mem _ r)⟩ : S)
          = algebraMap k (S ⧸ Q) c := by
        rw [← sub_eq_zero, ← Ideal.Quotient.mk_eq_mk]
        change Ideal.Quotient.mk Q _ - Ideal.Quotient.mk Q (kS c) = 0
        rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact hc
      rw [e]; exact Subalgebra.algebraMap_mem _ c
    | add x z hx hz ihx ihz =>
      have : (⟨x + z, hSm _ (add_mem hx hz)⟩ : S) = ⟨x, hSm _ hx⟩ + ⟨z, hSm _ hz⟩ := rfl
      rw [this, map_add]; exact add_mem ihx ihz
    | mul x z hx hz ihx ihz =>
      have : (⟨x * z, hSm _ (mul_mem hx hz)⟩ : S) = ⟨x, hSm _ hx⟩ * ⟨z, hSm _ hz⟩ := rfl
      rw [this, map_mul]; exact mul_mem ihx ihz
  have top : Algebra.adjoin k {Ideal.Quotient.mk Q y'} = ⊤ := by
    refine eq_top_iff.mpr fun t _ => ?_
    obtain ⟨⟨s, hs⟩, rfl⟩ := Ideal.Quotient.mk_surjective t
    exact gen s (by rw [hS] at hs; exact hs)
  have : Algebra.FiniteType k (S ⧸ Q) := ⟨⟨{Ideal.Quotient.mk Q y'}, by simpa using top⟩⟩
  have : Module.Finite k (S ⧸ Q) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ Q)
  have surj := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := S ⧸ Q)).2
  have stepS : ∀ s : S, ∃ c : k, s - kS c ∈ Q := by
    intro s
    obtain ⟨c, hc⟩ := surj (Ideal.Quotient.mk Q s)
    refine ⟨c, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    change Ideal.Quotient.mk Q s - φ c = 0
    rw [← hc]; exact sub_self _

  set B := LocalSubring.ofPrime S Q
  refine ⟨fun c => LocalSubring.le_ofPrime S Q (hAS (hA.1 c)), ?_⟩
  intro b hb
  let bb : B.toSubring := ⟨b, hb⟩
  obtain ⟨t, ht⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal Q B.toSubring).surjective
    (Ideal.Quotient.mk (maximalIdeal B.toSubring) bb)
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨c, hc⟩ := stepS s
  refine ⟨c, ?_⟩
  by_cases h0 : b = algebraMap k K c
  · exact Or.inl h0
  right
  intro hinv
  have hmem : bb - algebraMap S B.toSubring (kS c) ∈ maximalIdeal B.toSubring := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← ht,
      IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk, ← map_sub, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_comap.mp (show s - kS c ∈ (maximalIdeal B.toSubring).comap (algebraMap S B.toSubring) by
      rw [← Ideal.under_def, IsLocalization.AtPrime.under_maximalIdeal B.toSubring Q]; exact hc)
  rw [mem_maximalIdeal, mem_nonunits_iff] at hmem
  apply hmem
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
  ext
  change (b - algebraMap k K c) * (b - algebraMap k K c)⁻¹ = 1
  exact mul_inv_cancel₀ (sub_ne_zero.mpr h0)

end LateralTheory.KummerTheory
