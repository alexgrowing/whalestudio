import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SmoothColumnLifts.SmoothCol
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.SmoothColumnLifts.KerOpen

noncomputable section

open Matrix
open scoped Topology

namespace PositivityTheory.RgUd.Form.U.Lift2.AvA

section Grp

variable {G : Type*} [AddCommGroup G]

theorem sum_transl {M : Type*} [AddCommMonoid M] (A H : AddSubgroup G) (_hHA : H ≤ A) (T : Finset G)
    (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (f : G → M) (hf : ∀ x, ∀ h ∈ H, f (x + h) = f x) (a : G) (ha : a ∈ A) :
    ∑ t ∈ T, f (t + a) = ∑ t ∈ T, f t := by
  classical
  have hex : ∀ x ∈ A, ∃ t, t ∈ T ∧ x - t ∈ H := fun x hx => (hu x hx).exists
  let r : G → G := fun x => if hx : x ∈ A then (hex x hx).choose else x
  have hr : ∀ x ∈ A, r x ∈ T ∧ x - r x ∈ H := by
    intro x hx
    simp only [r, dif_pos hx]
    exact (hex x hx).choose_spec
  have huniq : ∀ x ∈ A, ∀ t ∈ T, x - t ∈ H → r x = t := fun x hx t ht hxt =>
    (hu x hx).unique (hr x hx) ⟨ht, hxt⟩
  have hfr : ∀ x ∈ A, f x = f (r x) := by
    intro x hx
    have := hf (r x) (x - r x) (hr x hx).2
    rw [add_sub_cancel] at this
    exact this
  refine Finset.sum_nbij' (fun t => r (t + a)) (fun t => r (t - a)) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    exact (hr _ (A.add_mem (hT t ht) ha)).1
  · intro t ht
    exact (hr _ (A.sub_mem (hT t ht) ha)).1
  · intro t ht
    have h1 := hr (t + a) (A.add_mem (hT t ht) ha)
    apply huniq _ (A.sub_mem (hT _ h1.1) ha) t ht
    have : r (t + a) - a - t = -((t + a) - r (t + a)) := by abel
    rw [this]
    exact H.neg_mem h1.2
  · intro t ht
    have h1 := hr (t - a) (A.sub_mem (hT t ht) ha)
    apply huniq _ (A.add_mem (hT _ h1.1) ha) t ht
    have : r (t - a) + a - t = -((t - a) - r (t - a)) := by abel
    rw [this]
    exact H.neg_mem h1.2
  · intro t ht
    exact hfr _ (A.add_mem (hT t ht) ha)

theorem card_ne_zero (A H : AddSubgroup G) (T : Finset G) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) :
    (T.card : ℂ) ≠ 0 := by
  obtain ⟨t, ⟨ht, -⟩, -⟩ := hu 0 A.zero_mem
  exact Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨t, ht⟩)

theorem sum_char_eq_zero (A H : AddSubgroup G) (hHA : H ≤ A) (T : Finset G)
    (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (χ : G → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y) (hH : ∀ h ∈ H, χ h = 1)
    (a : G) (ha : a ∈ A) (hne : χ a ≠ 1) : ∑ t ∈ T, χ t = 0 := by
  have h := sum_transl A H hHA T hT hu χ (fun x h hh => by rw [hχ, hH h hh, mul_one]) a ha
  simp_rw [hχ] at h
  rw [← Finset.sum_mul] at h
  have : (∑ t ∈ T, χ t) * (χ a - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact h1
  · exact absurd (sub_eq_zero.1 h1) hne

theorem avg_indep {M : Type*} [AddCommGroup M] [Module ℂ M] (A H K : AddSubgroup G) (hHA : H ≤ A)
    (hKA : K ≤ A) (S R : Finset G)
    (hS : ∀ t ∈ S, t ∈ A) (huS : ∀ a ∈ A, ∃! t, t ∈ S ∧ a - t ∈ H)
    (hR : ∀ t ∈ R, t ∈ A) (huR : ∀ a ∈ A, ∃! t, t ∈ R ∧ a - t ∈ K)
    (f : G → M) (hfH : ∀ x, ∀ h ∈ H, f (x + h) = f x) (hfK : ∀ x, ∀ h ∈ K, f (x + h) = f x) :
    ((S.card : ℂ)⁻¹) • ∑ t ∈ S, f t = ((R.card : ℂ)⁻¹) • ∑ t ∈ R, f t := by
  have e1 : ∑ r ∈ R, ∑ t ∈ S, f (t + r) = (R.card : ℂ) • ∑ t ∈ S, f t := by
    rw [Finset.sum_congr rfl (fun r hr => sum_transl A H hHA S hS huS f hfH r (hR r hr))]
    rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have e2 : ∑ t ∈ S, ∑ r ∈ R, f (r + t) = (S.card : ℂ) • ∑ t ∈ R, f t := by
    rw [Finset.sum_congr rfl (fun t ht => sum_transl A K hKA R hR huR f hfK t (hS t ht))]
    rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have key : (R.card : ℂ) • ∑ t ∈ S, f t = (S.card : ℂ) • ∑ t ∈ R, f t := by
    rw [← e1, ← e2, Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [add_comm]
  have hSp := card_ne_zero A H S huS
  have hRp := card_ne_zero A K R huR
  have hX : (∑ t ∈ S, f t) = (R.card : ℂ)⁻¹ • ((S.card : ℂ) • ∑ t ∈ R, f t) := by
    rw [← key, smul_smul, inv_mul_cancel₀ hRp, one_smul]
  rw [hX, smul_smul, smul_smul, mul_comm ((S.card : ℂ)⁻¹) ((R.card : ℂ)⁻¹), mul_assoc,
    inv_mul_cancel₀ hSp, mul_one]

theorem sum_circ_eq_zero (A H : AddSubgroup G) (hHA : H ≤ A) (T : Finset G)
    (hT : ∀ t ∈ T, t ∈ A) (hu : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (χ : G → Circle) (hχ : ∀ x y, χ (x + y) = χ x * χ y) (hH : ∀ h ∈ H, χ h = 1)
    (a : G) (ha : a ∈ A) (hne : χ a ≠ 1) : ∑ t ∈ T, ((χ t : Circle) : ℂ) = 0 :=
  sum_char_eq_zero A H hHA T hT hu (fun x => (χ x : ℂ)) (fun x y => by rw [hχ, Circle.coe_mul])
    (fun h hh => by rw [hH h hh, Circle.coe_one]) a ha (fun h => hne (Circle.coe_eq_one.1 h))

theorem exists_tr [TopologicalSpace G] [IsTopologicalAddGroup G] (A H : AddSubgroup G)
    (hAc : IsCompact (A : Set G)) (hH : IsOpen (H : Set G)) (hHA : H ≤ A) :
    ∃ T : Finset G, (∀ t ∈ T, t ∈ A) ∧ ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H := by
  classical
  obtain ⟨F, hF⟩ := hAc.elim_finite_subcover (fun a : A => (fun x => x - (a : G)) ⁻¹' (H : Set G))
    (fun a => hH.preimage (continuous_sub_right _))
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, by simp [H.zero_mem]⟩)
  let r : G → G := fun x => Quotient.out (QuotientAddGroup.mk x : G ⧸ H)
  have hr : ∀ x, r x - x ∈ H := fun x => by
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add H x
    simp only [r]
    rw [hh, add_sub_cancel_left]
    exact h.2
  have hrr : ∀ x y, x - y ∈ H → r x = r y := fun x y hxy => by
    simp only [r]
    congr 1
    refine QuotientAddGroup.eq.2 ?_
    have : -x + y = -(x - y) := by abel
    rw [this]
    exact H.neg_mem hxy
  have hrA : ∀ x ∈ A, r x ∈ A := fun x hx => by
    have : r x = x + (r x - x) := by abel
    rw [this]
    exact A.add_mem hx (hHA (hr x))
  refine ⟨F.image (fun a : A => r a), ?_, ?_⟩
  · intro t ht
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 ht
    exact hrA a a.2
  · intro a ha
    obtain ⟨i, hi, hai⟩ := Set.mem_iUnion₂.1 (hF ha)
    refine ⟨r i, ⟨Finset.mem_image.2 ⟨i, hi, rfl⟩, ?_⟩, ?_⟩
    · have : a - r i = (a - i) - (r i - i) := by abel
      rw [this]
      exact H.sub_mem hai (hr i)
    · rintro t ⟨ht, hat⟩
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
      have h1 : r (r j) = r j := hrr _ _ (hr j)
      have h2 : r (r i) = r i := hrr _ _ (hr i)
      have h3 : r j - r i ∈ H := by
        have : r j - r i = (a - r i) - (a - r j) := by abel
        rw [this]
        have : a - r i = (a - i) - (r i - i) := by abel
        rw [this]
        exact H.sub_mem (H.sub_mem hai (hr i)) hat
      rw [← h1, ← h2]
      exact hrr _ _ h3

end Grp

theorem isOpen_ker {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (φ : AddChar k Circle) (hφ : Continuous φ) : IsOpen {x : k | φ x = 1} :=
  PositivityTheory.RgUd.Form.U.Lift2.KerOpen.isOpen_ker φ hφ

end PositivityTheory.RgUd.Form.U.Lift2.AvA
