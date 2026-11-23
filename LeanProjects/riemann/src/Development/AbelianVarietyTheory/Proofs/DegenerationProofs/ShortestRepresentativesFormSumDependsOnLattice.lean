import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.OneBasis.ShortSum

variable {X : Type} [AddCommGroup X]

abbrev mulSub (X : Type) [AddCommGroup X] (k : ℕ) : AddSubgroup X := (nsmulAddMonoidHom (α := X) k).range

theorem mk_eq_iff (k : ℕ) (a b : X) :
    (QuotientAddGroup.mk a : X ⧸ mulSub X k) = QuotientAddGroup.mk b ↔ ∃ z, b = a + k • z := by
  rw [QuotientAddGroup.eq]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have : k • z = -a + b := hz
    rw [this]; abel
  · rintro ⟨z, rfl⟩
    exact ⟨z, by simp⟩

theorem surj {k r mu : ℕ} {Q : X → ℤ} {cls : Fin r → X} (h : Adapted k Q cls mu) :
    Function.Surjective (fun i => (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k)) := by
  intro c
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨i, z, hz⟩ := h.2.2.1 a
  exact ⟨i, (mk_eq_iff k _ _).2 ⟨z, hz⟩⟩

theorem sum_comp {k r mu : ℕ} {Q : X → ℤ} {cls : Fin r → X} (h : Adapted k Q cls mu)
    [Fintype (X ⧸ mulSub X k)] (g : X ⧸ mulSub X k → ℤ) :
    ∑ i, g (QuotientAddGroup.mk (cls i)) = mu * ∑ c, g c := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun i => (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨i₀, rfl⟩ := surj h c
  rw [Finset.sum_congr rfl (g := fun _ => g (QuotientAddGroup.mk (cls i₀)))
    (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← h.2.2.2 i₀, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  refine Finset.filter_congr fun i _ => ⟨fun hi => ?_, fun hi => by simp only [hi]⟩
  exact h.2.1 i i₀ ((mk_eq_iff k _ _).1 hi.symm)

theorem val_eq {k r r' mu mu' : ℕ} {Q : X → ℤ} {cls : Fin r → X} {cls' : Fin r' → X} (h : Adapted k Q cls mu)
    (h' : Adapted k Q cls' mu') {i : Fin r} {i' : Fin r'}
    (e : (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k) = QuotientAddGroup.mk (cls' i')) :
    Q (cls i) = Q (cls' i') := by
  apply le_antisymm
  · obtain ⟨z, hz⟩ := (mk_eq_iff k _ _).1 e
    rw [hz]; exact h.1 i z
  · obtain ⟨z, hz⟩ := (mk_eq_iff k _ _).1 e.symm
    rw [hz]; exact h'.1 i' z

theorem sum_eq {k r mu mu' : ℕ} {Q : X → ℤ} {cls cls' : Fin r → X} (h : Adapted k Q cls mu)
    (h' : Adapted k Q cls' mu') : ∑ i, Q (cls i) = ∑ i, Q (cls' i) := by
  haveI : Finite (X ⧸ mulSub X k) := Finite.of_surjective _ (surj h)
  letI : Fintype (X ⧸ mulSub X k) := Fintype.ofFinite _
  have a := sum_comp h (fun _ => 1)
  have a' := sum_comp h' (fun _ => 1)
  have hm : (mu : ℤ) = mu' := by
    have hp : (∑ _c : X ⧸ mulSub X k, (1 : ℤ)) ≠ 0 := by simp
    exact mul_right_cancel₀ hp (a.symm.trans a')
  have b := sum_comp h (fun c => Q (cls (Function.surjInv (surj h) c)))
  have b' := sum_comp h' (fun c => Q (cls (Function.surjInv (surj h) c)))
  calc ∑ i, Q (cls i) = _ := Finset.sum_congr rfl fun i _ =>
        val_eq h h (Function.surjInv_eq (surj h) _).symm
    _ = _ := b
    _ = _ := by rw [hm]
    _ = _ := b'.symm
    _ = _ := Finset.sum_congr rfl fun i _ => val_eq h h' (Function.surjInv_eq (surj h) _)

theorem transport {X₀ : Type} [AddCommGroup X₀] {q₀ : X₀ → ℤ} {Q : X → ℤ} (e : X₀ ≃+ X) {w : ℕ} (hw : 0 < w)
    (hQ : ∀ y, Q (e y) = w * q₀ y) {k r mu : ℕ} {cls : Fin r → X} (h : Adapted k Q cls mu) :
    Adapted k q₀ (fun i => e.symm (cls i)) mu := by
  refine ⟨fun i z => ?_, fun i i' ⟨z, hz⟩ => ?_, fun α => ?_, fun i₀ => ?_⟩
  · have h1 := h.1 i (e z)
    have h2 := hQ (e.symm (cls i))
    have h3 := hQ (e.symm (cls i) + k • z)
    rw [map_add, map_nsmul] at h3
    rw [e.apply_symm_apply] at h2 h3
    rw [h2, h3] at h1
    exact le_of_mul_le_mul_left h1 (by exact_mod_cast hw)
  · have h1 := congrArg e hz
    simp only [map_add, map_nsmul, e.apply_symm_apply] at h1
    simp only [h.2.1 i i' ⟨_, h1⟩]
  · obtain ⟨i, z, hz⟩ := h.2.2.1 (e α)
    refine ⟨i, e.symm z, e.injective ?_⟩
    simp only [map_add, map_nsmul, e.apply_symm_apply]
    exact hz
  · rw [← h.2.2.2 i₀]
    simp only [e.symm.injective.eq_iff]

end GlobalTheory.OneBasis.ShortSum

namespace GlobalTheory.OneBasis

theorem sum_adapted_eq : ∀ (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (q₀ : X₀ → ℤ) (k r : ℕ), 1 ≤ k → (∀ y, 0 ≤ q₀ y) → ∃ d C : ℕ, 1 ≤ d ∧ ∀ (X : Type) [AddCommGroup X] (Q : X → ℤ) (e : X₀ ≃+ X) (w : ℕ), 0 < w → (∀ y, Q (e y) = w * q₀ y) → ∀ (cls : Fin r → X) (mu : ℕ), Adapted k Q cls mu → (d : ℤ) * ∑ i, Q (cls i) = C * w * k := by
  intro X₀ _ _ _ q₀ k r hk hq
  by_cases hex : ∃ (c₀ : Fin r → X₀) (m₀ : ℕ), Adapted k q₀ c₀ m₀
  · obtain ⟨c₀, m₀, h₀⟩ := hex
    refine ⟨k, (∑ i, q₀ (c₀ i)).toNat, hk, fun X _ Q e w hw hQ cls mu h => ?_⟩
    rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hq _),
      ShortSum.sum_eq h₀ (ShortSum.transport e hw hQ h)]
    have : ∑ i, Q (cls i) = w * ∑ i, q₀ (e.symm (cls i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← hQ, e.apply_symm_apply]
    rw [this]; ring
  · exact ⟨k, 0, hk, fun X _ Q e w hw hQ cls mu h => (hex ⟨_, _, ShortSum.transport e hw hQ h⟩).elim⟩

end GlobalTheory.OneBasis
