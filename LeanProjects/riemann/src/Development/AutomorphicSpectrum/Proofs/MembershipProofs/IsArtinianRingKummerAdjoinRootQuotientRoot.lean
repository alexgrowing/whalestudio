import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.LaEqSqrtSmulLam
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.HasElemDiv
open GlobalTheory.CompanionTheory.SplitRow GlobalTheory.CompanionTheory.FinHeis GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitRow.IdxV

theorem relIndex_pi' {ι G : Type} [Fintype ι] [AddCommGroup G] (H K : ι → AddSubgroup G) :
    (AddSubgroup.pi Set.univ H).relIndex (AddSubgroup.pi Set.univ K) = ∏ i, (H i).relIndex (K i) := by
  let f : (∀ i, K i) →+ (ι → G) :=
    { toFun := fun x i => (x i : G), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have h1 : AddSubgroup.pi Set.univ K = (⊤ : AddSubgroup (∀ i, K i)).map f := by
    ext x
    simp only [AddSubgroup.mem_pi, Set.mem_univ, forall_true_left, AddSubgroup.mem_map,
      AddSubgroup.mem_top, true_and]
    exact ⟨fun h => ⟨fun i => ⟨x i, h i⟩, rfl⟩, by rintro ⟨y, rfl⟩ i; exact (y i).2⟩
  rw [h1, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right]
  simp only [AddSubgroup.relIndex]
  simp only [AddSubgroup.index]
  rw [← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight fun x y => ?_).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientAddGroup.leftRel_apply]
  refine forall_congr' fun i => ?_
  exact ⟨fun h => QuotientAddGroup.leftRel_apply.2 (h trivial), fun h _ =>
    (QuotientAddGroup.leftRel_apply (s := (H i).addSubgroupOf (K i))).1 h⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ball (c : k) : AddSubgroup k := (𝒪[k]).toAddSubgroup.comap (AddMonoidHom.mulRight c)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem mem_ball (c x : k) : x ∈ ball c ↔ x * c ∈ 𝒪[k] := Iff.rfl

theorem relIndex_ball (ϖ : kˣ) (hϖ : ∃ p : 𝒪[k], Irreducible p ∧ (p : k) = ϖ) (b : ℤ) :
    (ball (1 : k)).relIndex (ball ((ϖ ^ b : kˣ) : k)) = resCard k ^ b.toNat := by
  obtain ⟨p, hp, hpϖ⟩ := hϖ
  have hne : (ϖ : k) ≠ 0 := ϖ.ne_zero
  obtain ⟨m, rfl | rfl⟩ := b.eq_nat_or_neg
  · let f : 𝒪[k] →+ k := (AddMonoidHom.mulRight (((ϖ : k) ^ m)⁻¹)).comp (𝒪[k]).subtype.toAddMonoidHom
    have hf : ∀ x, f x = (x : k) * ((ϖ : k) ^ m)⁻¹ := fun _ => rfl
    have h1 : ball ((ϖ ^ (m : ℤ) : kˣ) : k) = (⊤ : AddSubgroup 𝒪[k]).map f := by
      ext x
      simp only [mem_ball, AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, hf, zpow_natCast,
        Units.val_pow_eq_pow_val]
      constructor
      · intro h
        exact ⟨⟨_, h⟩, by field_simp⟩
      · rintro ⟨y, rfl⟩
        rw [inv_mul_cancel_right₀ (pow_ne_zero _ hne)]
        exact y.2
    have h2 : (ball (1 : k)).comap f = ((IsLocalRing.maximalIdeal 𝒪[k]) ^ m).toAddSubgroup := by
      ext x
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer p).1 hp, Ideal.span_singleton_pow,
        AddSubgroup.mem_comap, mem_ball, hf, mul_one, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton']
      constructor
      · intro h
        refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
        push_cast
        rw [hpϖ]; field_simp
      · rintro ⟨y, rfl⟩
        push_cast
        rw [hpϖ, mul_inv_cancel_right₀ (pow_ne_zero _ hne)]
        exact y.2
    rw [h1, ← AddSubgroup.relIndex_comap, AddSubgroup.relIndex_top_right, h2, Int.toNat_natCast]
    exact cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field 𝒪[k])
  · rw [Int.toNat_neg_natCast, pow_zero, AddSubgroup.relIndex_eq_one]
    intro x hx
    rw [mem_ball] at hx ⊢
    have : x * 1 = x * ((ϖ ^ (-(m : ℤ)) : kˣ) : k) * ((p ^ m : 𝒪[k]) : k) := by
      push_cast
      rw [hpϖ]
      simp only [_root_.zpow_neg, zpow_natCast]
      field_simp
    rw [this]
    exact mul_mem hx (p ^ m).2

variable {r n : Type} [Fintype r] [DecidableEq r] [Fintype n] [DecidableEq n]

end GlobalTheory.CompanionTheory.SplitRow.IdxV
