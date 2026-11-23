import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.HeisenbergUnitaryHolds

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

open Formalism.L2.Th1.H

section Reps
variable {G : Type*} [AddCommGroup G]

theorem repsG_exist (M N : AddSubgroup G) (h : M.relIndex N ≠ 0) :
    ∃ S : Finset G, IsRepsG M N S ∧ S.card = M.relIndex N := by
  classical
  have : (M.addSubgroupOf N).FiniteIndex := ⟨h⟩
  have : Finite (N ⧸ M.addSubgroupOf N) := AddSubgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (N ⧸ M.addSubgroupOf N)
  let f : (N ⧸ M.addSubgroupOf N) → G := fun q => ((Quotient.out q : N) : G)
  have hf : Function.Injective f := by
    intro q q' hq
    have : (Quotient.out q : N) = Quotient.out q' := Subtype.ext hq
    simpa using congrArg (fun x : N => (x : N ⧸ M.addSubgroupOf N)) this
  refine ⟨Finset.univ.image f, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    exact (Quotient.out q : N).2
  · intro x hx y hy hxy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hy
    have : q = q' := by
      rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
      rw [QuotientAddGroup.eq]
      rw [AddSubgroup.mem_addSubgroupOf]
      have : -(f q) + f q' ∈ M := by
        have := M.neg_mem hxy
        simpa [neg_sub, sub_eq_neg_add] using this
      simpa [f] using this
    rw [this]
  · intro y hy
    refine ⟨f (QuotientAddGroup.mk (⟨y, hy⟩ : N)), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h1 := QuotientAddGroup.out_eq' (QuotientAddGroup.mk (⟨y, hy⟩ : N) : N ⧸ M.addSubgroupOf N)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
    convert h1 using 1
    simp only [f, AddSubgroup.coe_add, AddSubgroup.coe_neg]
    abel
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl

end Reps

section
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cU_eq_one_iff (H : Sesq V) (A B : AddSubgroup V) (b : B) (a : A) :
    cU H A B b a = 1 ↔ ∃ m : ℤ, altE H (a : V) (b : V) = m := by
  unfold cU
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    have : ((altE H (a : V) (b : V) : ℝ) : ℂ) = ((-n : ℤ) : ℂ) := by
      apply mul_right_cancel₀ h2
      push_cast
      linear_combination -hn
    exact_mod_cast this
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    rw [hm]; push_cast; ring

end

section Moves
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem relIndex_addSubgroupOf_inf (X Y Z : AddSubgroup V) :
    (X.addSubgroupOf Z).relIndex (Y.addSubgroupOf Z) = (X ⊓ Z).relIndex (Y ⊓ Z) := by
  rw [← AddSubgroup.inf_addSubgroupOf_right Y Z, AddSubgroup.relIndex_addSubgroupOf inf_le_right,
    ← AddSubgroup.inf_relIndex_right, ← AddSubgroup.inf_relIndex_right (X ⊓ Z)]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf]
  tauto

theorem bichar_swap {k : Type*} [Field k] {A B : Type*} [AddCommGroup A] [AddCommGroup B] {c : B → A → k}
    (h : IsBichar c) : IsBichar (fun a b => c b a) :=
  ⟨fun a b => h.1 b a, fun a a' b => h.2.2 b a a', fun a b b' => h.2.1 b b' a⟩

theorem sqrt_div_mul_eq_sqrt_mul (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (Real.sqrt (a * b))⁻¹ * b = (Real.sqrt (a / b))⁻¹ := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hbb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  rw [Real.sqrt_div ha.le, Real.sqrt_mul ha.le]
  field_simp
  nlinarith [hbb]

theorem MovesU_of (hMv : Moves) (hID : IndexDual) : MovesU := by
  intro V _ _ H α A B Λ₀ Λ₁ hH hA hB g0 g1 hfin θ hθ Xi hXi
  classical
  obtain ⟨hbc, hheis⟩ := heisenberg_unitary_holds V H α A B hH hA hB
  have int0 : ∀ x ∈ Λ₀, ∀ y ∈ Λ₀, ∃ m : ℤ, altE H x y = m :=
    fun x hx y hy => (semiCharBasic V H hH Λ₀ α g0.1).2.2 hx y hy
  have int1 : ∀ x ∈ Λ₁, ∀ y ∈ Λ₁, ∃ m : ℤ, altE H x y = m :=
    fun x hx y hy => (semiCharBasic V H hH Λ₁ α g1.1).2.2 hx y hy
  have o1 : ∀ b : B, b ∈ Λ₀.addSubgroupOf B ↔ ∀ a ∈ Λ₀.addSubgroupOf A, cU H A B b a = 1 := by
    intro b
    simp only [AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro hb a ha
      exact (cU_eq_one_iff H A B b a).2 (int0 _ ha _ hb)
    · intro h
      exact g0.2.2.2.2 b b.2 fun a ha haΛ =>
        (cU_eq_one_iff H A B b ⟨a, ha⟩).1 (h ⟨a, ha⟩ (by simpa [AddSubgroup.mem_addSubgroupOf] using haΛ))
  have o2 : ∀ b ∈ Λ₁.addSubgroupOf B, ∀ a ∈ Λ₁.addSubgroupOf A, cU H A B b a = 1 := by
    intro b hb a ha
    rw [AddSubgroup.mem_addSubgroupOf] at hb ha
    exact (cU_eq_one_iff H A B b a).2 (int1 _ ha _ hb)
  have o3 : ∀ a : A, (∀ b ∈ Λ₁.addSubgroupOf B, cU H A B b a = 1) → a ∈ Λ₁.addSubgroupOf A := by
    intro a h
    rw [AddSubgroup.mem_addSubgroupOf]
    exact g1.2.2.2.1 a a.2 fun b hb hbΛ =>
      (cU_eq_one_iff H A B ⟨b, hb⟩ a).1 (h ⟨b, hb⟩ (by simpa [AddSubgroup.mem_addSubgroupOf] using hbΛ))
  have hfinB : (Λ₀.addSubgroupOf B).relIndex (Λ₁.addSubgroupOf B) ≠ 0 := by
    rw [relIndex_addSubgroupOf_inf, ← AddSubgroup.inf_relIndex_right (Λ₀ ⊓ B)]
    have e : Λ₀ ⊓ B ⊓ (Λ₁ ⊓ B) = Λ₀ ⊓ (Λ₁ ⊓ B) := by
      ext x; simp only [AddSubgroup.mem_inf]; tauto
    rw [e, AddSubgroup.inf_relIndex_right]
    intro h0
    exact hfin (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h0)
  have hfinA : (Λ₀.addSubgroupOf A).relIndex (Λ₁.addSubgroupOf A) ≠ 0 := by
    rw [relIndex_addSubgroupOf_inf, ← AddSubgroup.inf_relIndex_right (Λ₀ ⊓ A)]
    have e : Λ₀ ⊓ A ⊓ (Λ₁ ⊓ A) = Λ₀ ⊓ (Λ₁ ⊓ A) := by
      ext x; simp only [AddSubgroup.mem_inf]; tauto
    rw [e, AddSubgroup.inf_relIndex_right]
    intro h0
    exact hfin (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h0)

  have hdual : (Λ₁.addSubgroupOf A).relIndex (Λ₀.addSubgroupOf A) =
      (Λ₀.addSubgroupOf B).relIndex (Λ₁.addSubgroupOf B) := by
    refine hID ℂ B A (fun a b => cU H A B b a) (bichar_swap hbc) (Λ₁.addSubgroupOf B) (Λ₀.addSubgroupOf B)
      (Λ₁.addSubgroupOf A) (Λ₀.addSubgroupOf A) ?_ ?_ ?_ hfinB
    · intro a
      exact ⟨fun ha b hb => o2 b hb a ha, fun h => o3 a h⟩
    · intro a ha b hb
      exact (o1 b).1 hb a ha
    · intro b hb h
      exact (o1 b).2 h
  obtain ⟨SA, hSA, hSAc⟩ := repsG_exist _ _ hfinA
  obtain ⟨SB, hSB, hSBc⟩ := repsG_exist _ _ hfinB
  have hSBne : (SB.card : ℂ) ≠ 0 := by rw [hSBc]; exact_mod_cast hfinB
  obtain ⟨h, hsum⟩ := hMv ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis
    (Λ₀.addSubgroupOf A) (Λ₁.addSubgroupOf A) (Λ₀.addSubgroupOf B) (Λ₁.addSubgroupOf B) θ Xi hXi
    o1 o2 (fun a _ h => o3 a h) SA SB hSA hSB hSBne
  refine ⟨h, ?_, ?_⟩
  · unfold volA
    have h1 : 0 < (Λ₀ ⊓ A).relIndex (Λ₁ ⊓ A) := by
      rw [← relIndex_addSubgroupOf_inf]; exact Nat.pos_of_ne_zero hfinA
    have h2 : 0 < (Λ₁ ⊓ A).relIndex (Λ₀ ⊓ A) := by
      rw [← relIndex_addSubgroupOf_inf, hdual]; exact Nat.pos_of_ne_zero hfinB
    positivity

  let f : A × B → V := fun p => (p.1 : V) + (p.2 : V)
  have key : ∀ p ∈ SA ×ˢ SB, ∀ q ∈ SA ×ˢ SB, f p - f q ∈ Λ₀ → p = q := by
    intro p hp q hq hpq
    rw [Finset.mem_product] at hp hq
    have e : f p - f q = ((p.1 : V) - q.1) + ((p.2 : V) - q.2) := by simp only [f]; abel
    rw [e] at hpq
    have ha : ((p.1 : V) - q.1) ∈ Λ₀ :=
      g0.2.2.1 _ (A.sub_mem p.1.2 q.1.2) _ (B.sub_mem p.2.2 q.2.2) hpq
    have e1 : p.1 = q.1 := hSA.2.1 _ hp.1 _ hq.1 (by simpa [AddSubgroup.mem_addSubgroupOf] using ha)
    have hb : ((p.2 : V) - q.2) ∈ Λ₀ := by
      have := Λ₀.sub_mem hpq ha
      simpa using this
    have e2 : p.2 = q.2 := hSB.2.1 _ hp.2 _ hq.2 (by simpa [AddSubgroup.mem_addSubgroupOf] using hb)
    exact Prod.ext e1 e2
  have hinj : Set.InjOn f (SA ×ˢ SB : Finset (A × B)) := by
    intro p hp q hq hpq
    exact key p hp q hq (by rw [hpq, sub_self]; exact Λ₀.zero_mem)
  let S : Finset V := (SA ×ˢ SB).image f
  have hS : IsReps Λ₀ Λ₁ S := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_product] at hp
      have h1 := hSA.1 _ hp.1
      have h2 := hSB.1 _ hp.2
      rw [AddSubgroup.mem_addSubgroupOf] at h1 h2
      exact Λ₁.add_mem h1 h2
    · intro x hx y hy hxy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      rw [key p hp q hq hxy]
    · intro y hy
      obtain ⟨y1, hy1, y2, hy2, rfl⟩ := AddSubgroup.mem_sup.1 (g1.2.1 hy)
      obtain ⟨a, ha, ha'⟩ := hSA.2.2 ⟨y1, hy1.2⟩ (by simpa [AddSubgroup.mem_addSubgroupOf] using hy1.1)
      obtain ⟨b, hb, hb'⟩ := hSB.2.2 ⟨y2, hy2.2⟩ (by simpa [AddSubgroup.mem_addSubgroupOf] using hy2.1)
      refine ⟨f (a, b), Finset.mem_image_of_mem _ (Finset.mem_product.2 ⟨ha, hb⟩), ?_⟩
      rw [AddSubgroup.mem_addSubgroupOf] at ha' hb'
      have e : y1 + y2 - f (a, b) = (y1 - a) + (y2 - b) := by simp only [f]; abel
      rw [e]
      exact Λ₀.add_mem (by simpa using ha') (by simpa using hb')
  have hcard : S.card = SA.card * SB.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product]
  have hn : relIdx Λ₀ Λ₁ = SA.card * SB.card := by
    rw [← hcard]; exact ((repsExist V Λ₀ Λ₁ hfin).2 S hS).symm
  funext z
  rw [interReps V H hH Λ₀ Λ₁ α g1.1 θ hθ S hS z]
  have hsumU : sumU H α S θ z = (SB.card : ℂ) * Xi ⟨_, h⟩ z := by
    have := congrFun hsum z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    unfold sumU
    rw [Finset.sum_image hinj, Finset.sum_product]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    have h1 := hSA.1 _ ha
    have h2 := hSB.1 _ hb
    rw [AddSubgroup.mem_addSubgroupOf] at h1 h2
    simp only [wA, wB, wU, LinearMap.coe_mk, AddHom.coe_mk, f]
    exact (semiHom V H hH Λ₁ α g1.1 _ h1 _ h2 θ z).symm
  rw [hsumU, hn]
  have hA' : ((Λ₀ ⊓ A).relIndex (Λ₁ ⊓ A) : ℝ) = SA.card := by
    rw [hSAc, relIndex_addSubgroupOf_inf]
  have hB' : ((Λ₁ ⊓ A).relIndex (Λ₀ ⊓ A) : ℝ) = SB.card := by
    rw [hSBc, ← hdual, relIndex_addSubgroupOf_inf]
  have hpa : (0 : ℝ) < SA.card := by rw [hSAc]; exact_mod_cast Nat.pos_of_ne_zero hfinA
  have hpb : (0 : ℝ) < SB.card := by rw [hSBc]; exact_mod_cast Nat.pos_of_ne_zero hfinB
  have hv : volA A Λ₀ Λ₁ = (SA.card : ℝ) / SB.card := by unfold volA; rw [hA', hB']
  rw [hv, ← sqrt_div_mul_eq_sqrt_mul _ _ hpa hpb]
  simp only [Pi.smul_apply, Complex.real_smul, Nat.cast_mul]
  push_cast
  ring

end Moves

end Formalism.L2.PairingIndexBounds.Mv
