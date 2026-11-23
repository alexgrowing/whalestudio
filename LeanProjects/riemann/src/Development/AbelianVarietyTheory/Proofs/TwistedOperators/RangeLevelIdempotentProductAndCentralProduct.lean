import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevRange

theorem range_sum_eq_eig {G M : Type} [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (P : Subgroup G) (χ : P → ℂ) (E : G → ℂ) (k : ℂ) (hk : k ≠ 0) (h0 : ∀ g, g ∉ P → E g = 0)
    (h1 : ∀ g : P, E g * χ g = k) (hm : ∀ a b : P, χ (a * b) = χ a * χ b) :
    LinearMap.range (∑ g, E g • ρ g) = eig ρ P χ := by
  classical
  have hs : ∀ (p : P) (g : G), E g = χ p * E (p * g) := by
    intro p g
    by_cases hg : g ∈ P
    · have e1 := h1 ⟨g, hg⟩
      have e2 := h1 (p * ⟨g, hg⟩)
      rw [hm] at e2
      have hne : χ ⟨g, hg⟩ ≠ 0 := by
        intro h; rw [h, mul_zero] at e1; exact hk e1.symm
      apply mul_right_cancel₀ hne
      simp only [Subgroup.coe_mul] at e1 e2
      rw [e1, ← e2]; ring
    · have : (p : G) * g ∉ P := fun h => hg ((P.mul_mem_cancel_left p.2).1 h)
      rw [h0 g hg, h0 _ this, mul_zero]
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [mem_eig]
    intro p
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft (p : G)) (fun g => χ p • E g • ρ g y)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hs p g, Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, mul_smul]
  · intro x hx
    rw [mem_eig] at hx
    have hT : (∑ g, E g • ρ g) x = (∑ g : G, if g ∈ P then k else 0) • x := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_smul]
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases hg : g ∈ P
      · rw [if_pos hg, ← h1 ⟨g, hg⟩, mul_smul, ← hx ⟨g, hg⟩]
      · rw [if_neg hg, h0 g hg, zero_smul, zero_smul]
    have hne : (∑ g : G, if g ∈ P then k else 0) ≠ 0 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      refine mul_ne_zero ?_ hk
      have : (Finset.univ.filter fun g : G => g ∈ P).Nonempty := ⟨1, by simp⟩
      exact_mod_cast this.card_pos.ne'
    refine ⟨(∑ g : G, if g ∈ P then k else 0)⁻¹ • x, ?_⟩
    rw [map_smul, hT, smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem range_mul_eq_inf {M : Type} [AddCommGroup M] [Module ℂ M] (C T : Module.End ℂ M) (hC : C * C = C)
    (hc : C * T = T * C) : LinearMap.range (C * T) = LinearMap.range T ⊓ LinearMap.ker (C - LinearMap.id) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    refine ⟨⟨C y, ?_⟩, ?_⟩
    · rw [hc]; rfl
    · have : C (C (T y)) = C (T y) := by rw [← Module.End.mul_apply, hC]
      simp [this]
  · rintro _ ⟨⟨y, rfl⟩, h⟩
    refine ⟨y, ?_⟩
    simpa [sub_eq_zero] using h

theorem op_comp {G H M : Type} [Group G] [Fintype G] [Group H] [Fintype H] [AddCommGroup M] [Module ℂ M]
    (Φ : G ≃* H) (ρ : Representation ℂ G M) (e : H → ℂ) :
    GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) e = ∑ g, e (Φ g) • ρ g := by
  unfold GlobalTheory.BadShare.op
  rw [← Equiv.sum_comp Φ.toEquiv]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp

theorem tens_e_mul {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N)
    (γ : ι → GlobalTheory.BadShare.GG g N) (h : ∀ v, (L v).Mem (γ v)) :
    GlobalTheory.BadShare.tens (fun v => (L v).e) γ * ∏ v, (L v).chi (γ v) = ∏ v, (Nat.card {u // (L v).Mem u} : ℂ)⁻¹ := by
  unfold GlobalTheory.BadShare.tens
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have := GlobalTheory.BadShare.Basic.chi_ne (L v) (γ v)
  simp only [GlobalTheory.BadShare.Lev.e, GlobalTheory.BadShare.eps, if_pos (h v)]
  field_simp

theorem tens_e_zero {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N)
    (γ : ι → GlobalTheory.BadShare.GG g N) (h : ¬ ∀ v, (L v).Mem (γ v)) :
    GlobalTheory.BadShare.tens (fun v => (L v).e) γ = 0 := by
  obtain ⟨v, hv⟩ := not_forall.1 h
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp only [GlobalTheory.BadShare.Lev.e, GlobalTheory.BadShare.eps, if_neg hv])

theorem prod_card_ne {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N) :
    (∏ v, (Nat.card {u // (L v).Mem u} : ℂ)⁻¹) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun v _ => inv_ne_zero ?_
  haveI : Nonempty {u // (L v).Mem u} := ⟨⟨1, GlobalTheory.BadShare.Basic.mem_one (L v)⟩⟩
  exact_mod_cast Nat.card_pos.ne'

theorem ranges : ∀ (g₁ g₂ N : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (ι₁ ι₂ G M : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (Φ : G ≃* (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N)) (L₁ : ι₁ → GlobalTheory.BadShare.Lev g₁ N) (L₂ : ι₂ → GlobalTheory.BadShare.Lev g₂ N) (P : Subgroup G) (χ : P → ℂ) (ρ : Representation ℂ G M) [Fintype ((ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N))] (c : (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N) → ℂ), (∀ g : G, g ∈ P ↔ (∀ v, (L₁ v).Mem ((Φ g).1 v)) ∧ ∀ v, (L₂ v).Mem ((Φ g).2 v)) → (∀ g : P, χ g = (∏ v, (L₁ v).chi ((Φ g).1 v)) * ∏ v, (L₂ v).chi ((Φ g).2 v)) → GlobalTheory.BadShare.conv c c = c → (∀ a, GlobalTheory.BadShare.conv c a = GlobalTheory.BadShare.conv a c) → LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e))) = eig ρ P χ ∧ LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.conv c (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e)))) = eig ρ P χ ⊓ LinearMap.ker ((∑ g : G, c (Φ g) • ρ g) - LinearMap.id) := by
  intro g₁ g₂ N _ _ ι₁ ι₂ G M _ _ _ _ _ _ _ _ Φ L₁ L₂ P χ ρ _ c hP hχ hcc hc
  have key : LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e))) = eig ρ P χ := by
    rw [op_comp]
    refine range_sum_eq_eig ρ P χ _ _ (mul_ne_zero (prod_card_ne L₁) (prod_card_ne L₂)) ?_ ?_ ?_
    · intro g hg
      rw [hP, not_and_or] at hg
      unfold GlobalTheory.BadShare.tens2
      rcases hg with h | h
      · rw [tens_e_zero _ _ h, zero_mul]
      · rw [tens_e_zero L₂ _ h, mul_zero]
    · intro g
      obtain ⟨h1, h2⟩ := (hP g).1 g.2
      rw [hχ, ← tens_e_mul L₁ _ h1, ← tens_e_mul L₂ _ h2]
      unfold GlobalTheory.BadShare.tens2
      ring
    · intro a b
      obtain ⟨a1, a2⟩ := (hP a).1 a.2
      obtain ⟨b1, b2⟩ := (hP b).1 b.2
      rw [hχ, hχ, hχ]
      simp only [Subgroup.coe_mul, map_mul, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
      simp only [fun v => GlobalTheory.BadShare.Basic.chi_mul (L₁ v) (a1 v) (b1 v),
        fun v => GlobalTheory.BadShare.Basic.chi_mul (L₂ v) (a2 v) (b2 v), Finset.prod_mul_distrib]
      ring
  refine ⟨key, ?_⟩
  rw [GlobalTheory.BadShare.Basic.op_conv, range_mul_eq_inf, key, op_comp]
  · rw [← GlobalTheory.BadShare.Basic.op_conv, hcc]
  · rw [← GlobalTheory.BadShare.Basic.op_conv, hc, GlobalTheory.BadShare.Basic.op_conv]

end GlobalTheory.LevRange
