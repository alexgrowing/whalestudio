import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymPattern
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

section Field
variable {F : Type} [Field F] {κ l : ℕ}

theorem mul_fromBlocks_inl (M : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) (C : Matrix (Fin κ) (Fin κ) F)
    (a : Fin κ ⊕ Fin l) (j : Fin κ) :
    (M * (fromBlocks C 0 0 1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) : Matrix _ _ F) a (Sum.inl j) = ∑ t, M a (Sum.inl t) * C t j := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

theorem mul_fromBlocks_inr (M : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) (C : Matrix (Fin κ) (Fin κ) F)
    (a : Fin κ ⊕ Fin l) (j : Fin l) :
    (M * (fromBlocks C 0 0 1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) : Matrix _ _ F) a (Sum.inr j) = M a (Sum.inr j) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem pat_of_mul (ρ : ℕ) (u : GL (Fin κ ⊕ Fin l) F) (hu : InN (ρ + 1) u) (γ : GL (Fin κ) F)
    (hγ : IsUpperUnip Fin.val γ.val) :
    ∀ a b, ¬ FreeTop ρ a b → (u * embX l γ).val a b = (1 : Matrix _ _ F) a b := by
  intro a b hab
  have hv : (u * embX l γ).val = u.val * fromBlocks γ.val 0 0 1 := by
    rw [Units.val_mul, Radical.embX_val]
  rw [hv]
  rcases a with i | i <;> rcases b with j | j <;> simp only [FreeTop, not_lt] at hab
  · rw [mul_fromBlocks_inl]
    have hu' : ∀ t, u.val (Sum.inl i) (Sum.inl t) = if i = t then 1 else 0 := fun t => by
      rw [hu (Sum.inl i) (Sum.inl t) le_rfl, Matrix.one_apply]; simp
    simp only [hu', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hγ i j (by exact_mod_cast hab)]
    simp [Matrix.one_apply]
  · rw [mul_fromBlocks_inr, hu (Sum.inl i) (Sum.inr j) (Nat.succ_le_succ hab)]
  · rw [mul_fromBlocks_inl]
    have hu' : ∀ t, u.val (Sum.inr i) (Sum.inl t) = 0 := fun t => by
      rw [hu (Sum.inr i) (Sum.inl t) (Nat.succ_le_succ hab)]; simp
    simp [hu']
  · rw [mul_fromBlocks_inr, hu (Sum.inr i) (Sum.inr j) (Nat.succ_le_succ hab)]

theorem exists_of_pat (ρ : ℕ) (gb : GL (Fin κ ⊕ Fin l) F)
    (h : ∀ a b, ¬ FreeTop ρ a b → gb.val a b = (1 : Matrix _ _ F) a b) :
    ∃ u : GL (Fin κ ⊕ Fin l) F, InN (ρ + 1) u ∧ ∃ γ : GL (Fin κ) F,
      IsUpperUnip Fin.val γ.val ∧ gb = u * embX l γ := by
  have hU : IsUpperUnip Fin.val gb.val.toBlocks₁₁ := fun r t hrt => by
    have := h (Sum.inl r) (Sum.inl t) (by simp only [FreeTop, not_lt]; exact hrt)
    simpa [Matrix.toBlocks₁₁, Matrix.one_apply] using this
  have hdet : gb.val.toBlocks₁₁.det = 1 := Radical.Uni.det (b := Fin.val) hU
  let γ : GL (Fin κ) F := ⟨gb.val.toBlocks₁₁, gb.val.toBlocks₁₁⁻¹,
    Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_one),
    Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one)⟩
  refine ⟨gb * (embX l γ)⁻¹, ?_, γ, hU, (inv_mul_cancel_right gb _).symm⟩
  have hv : (gb * (embX l γ)⁻¹).val = gb.val * fromBlocks (γ⁻¹).val 0 0 1 := by
    rw [Units.val_mul, ← map_inv, Radical.embX_val]
  intro r t hrt
  rw [hv]
  rcases r with i | i <;> rcases t with j | j
  · rw [mul_fromBlocks_inl]
    have hm : ∑ q, gb.val (Sum.inl i) (Sum.inl q) * (γ⁻¹).val q j =
        (1 : Matrix (Fin κ) (Fin κ) F) i j := by
      have := congrFun (congrFun γ.mul_inv i) j
      rw [Matrix.mul_apply] at this
      exact this
    rw [hm]
    simp [Matrix.one_apply]
  · have hrt' : j.val + 1 ≤ ρ + 1 := hrt
    rw [mul_fromBlocks_inr]
    exact h _ _ (by simp only [FreeTop, not_lt]; omega)
  · have hrt' : ρ + 1 ≤ i.val + 1 := hrt
    rw [mul_fromBlocks_inl]
    have hz : ∀ q, gb.val (Sum.inr i) (Sum.inl q) = 0 := fun q => by
      have := h (Sum.inr i) (Sum.inl q) (by simp only [FreeTop, not_lt]; omega)
      simpa [Matrix.one_apply] using this
    simp [hz]
  · have hrt' : j.val + 1 ≤ i.val + 1 := hrt
    rw [mul_fromBlocks_inr]
    exact h _ _ (by simp only [FreeTop, not_lt]; exact Fin.le_def.mpr (by omega))

end Field

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem valuation_lt_one_iff_residue_eq_zero (y : 𝒪[k]) :
    valuation k (y : k) < 1 ↔ IsLocalRing.residue 𝒪[k] y = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.symm

theorem entry_lt_iff (g₀ : GL ι 𝒪[k]) (a b : ι) :
    valuation k ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀).val a b - (1 : Matrix ι ι k) a b) < 1 ↔
      (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀).val a b = (1 : Matrix ι ι 𝓀[k]) a b := by
  have e1 : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀).val a b - (1 : Matrix ι ι k) a b =
      ((g₀.val a b - (1 : Matrix ι ι 𝒪[k]) a b : 𝒪[k]) : k) := by
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab] <;> rfl
  have e2 : (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀).val a b -
      (1 : Matrix ι ι 𝓀[k]) a b = IsLocalRing.residue 𝒪[k] (g₀.val a b - (1 : Matrix ι ι 𝒪[k]) a b) := by
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [e1, valuation_lt_one_iff_residue_eq_zero, ← e2, sub_eq_zero]

end Local

end GlobalTheory.SymPattern

theorem GlobalTheory.SymChain.SymData.mem_J_iff_pattern :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ)
      (S : SymData k s κ) (g : GL (Fin κ ⊕ Fin (s + 1)) k),
      g ∈ S.P.J ↔ g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop S.ρ a b →
        valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  intro k _ _ _ _ s κ S g
  rw [S.sym.1 g]
  constructor
  · rintro ⟨u, hu, γ, hγ, g₀, hg₀, hgb⟩
    refine ⟨⟨g₀, hg₀⟩, fun a b hab => ?_⟩
    rw [← hg₀, SymPattern.entry_lt_iff, hgb]
    exact SymPattern.pat_of_mul S.ρ u ((Radical.mem_N_iff u).mp hu) γ hγ a b hab
  · rintro ⟨⟨g₀, hg₀⟩, hpat⟩
    obtain ⟨u, hu, γ, hγ, he⟩ := SymPattern.exists_of_pat S.ρ
      (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀) (fun a b hab => by
        rw [← SymPattern.entry_lt_iff, hg₀]; exact hpat a b hab)
    exact ⟨u, (Radical.mem_N_iff u).mpr hu, γ, hγ, g₀, hg₀, he⟩
