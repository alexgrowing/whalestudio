import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleRestrictionMirabolicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleRestrictionMirabolicRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetCharacteristicPolynomialLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetCharacteristicPolynomialRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetDetPairFiltrationLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetDetPairFiltrationRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetDetPairFiltrationSwapLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetDetPairFiltrationSwapRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetPairInducedNontrivialStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

namespace GlobalTheory.MixedCell

open GlobalTheory.Published in

theorem isIrreducible : GlobalTheory.Published.GeometricLemmaFiltration → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x y : ℕ), x ≠ y → ∀ (α β : kˣ →* ℂˣ), IsSmoothChar α → IsSmoothChar β →
    (∀ t, ‖((α t : ℂˣ) : ℂ)‖ = 1) → (∀ t, ‖((β t : ℂˣ) : ℂ)‖ = 1) →
    (prod₂ (detRep (Fin x) (α * absPow k (1 / 2))) (detRep (Fin y) (β * absPow k (-(1 / 2))))).IsIrreducible ∧
    (prod₂ (detRep (Fin x) (α * absPow k (-(1 / 2)))) (detRep (Fin y) (β * absPow k (1 / 2)))).IsIrreducible := by
  intro hG hBZ hB k _ _ _ _ x y hxy α β hαs hβs hαu hβu
  obtain ⟨ϖ, -, hϖ⟩ := GlobalTheory.CentralExponent.exists_nabs_lt_one k
  set q := GlobalTheory.SplitWeil.nabs k ϖ with hqdef
  have hq0 : 0 < q := nabs_pos' k ϖ
  have hsm : ∀ (γ : kˣ →* ℂˣ) (s : ℂ), IsSmoothChar γ → IsSmoothChar (γ * absPow k s) :=
    fun γ s h => h.mul (isSmoothChar_of_isUnram (isUnram_absPow k s))
  have hnorm : ∀ (γ : kˣ →* ℂˣ) (s : ℂ),
      ‖(((γ * absPow k s) ϖ : ℂˣ) : ℂ)‖ = ‖((γ ϖ : ℂˣ) : ℂ)‖ * q ^ s.re := by
    intro γ s
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, val_absPow,
      Complex.norm_cpow_eq_rpow_re_of_pos hq0]
  have hne : ∀ (γ δ : kˣ →* ℂˣ) (a b : ℝ), ‖((γ ϖ : ℂˣ) : ℂ)‖ = q ^ a → ‖((δ ϖ : ℂˣ) : ℂ)‖ = q ^ b →
      a ≠ b → ((γ ϖ : ℂˣ) : ℂ) ≠ ((δ ϖ : ℂˣ) : ℂ) := by
    intro γ δ a b hγ hδ hab h
    have h1 := congrArg norm h
    rw [hγ, hδ] at h1
    have h2 := congrArg Real.log h1
    rw [Real.log_rpow hq0, Real.log_rpow hq0] at h2
    exact hab (mul_right_cancel₀ (Real.log_neg hq0 hϖ).ne h2)

  have n1 : ∀ (γ : kˣ →* ℂˣ), (∀ t, ‖((γ t : ℂˣ) : ℂ)‖ = 1) → ∀ s : ℂ,
      ‖(((γ * absPow k s) ϖ : ℂˣ) : ℂ)‖ = q ^ s.re := by
    intro γ hγ s; rw [hnorm, hγ, one_mul]
  have n2 : ∀ (γ : kˣ →* ℂˣ), (∀ t, ‖((γ t : ℂˣ) : ℂ)‖ = 1) → ∀ s s' : ℂ,
      ‖((((γ * absPow k s) * absPow k s') ϖ : ℂˣ) : ℂ)‖ = q ^ (s.re + s'.re) := by
    intro γ hγ s s'; rw [hnorm, n1 γ hγ, Real.rpow_add hq0]
  have hx : (x : ℝ) ≠ y := by exact_mod_cast hxy

  have hirr0 : (prod₂ (detRep (Fin (x + 1)) α) (detRep (Fin (y + 1)) β)).IsIrreducible := by
    have h1 := BernsteinUnitaryProductIrreducible.detRep_hyp (k := k) (x + 1) hαs hαu
    have h2 := BernsteinUnitaryProductIrreducible.detRep_hyp (k := k) (y + 1) hβs hβu
    exact hB k (x + 1) (y + 1) ℂ ℂ _ _ h1.1 h1.2.1 h1.2.2 h2.1 h2.2.1 h2.2.2
  have hα2 := hsm α (1 / 2) hαs
  have hα2' := hsm α (-(1 / 2)) hαs
  have hβ2 := hsm β (1 / 2) hβs
  have hβ2' := hsm β (-(1 / 2)) hβs
  have hpoly : ∀ (z c₁ c₂ : ℂ), z ≠ c₁ → z ≠ c₂ →
      ((Polynomial.X - Polynomial.C c₁) * (Polynomial.X - Polynomial.C c₂)).eval z ≠ 0 := by
    intro z c₁ c₂ h₁ h₂
    rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_C]
    exact mul_ne_zero (sub_ne_zero.2 h₁) (sub_ne_zero.2 h₂)
  constructor
  ·
    have step1 : (prod₂ (detRep (Fin x) (α * absPow k (1 / 2))) (detRep (Fin (y + 1)) β)).IsIrreducible := by
      obtain ⟨hnt, hfl⟩ := GlobalTheory.T.det_pair_induced_nontrivial hBZ (α * absPow k (1 / 2)) β hα2 hβs x (y + 1)
      let e := stdSum (show 1 + (x + (y + 1)) = x + 1 + (y + 1) by omega)
      obtain ⟨N, S, hS, h0, hN, t₀, ⟨φ⟩, hoth⟩ := GlobalTheory.T.jacquet_det_pair_filtration_left hG α β hαs hβs x (y + 1) e ϖ
      refine GlobalTheory.T.irreducible_restriction_mirabolic hG e _ _ (isSmooth_prod₂ _ _) hirr0 (isSmooth_prod₂ _ _) hfl
        (α * absPow k (-(x : ℂ) / 2)) (hsm _ _ hαs) ϖ N S hS h0 hN t₀ φ
        (fun t ht => ⟨_, hne _ _ _ _ (n1 β hβu _) (n1 α hαu _) (by norm_num <;> first | omega | (intro h; linarith) | (intro h; apply hx; linarith)), hoth t ht⟩) ?_
      intro m' _ _ e'
      exact ⟨_, hpoly _ _ _ (hne _ _ _ _ (n1 α hαu _) (n2 α hαu _ _) (by norm_num <;> first | omega | (intro h; linarith) | (intro h; apply hx; linarith)))
        (hne _ _ _ _ (n1 α hαu _) (n1 β hβu _) (by norm_num <;> first | omega | (intro h; linarith) | (intro h; apply hx; linarith))),
        GlobalTheory.T.jacquet_characteristic_polynomial_left hG (α * absPow k (1 / 2)) β hα2 hβs x (y + 1) m' e' ϖ⟩
    obtain ⟨hnt, hfl⟩ := GlobalTheory.T.det_pair_induced_nontrivial hBZ (α * absPow k (1 / 2)) (β * absPow k (-(1 / 2))) hα2 hβ2' x y
    let e := stdSum (show x + y + 1 = x + (y + 1) by omega)
    obtain ⟨N, S, hS, h0, hN, t₀, ⟨φ⟩, hoth⟩ := GlobalTheory.T.jacquet_det_pair_filtration_swap_right hG (α * absPow k (1 / 2)) β hα2 hβs x y e ϖ
    refine GlobalTheory.T.irreducible_restriction_mirabolic_right hG e _ _ (isSmooth_prod₂ _ _) step1 (isSmooth_prod₂ _ _) hfl
      (β * absPow k ((y : ℂ) / 2)) (hsm _ _ hβs) ϖ N S hS h0 hN t₀ φ
      (fun t ht => ⟨_, hne _ _ _ _ (n2 α hαu _ _) (n1 β hβu _) (by norm_num <;> first | omega | (intro h; linarith) | (intro h; apply hx; linarith)), hoth t ht⟩) ?_
    intro m' _ _ e'
    exact ⟨_, hpoly _ _ _ (hne _ _ _ _ (n1 β hβu _) (n2 α hαu _ _) (by norm_num <;> first | omega | (intro h; linarith) | (intro h; apply hx; linarith)))
      (hne _ _ _ _ (n1 β hβu _) (n2 β hβu _ _) (by norm_num <;> first | omega | (intro h; linarith) | (intro h; apply hx; linarith))),
      GlobalTheory.T.jacquet_characteristic_polynomial_right hG (α * absPow k (1 / 2)) (β * absPow k (-(1 / 2))) hα2 hβ2' x y m' e' ϖ⟩
  ·
    have step1 : (prod₂ (detRep (Fin (x + 1)) α) (detRep (Fin y) (β * absPow k (1 / 2)))).IsIrreducible := by
      obtain ⟨hnt, hfl⟩ := GlobalTheory.T.det_pair_induced_nontrivial hBZ α (β * absPow k (1 / 2)) hαs hβ2 (x + 1) y
      let e := stdSum (show 1 + (x + 1 + y) = x + 1 + (y + 1) by omega)
      obtain ⟨N, S, hS, h0, hN, t₀, ⟨φ⟩, hoth⟩ := GlobalTheory.T.jacquet_det_pair_filtration_right hG α β hαs hβs (x + 1) y e ϖ
      refine GlobalTheory.T.irreducible_restriction_mirabolic hG e _ _ (isSmooth_prod₂ _ _) hirr0 (isSmooth_prod₂ _ _) hfl
        (β * absPow k (-(y : ℂ) / 2)) (hsm _ _ hβs) ϖ N S hS h0 hN t₀ φ
        (fun t ht => ⟨_, hne _ _ _ _ (n1 α hαu _) (n1 β hβu _) (by norm_num <;> first | omega | (intro h; linarith) | (intro h; apply hx; linarith)), hoth t ht⟩) ?_
      intro m' _ _ e'
      exact ⟨_, hpoly _ _ _ (hne _ _ _ _ (n1 β hβu _) (n1 α hαu _) (by norm_num <;> first | omega | (intro h; linarith) | (intro h; apply hx; linarith)))
        (hne _ _ _ _ (n1 β hβu _) (n2 β hβu _ _) (by norm_num <;> first | omega | (intro h; linarith) | (intro h; apply hx; linarith))),
        GlobalTheory.T.jacquet_characteristic_polynomial_left hG α (β * absPow k (1 / 2)) hαs hβ2 (x + 1) y m' e' ϖ⟩
    obtain ⟨hnt, hfl⟩ := GlobalTheory.T.det_pair_induced_nontrivial hBZ (α * absPow k (-(1 / 2))) (β * absPow k (1 / 2)) hα2' hβ2 x y
    let e := stdSum (show x + y + 1 = x + 1 + y by omega)
    obtain ⟨N, S, hS, h0, hN, t₀, ⟨φ⟩, hoth⟩ := GlobalTheory.T.jacquet_det_pair_filtration_swap_left hG α (β * absPow k (1 / 2)) hαs hβ2 x y e ϖ
    refine GlobalTheory.T.irreducible_restriction_mirabolic_right hG e _ _ (isSmooth_prod₂ _ _) step1 (isSmooth_prod₂ _ _) hfl
      (α * absPow k ((x : ℂ) / 2)) (hsm _ _ hαs) ϖ N S hS h0 hN t₀ φ
      (fun t ht => ⟨_, hne _ _ _ _ (n2 β hβu _ _) (n1 α hαu _) (by norm_num <;> first | omega | (intro h; linarith) | (intro h; apply hx; linarith)), hoth t ht⟩) ?_
    intro m' _ _ e'
    exact ⟨_, hpoly _ _ _ (hne _ _ _ _ (n1 α hαu _) (n2 α hαu _ _) (by norm_num <;> first | omega | (intro h; linarith) | (intro h; apply hx; linarith)))
      (hne _ _ _ _ (n1 α hαu _) (n2 β hβu _ _) (by norm_num <;> first | omega | (intro h; linarith) | (intro h; apply hx; linarith))),
      GlobalTheory.T.jacquet_characteristic_polynomial_right hG (α * absPow k (-(1 / 2))) (β * absPow k (1 / 2)) hα2' hβ2 x y m' e' ϖ⟩

end GlobalTheory.MixedCell
