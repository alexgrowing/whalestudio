import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpEOmTargetUnipotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSumRowCol

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.CutRow

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

end GlobalTheory.RootEx.CutRow

open MeasureTheory ValuativeRel Matrix in

theorem _root_.GlobalTheory.RootEx.opE_cut_om_equivariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (χ : (n' → k) → ℂ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : GL n k), ∀ u ∈ _root_.GlobalTheory.RootEx.N k n c p ⊓ _root_.GlobalTheory.RootEx.N k n c (p + 1), _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => (∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) (Sum.inl s)) else 0) * _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x * u) Φ y) = (((_root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((p + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * (ψ (-_root_.GlobalTheory.RootEx.simpleSum u) : ℂ)) • _root_.GlobalTheory.SplitWeil.om μ 1 x (_root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => (∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) (Sum.inl s)) else 0) * Φ y)) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p hp1 hpc ψ ν _ μ χ Φ x u hu
  obtain ⟨huP, huP1⟩ := Subgroup.mem_inf.mp hu
  set cut : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ := fun y =>
    ∑ l : Fin c, if l.val + 1 = p then χ (fun s => y (Sum.inr l) (Sum.inl s)) else 0 with hcut
  have hlevi : ∀ (g : GL n k) (y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      cut (((_root_.GlobalTheory.RootEx.embX c g : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * y) = cut y := by
    intro g y
    simp only [hcut, _root_.GlobalTheory.RootEx.Radical.embX_val, _root_.GlobalTheory.RootEx.OpELevi.left_inr]
  have hgen : _root_.GlobalTheory.RootEx.InN p u⁻¹ :=
    _root_.GlobalTheory.RootEx.Model.mem_N_iff.mp (inv_mem huP)
  have hunip : ∀ (x₀ : Matrix n n' k) (e : { rs // _root_.GlobalTheory.RootEx.Free (p + 1) rs } → k),
      cut (((u⁻¹ : GL (n ⊕ Fin c) k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * _root_.GlobalTheory.RootEx.affPt (p + 1) x₀ e) =
        cut (_root_.GlobalTheory.RootEx.affPt (p + 1) x₀ e) := by
    intro x₀ e
    simp only [hcut]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with hl
    · congr 1
      funext s
      rw [_root_.GlobalTheory.RootEx.TargetUnip.mul_apply_of_inN hgen, Finset.sum_eq_zero, add_zero]
      intro r _
      split_ifs with hlt
      · cases r with
        | inl i =>
          simp [_root_.GlobalTheory.RootEx.lev] at hlt
          omega
        | inr i =>
          simp [_root_.GlobalTheory.RootEx.lev] at hlt
          rw [_root_.GlobalTheory.RootEx.TargetUnip.affPt_of_not_free]
          · simp [_root_.GlobalTheory.RootEx.basePt]
          · simp [_root_.GlobalTheory.RootEx.Free]
            omega
      · rfl
    · rfl
  have hmul : _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x * u) Φ =
      _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x) (_root_.GlobalTheory.SplitWeil.om μ 1 u Φ) := by
    have h := _root_.GlobalTheory.SplitWeil.Model.om_mul μ 1 1 (_root_.GlobalTheory.RootEx.embX c x) u Φ
    rwa [one_mul] at h
  have hcomm : ∀ Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ,
      (fun y => cut y * _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x) Ψ y) =
        _root_.GlobalTheory.SplitWeil.om μ 1 (_root_.GlobalTheory.RootEx.embX c x) (fun y => cut y * Ψ y) := by
    intro Ψ
    funext y
    simp only [_root_.GlobalTheory.SplitWeil.om, Units.val_one, Matrix.mul_one, ← map_inv, hlevi]
    ring
  have hcut_unip : _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (fun y => cut y * _root_.GlobalTheory.SplitWeil.om μ 1 u Φ y) =
      _root_.GlobalTheory.RootEx.opE ψ ν (p + 1) (_root_.GlobalTheory.SplitWeil.om μ 1 u (fun y => cut y * Φ y)) := by
    funext x₀
    unfold _root_.GlobalTheory.RootEx.opE
    congr 1
    funext e
    simp only [_root_.GlobalTheory.SplitWeil.om, Units.val_one, Matrix.mul_one, hunip]
    ring
  rw [hmul, hcomm, (_root_.GlobalTheory.RootEx.opE_om_embX k n n' c (p + 1) (by omega) (by omega) ψ ν μ _).1 x,
    hcut_unip, _root_.GlobalTheory.RootEx.opE_om_target_unipotent k n n' c (p + 1) (by omega) (by omega) ψ ν μ _ u huP1]
  funext y
  simp only [_root_.GlobalTheory.SplitWeil.om, Pi.smul_apply, smul_eq_mul]
  ring
