import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualPickDot
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceStdCharContinuousNontrivialStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NegHalfPointTranslatesLastFrameRowStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaSplitHalfPointMultipliesByCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaConjugateHalfPointTranslatesLastColumnStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfPointNegMultipliesByCharacterStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Generic

variable {p : SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n]
  [Fintype n'] [DecidableEq n'] {α : Frame p S n'} {β : Frame p T n} {LS : Lat S} {LT : Lat T} {f₀ f : WO S T → ℂ}
  {Ψ Ψ' : Matrix n n' k → ℂ}

theorem over_trans (h : Over ψ α β LS LT f₀ Ψ f) {x : WO S T} (hx : IsHalf p.e x) (hΨ' : Ψ' ∈ SB (Matrix n n' k))
    (he : ∀ t, IsHalf p.e t → Ψ' (rd α β t) = Ψ (rd α β (t + x))) : Over ψ α β LS LT f₀ Ψ' (heisO ψ S T x f) := by
  obtain ⟨hS, hT, hV, hΨ, hex, hall⟩ := h
  have hsb := GlobalTheory.FinPl.OverProof.isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ
  have hfun : extFun α β Ψ' = fun t => extFun α β Ψ (t + x) := by
    funext t
    have hc : IsHalf p.e (t + x) ↔ IsHalf p.e t := forall_congr' fun i => forall_congr' fun j => by
      rw [Matrix.add_apply, mul_add, hx i j, add_left_inj]
    unfold extFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht, if_pos (hc.2 ht), he t ht]
    · rw [if_neg ht, if_neg (fun h' => ht (hc.1 h'))]
  refine ⟨hS, hT, hV, hΨ', hex, fun Tm hTm => ?_⟩
  show heisO ψ S T x f = Tm (extFun α β Ψ')
  rw [hall Tm hTm, hfun, hTm.trans _ hsb x hx]

theorem over_modul (h : Over ψ α β LS LT f₀ Ψ f) {y : WO S T} (hy : IsHalf (cA D p.e) y)
    (hΨ' : Ψ' ∈ SB (Matrix n n' k))
    (he : ∀ t, IsHalf p.e t → Ψ' (rd α β t) = ψ (symplO S T t y) * Ψ (rd α β t)) :
    Over ψ α β LS LT f₀ Ψ' (heisO ψ S T y f) := by
  obtain ⟨hS, hT, hV, hΨ, hex, hall⟩ := h
  have hsb := GlobalTheory.FinPl.OverProof.isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ
  have hfun : extFun α β Ψ' = fun t => ψ (symplO S T t y) * extFun α β Ψ t := by
    funext t
    unfold extFun
    by_cases ht : IsHalf p.e t
    · rw [if_pos ht, if_pos ht, he t ht]
    · rw [if_neg ht, if_neg ht, mul_zero]
  refine ⟨hS, hT, hV, hΨ', hex, fun Tm hTm => ?_⟩
  show heisO ψ S T y f = Tm (extFun α β Ψ')
  rw [hall Tm hTm, hfun, hTm.modul _ hsb y hy]

end Generic

section SBLemmas

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem tensCol_mul_mem {Ψ : Matrix n n' k → ℂ} {a g : (n → k) → ℂ} (hg : IsLocallyConstant g)
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) :
    tensCol Ψ (fun y => g y * a y) ∈ SB (Matrix n (n' ⊕ Fin 1) k) := by
  have e : tensCol Ψ (fun y => g y * a y) =
      (fun x : Matrix n (n' ⊕ Fin 1) k => g fun i => x i (Sum.inr 0)) * tensCol Ψ a := by
    funext x; simp only [tensCol, Pi.mul_apply]; ring
  rw [e]
  exact ⟨(hg.comp_continuous (by fun_prop)).mul h.1, h.2.mul_left⟩

theorem tensRow_mul_mem {Ψ : Matrix n' n k → ℂ} {b g : (n → k) → ℂ} (hg : IsLocallyConstant g)
    (h : tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k)) :
    tensRow Ψ (fun y => g y * b y) ∈ SB (Matrix (n' ⊕ Fin 1) n k) := by
  have e : tensRow Ψ (fun y => g y * b y) =
      (fun x : Matrix (n' ⊕ Fin 1) n k => g (x (Sum.inr 0))) * tensRow Ψ b := by
    funext x; simp only [tensRow, Pi.mul_apply]; ring
  rw [e]
  exact ⟨(hg.comp_continuous (by fun_prop)).mul h.1, h.2.mul_left⟩

theorem tensCol_sub_mem {Ψ : Matrix n n' k → ℂ} {a : (n → k) → ℂ} (t : n → k)
    (h : tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) :
    tensCol Ψ (fun y => a (y - t)) ∈ SB (Matrix n (n' ⊕ Fin 1) k) := by
  let M : Matrix n (n' ⊕ Fin 1) k := Matrix.of fun i j => Sum.elim (fun _ => 0) (fun _ => t i) j
  have e : tensCol Ψ (fun y => a (y - t)) = tensCol Ψ a ∘ Homeomorph.subRight M := by
    funext x
    simp only [tensCol, Function.comp_apply, Homeomorph.subRight_apply]
    congr 2
    all_goals first | (ext i j; simp [M]) | (funext i; simp [M])
  rw [e]
  exact ⟨h.1.comp_continuous (Homeomorph.subRight M).continuous, h.2.comp_homeomorph _⟩

theorem tensRow_sub_mem {Ψ : Matrix n' n k → ℂ} {b : (n → k) → ℂ} (t : n → k)
    (h : tensRow Ψ b ∈ SB (Matrix (n' ⊕ Fin 1) n k)) :
    tensRow Ψ (fun y => b (y - t)) ∈ SB (Matrix (n' ⊕ Fin 1) n k) := by
  let M : Matrix (n' ⊕ Fin 1) n k := Matrix.of fun i j => Sum.elim (fun _ => 0) (fun _ => t j) i
  have e : tensRow Ψ (fun y => b (y - t)) = tensRow Ψ b ∘ Homeomorph.subRight M := by
    funext x
    simp only [tensRow, Function.comp_apply, Homeomorph.subRight_apply]
    congr 2
    all_goals first | (ext i j; simp [M]) | (funext i; simp [M])
  rw [e]
  exact ⟨h.1.comp_continuous (Homeomorph.subRight M).continuous, h.2.comp_homeomorph _⟩

end SBLemmas

end GlobalTheory.FinPl.LineAct

end

noncomputable section
namespace GlobalTheory.FinPl.LineAct

theorem line_act : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), p.IsChar ψ χ →
    ∃ ε : k, (ε = 1 ∨ ε = -1) ∧ ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (σ : ℕ) (B : BesLev D (σ + 1)) (B' : BesLev D σ) (W₀ : HSp D) (l : Link B B'.L B'.ζ) (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n) (γ : Frame p B'.A n'') (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)), IsSumFrame B.o B.ζ α α₀ → IsSumFrame B'.o B'.ζ γ γ₀ → IsStdChar D ψ (-1) → ∀ t : n → k,
      (∃ w₀ : WO W₀ B'.L,
        (∀ (L₁ : Lat B.V₀) (L₂ : Lat W₀) (f₁ : WO B.V₀ W₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (Ξ : WO B.V₀ W₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ fun y => (χ (ε * (t ⬝ᵥ y)) : ℂ) * a y) (heisO ψ B.V₀ W₀ ((B.o.resS W₀).symm (0, l.κ W₀ w₀)) Ξ)) ∧
        (∀ (L₂' : Lat W₀) (L₃ : Lat B'.V₀) (f₂ : WO W₀ B'.V₀ → ℂ) (Ψ₂ : Matrix n'' n k → ℂ) (b : (n → k) → ℂ) (Ξ : WO W₀ B'.V₀ → ℂ),
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ fun η => b (η - t)) (heisO ψ W₀ B'.V₀ ((B'.o.resT W₀).symm (0, -w₀)) Ξ))) ∧
      (∃ w₀ : WO W₀ B'.L,
        (∀ (L₁ : Lat B.V₀) (L₂ : Lat W₀) (f₁ : WO B.V₀ W₀ → ℂ) (Ψ₁ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (Ξ : WO B.V₀ W₀ → ℂ),
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ a) Ξ →
          Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ₁ fun y => a (y - t)) (heisO ψ B.V₀ W₀ ((B.o.resS W₀).symm (0, l.κ W₀ w₀)) Ξ)) ∧
        (∀ (L₂' : Lat W₀) (L₃ : Lat B'.V₀) (f₂ : WO W₀ B'.V₀ → ℂ) (Ψ₂ : Matrix n'' n k → ℂ) (b : (n → k) → ℂ) (Ξ : WO W₀ B'.V₀ → ℂ),
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ b) Ξ →
          Over ψ β γ₀ L₂' L₃ f₂ (tensRow Ψ₂ fun η => (χ (ε * (η ⬝ᵥ t)) : ℂ) * b η) (heisO ψ W₀ B'.V₀ ((B'.o.resT W₀).symm (0, -w₀)) Ξ))) := by
  intro D k _ _ _ _ p ψ χ hχ
  refine ⟨-1, Or.inr rfl, ?_⟩
  intro n n' n'' _ _ _ _ _ _ σ B B' W₀ l α α₀ β γ γ₀ hα hγ hstd t
  have hχc := (GlobalTheory.T.splitPlace_stdChar_continuous_nontrivial D k p ψ χ hχ hstd).1
  have hχl := GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar χ hχc
  have hlc : IsLocallyConstant fun y : n → k => (χ (-1 * (t ⬝ᵥ y)) : ℂ) :=
    hχl.comp_continuous (continuous_const.mul (continuous_const.dotProduct continuous_id))
  have hlc' : IsLocallyConstant fun η : n → k => (χ (-1 * (η ⬝ᵥ t)) : ℂ) :=
    hχl.comp_continuous (continuous_const.mul (continuous_id.dotProduct continuous_const))
  constructor
  · obtain ⟨h1h, h1m⟩ := GlobalTheory.T.kappa_splitHalfPoint_multiplies_by_character D k p ψ χ hχ n n' (σ + 1) B B'.L W₀ B'.ζ l α α₀ β hα t
    obtain ⟨h1ah, h1ar⟩ := GlobalTheory.T.neg_halfPoint_translates_lastFrameRow D k p n n'' B'.V₀ B'.A B'.L W₀ B'.o B'.ζ β γ γ₀ hγ t
    refine ⟨wRow p B'.ζ β t, fun L₁ L₂ f₁ Ψ₁ a Ξ h => ?_, fun L₂' L₃ f₂ Ψ₂ b Ξ h => ?_⟩
    · refine over_modul h h1h (tensCol_mul_mem hlc h.2.2.2.1) fun x hx => ?_
      rw [h1m x hx]
      simp only [tensCol, neg_one_mul]
      ring
    · refine over_trans h h1ah (tensRow_sub_mem t h.2.2.2.1) fun x hx => ?_
      simp only [tensRow, GlobalTheory.FinPl.OverProof.rd_add]
      congr 1
      · congr 1; ext i j; simp [Matrix.add_apply, h1ar]
      · congr 1; funext j; simp [Matrix.add_apply, h1ar, sub_eq_add_neg]
  · obtain ⟨h2h, h2r⟩ := GlobalTheory.T.kappa_conjugateHalfPoint_translates_lastColumn D k p n n' (σ + 1) B B'.L W₀ B'.ζ l B'.line α α₀ β hα t
    obtain ⟨h2bh, h2bm⟩ := GlobalTheory.T.conjugateHalfPoint_neg_multiplies_by_character D k p ψ χ hχ n n'' B'.V₀ B'.A B'.L W₀ B'.o B'.ζ B'.line β γ γ₀ hγ t
    refine ⟨wCol p B'.ζ β t, fun L₁ L₂ f₁ Ψ₁ a Ξ h => ?_, fun L₂' L₃ f₂ Ψ₂ b Ξ h => ?_⟩
    · refine over_trans h h2h (tensCol_sub_mem t h.2.2.2.1) fun x hx => ?_
      simp only [tensCol, GlobalTheory.FinPl.OverProof.rd_add]
      congr 1
      · congr 1; ext i j; simp [Matrix.add_apply, h2r]
      · congr 1; funext i; simp [Matrix.add_apply, h2r, sub_eq_add_neg]
    · refine over_modul h h2bh (tensRow_mul_mem hlc' h.2.2.2.1) fun x hx => ?_
      rw [h2bm x hx]
      simp only [tensRow, neg_one_mul]
      ring
end GlobalTheory.FinPl.LineAct
end
