import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def PeriodsOnLine (ch : Choice R) : Prop :=
  ∃ ell : PolCol ch.G × PolRow ch.G → ℂ, ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
    IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
      ∃ κ : ℂ, ∀ P, defPer t ch.S.toGridChoice M P d (colFn ch a) (formTop ch t y) = κ * ell P

def RealLine (ch : Choice R) : Prop :=
  ∃ ell : PolCol ch.G × PolRow ch.G → ℂ, ell ≠ 0 ∧
    (∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G, IsTermVol t ch.S.toGridChoice (ch.Phi a) β M →
      ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ y, ∃ K : ℂ, ∀ σ : PolCol ch.G × PolRow ch.G →₀ ℂ,
        defTot t ch.S.toGridChoice M σ τ (colFn ch a) (formTop ch t y) = (σ.sum fun P c => c * ell P) * K) ∧
    ∀ z : ℂ, ∃ σ : PolCol ch.G × PolRow ch.G →₀ ℂ, (z = 0 → σ = 0) ∧ (σ.sum fun P c => c * ell P) = z

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem sum_sum_line {P D' : Type} (σ : P →₀ ℂ) (τ : D' →₀ ℂ) (f : P → D' → ℂ) (ell : P → ℂ)
    (κ : D' → ℂ) (h : ∀ d ∈ τ.support, ∀ p, f p d = κ d * ell p) :
    (σ.sum fun p c => τ.sum fun d c' => c * c' * f p d) =
      (σ.sum fun p c => c * ell p) * τ.sum fun d c' => c' * κ d := by
  rw [Finsupp.sum_mul]
  refine Finsupp.sum_congr fun p _ => ?_
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun d hd => ?_
  rw [h d hd p]
  ring

theorem realLine_of_periodsOnLine (ch : Choice R) (h : PeriodsOnLine ch) : RealLine ch := by
  obtain ⟨ell₀, h₀⟩ := h
  classical
  let ell : PolCol ch.G × PolRow ch.G → ℂ := if ell₀ = 0 then fun _ => 1 else ell₀
  have hne : ell ≠ 0 := by
    by_cases e : ell₀ = 0
    · simp only [ell, e, if_true]
      intro h1
      have := congrFun h1 (Classical.arbitrary _)
      simp at this
    · simpa [ell, e] using e
  have hline : ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
        ∃ κ : ℂ, ∀ P, defPer t ch.S.toGridChoice M P d (colFn ch a) (formTop ch t y) = κ * ell P := by
    intro t a hS β hβ M hM τ hτ d hd y
    obtain ⟨κ, hκ⟩ := h₀ t a hS β hβ M hM τ hτ d hd y
    by_cases e : ell₀ = 0
    · refine ⟨0, fun P => ?_⟩
      rw [hκ P, e]
      simp
    · exact ⟨κ, fun P => by simp only [ell, e, if_false]; exact hκ P⟩
  refine ⟨ell, hne, fun t a hS β hβ M hM τ hτ y => ?_, fun z => ?_⟩
  · choose κ hκ using hline t a hS β hβ M hM τ hτ
    let κ' : PureDat ch.G t → ℂ := fun d => if hd : d ∈ τ.support then κ d hd y else 0
    refine ⟨τ.sum fun d c' => c' * κ' d, fun σ => ?_⟩
    refine sum_sum_line σ τ _ ell κ' fun d hd P => ?_
    simp only [κ', dif_pos hd]
    exact hκ d hd y P
  · obtain ⟨P₀, hP₀⟩ := Function.ne_iff.1 hne
    refine ⟨Finsupp.single P₀ (z / ell P₀), fun hz => by simp [hz], ?_⟩
    rw [Finsupp.sum_single_index (zero_mul _)]
    exact div_mul_cancel₀ z hP₀

theorem big_mono {Q Q' : ChP} (h : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), Q ch → Q' ch) (hQ : Big Q) : Big Q' := by
  obtain ⟨CF0, hC⟩ := hQ
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hC ε CF hCF
  exact ⟨x₀, fun D large₂ he hx' Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => h ch (hx D large₂ he hx' Γ Pl0 T A Ks R F hS ch hch hsc)⟩

end GlobalTheory.RowReal
