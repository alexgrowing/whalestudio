import Formalism.HermitianCurvature.StatementKB

namespace Formalism.FourierDecayAlt.KB

open Finset Filter Topology NumberField MeasureTheory
open scoped ComplexConjugate

noncomputable section

open Classical

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def NhatV (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ)
    (L : Fin S.f → ℂ) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, hatB S v ε i 1 (w.1 v) (L v) (C.loc (S.σ v) h) (C.loc (S.σ v) h')

def NstV (S : C.HidaSetting E Wp Wq) (ε : ℝ) (i s : ℕ) (w : S.W) (Y : Finset (TB.Pt E)) (κ : TB.Pt E → TB.Pt E → ℂ)
    (t t' : Fin S.f → ℂ) : ℂ :=
  (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, S.gramLoc v ε i (w.1 v) (C.loc (S.σ v) h ++ [(s, t v)])
      (C.loc (S.σ v) h' ++ [(s, t' v)])) / (C.Word.size S.P w.1 : ℂ)

end loc

def WaveV : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq) (X : ℕ → Fin S.f → ℝ),
    (∀ v, WaveLoc S v fun i => X i v) →
    ∀ ε, 0 < ε → ∀ i, 1 ≤ i → i ≤ S.G.r + 1 → ∀ w ∈ S.base.Wall, S.base.cnt w + C.Kst ≤ S.Ntop →
      ∃ θ : Finset (Fin S.f) → S.W → ℝ, (∀ A, TB.IsProb (S.base.Wb (S.base.cnt w + C.Kst)) (θ A)) ∧
        ∀ Y : Finset (TB.Pt E), (∀ h ∈ Y, TB.level h = i - 1) → ∀ κ, TB.PSDOn Y κ →
          ∀ (L : Fin S.f → ℂ) (A : Finset (Fin S.f)),
            (∏ v ∈ A, ‖L v‖ ^ C.Kst) * ‖NhatV S ε i w Y κ L‖ ≤
              (∏ v ∈ A, X i v ^ C.Kst) *
                ∑ w' ∈ S.base.Wb (S.base.cnt w + C.Kst), θ A w' * S.base.N0 ε (i - 1) w' Y κ

def LiftV : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
    (Λ : ℕ → ℕ → Fin S.f → ℝ),
    C.ThmPPos S → (∀ v, LiftLoc S v fun b s => Λ b s v) →
    ∀ ε, 0 < ε → ∀ i s, 1 ≤ s → s ≤ i → i ≤ S.G.r → ∀ w ∈ S.base.Wall, S.base.cnt w + C.Kst ≤ S.Ntop →
      ∃ θ : Finset (Fin S.f) → S.W × S.W → ℝ,
        (∀ A, TB.IsProb (S.base.Wb (S.base.cnt w + C.Kst) ×ˢ S.base.Wb (S.base.cnt w + C.Kst)) (θ A)) ∧
        ∀ (Y : Finset (TB.Pt E)) (κa κw κb : TB.Pt E → TB.Pt E → ℂ),
          (∀ h ∈ Y, TB.level h = i - s) → BlockPSD Y Y κa κw κb →
          ∀ (t t' : Fin S.f → ℂ), (∀ v, t v ≠ 0) → (∀ v, t' v ≠ 0) → ∀ A : Finset (Fin S.f),
            (∏ v ∈ A, ‖(t v)⁻¹ - (t' v)⁻¹‖ ^ C.Kst) * ‖NstV S ε i s w Y κw t t'‖ ≤
              (∏ v ∈ A, Λ (i - s + 1) s v ^ C.Kst) *
                ∑ x ∈ S.base.Wb (S.base.cnt w + C.Kst) ×ˢ S.base.Wb (S.base.cnt w + C.Kst), θ A x *
                  (((NstV S ε i s x.1 Y κa t t).re + (NstV S ε i s x.2 Y κb t' t').re) / 2)

end

end Formalism.FourierDecayAlt.KB
