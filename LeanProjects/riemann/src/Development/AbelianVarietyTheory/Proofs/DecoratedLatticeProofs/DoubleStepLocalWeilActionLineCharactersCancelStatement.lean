import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepLocalWeilActionLineCharactersCancel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStep_local_weil_action_line_characters_cancel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S)
    (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ))
    (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)),
    (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ →
  ∀ (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (φ : GA D S.B.A → ℂ) (F : GA D S.B'.V → ℂ)
    (a : GL (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) (x : GL (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) (y : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)
    (Φ₁ Φ₁' : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k))
    (Φ₂ Φ₂' : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k)),
    Φ₁'.1 = om Q.μ₁ a x Φ₁.1 → Φ₂'.1 = om Q.μ₂ x y Φ₂.1 →
    S.val c₁ c₂ (S.s₁.om (Q.gl₀ a, Q.gl₁ x) (T₁ Φ₁)) (S.s₂.om (Q.gl₁ x, Q.gl₂ y) (T₂ Φ₂)) φ F 1 1 1 =
      S.val c₁ c₂ (T₁ Φ₁') (T₂ Φ₂') φ F 1 1 1 := by
  first | exact @GlobalTheory.QPl.LineCancel.val_om_loc | exact GlobalTheory.QPl.LineCancel.val_om_loc | (intros; apply GlobalTheory.QPl.LineCancel.val_om_loc <;> assumption)
