import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeTateFromSandwich
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def SqEx3 : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (M : Model l K)
  (d : ℕ), 1 ≤ d → M.Sm → SmoothOfRelativeDimension (d + 1) M.p → ∃ S : Sq M (d + 1), Etale S.D.f

def DiagEt3 : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (M : Model l K)
  (d : ℕ), 1 ≤ d → M.Sm → SmoothOfRelativeDimension (d + 1) M.p → ∀ (S : Sq M (d + 1)), Etale S.D.f → ∀ (r : E.Roots l) (v : S.Y.T 2), IsEtaleFirstChernUntwisted r S.D v →
  ∃ (c : S.P.T (2 + 2 * d)) (w : S.Y.T (2 * d)) (z : S.Y.T (2 + 2 * d))
    (m₀ : ℕ) (a₀ : Fin m₀ → M.T (2 + 2 * d)) (b₀ : Fin m₀ → M.T 0) (ab₀ : Fin m₀ → S.P.T (2 + 2 * d + 0))
    (m : ℕ) (i j : Fin m → ℕ) (hij : ∀ s, i s + j s = 2 + 2 * d) (a : ∀ s, M.T (i s)) (b : ∀ s, M.T (j s))
    (ab : ∀ s, S.P.T (i s + j s)) (one : M.T 0) (N : ℚ_[l]),
    S.Y.CupT v w z ∧ S.Y.toV _ (Model.pullT S.π S.hπ _ c) = S.Y.toV _ z ∧
    (∀ s, S.P.CupT (Model.pullT S.p₁ S.h₁ _ (a₀ s)) (Model.pullT S.p₂ S.h₂ _ (b₀ s)) (ab₀ s)) ∧
    (∀ s, S.P.CupT (Model.pullT S.p₁ S.h₁ _ (a s)) (Model.pullT S.p₂ S.h₂ _ (b s)) (ab s)) ∧ (∀ s, j s ≠ 0) ∧
    S.P.toV _ c = ∑ s, S.P.toV (2 + 2 * d) (ab₀ s) + ∑ s, S.P.toV _ (castT (hij s) (ab s)) ∧
    (∀ k, one.lev k = GlobalTheory.EtC.one (l ^ k) M.spc) ∧ N ≠ 0 ∧
    LinearIndependent ℚ_[l] (fun s => M.toV _ (a₀ s)) ∧ ∑ s, M.toV 0 (b₀ s) = N • M.toV 0 one

theorem diagEt3_of (h : DiagEt2) : DiagEt3 := fun l _ K _ M d hd hM hs S _ => h l K M d hd hM hs S

def OntoOf3 : Prop := CupLaws → Slant → HodgeKill → SqEx3 → DiagEt3 → EtFin → HodgeTateSurjectiveOfTopDegreeInjective

def KillOf3 : Prop := SiteLaws → CupLaws → RelLift → RelInj → RelKill → HodgeKill

end CrystallineSemistableComparison.Onto

end
