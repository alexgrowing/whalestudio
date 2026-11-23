import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeTateSurjectivePositiveDim

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def SqEx2 : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (M : Model l K)
  (d : ℕ), 1 ≤ d → M.Sm → SmoothOfRelativeDimension (d + 1) M.p → Nonempty (Sq M (d + 1))

def DiagEt2 : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (M : Model l K)
  (d : ℕ), 1 ≤ d → M.Sm → SmoothOfRelativeDimension (d + 1) M.p → ∀ (S : Sq M (d + 1)) (r : E.Roots l) (v : S.Y.T 2), IsEtaleFirstChernUntwisted r S.D v →
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

def HodgeTateSurjectiveOfTopDegreeInjective : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  (P : HTPre l K) (M : Model l K) (d : ℕ), 1 ≤ d → M.Sm → SmoothOfRelativeDimension (d + 1) M.p → P.Inj M (2 + 2 * d) → ∀ n, Surj P M n

def Retract : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  (M : Model l K) (d : ℕ), M.Sm → SmoothOfRelativeDimension d M.p → ∃ (N : Model l K) (p : N.X ⟶ M.X) (s : M.X ⟶ N.X),
    p ≫ M.p = N.p ∧ s ≫ p = 𝟙 _ ∧ N.Sm ∧ SmoothOfRelativeDimension (d + 1 + 1) N.p

def OntoAll : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  (P : HTPre l K), (∀ M : Model l K, M.Sm → ∀ n, P.Inj M n) → ∀ (M : Model l K) (d : ℕ), M.Sm →
    SmoothOfRelativeDimension d M.p → ∀ n, Surj P M n

def OntoOf2 : Prop := CupLaws → Slant → HodgeKill → SqEx2 → DiagEt2 → EtFin → HodgeTateSurjectiveOfTopDegreeInjective

def OntoLow : Prop := CupLaws → Retract → HodgeTateSurjectiveOfTopDegreeInjective → OntoAll

end CrystallineSemistableComparison.Onto

end
