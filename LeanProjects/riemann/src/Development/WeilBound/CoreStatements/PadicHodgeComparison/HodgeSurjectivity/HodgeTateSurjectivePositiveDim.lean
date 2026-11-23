import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeKill
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsEtaleFirstChernUntwisted

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

structure Sq (M : Model l K) (d : ℕ) where
  P : Model l K
  Y : Model l K
  p₁ : P.X ⟶ M.X
  p₂ : P.X ⟶ M.X
  Δ : M.X ⟶ P.X
  π : Y.X ⟶ P.X
  h₁ : p₁ ≫ M.p = P.p
  h₂ : p₂ ≫ M.p = P.p
  hΔ : Δ ≫ P.p = M.p
  hπ : π ≫ P.p = Y.p
  Δ₁ : Δ ≫ p₁ = 𝟙 _
  Δ₂ : Δ ≫ p₂ = 𝟙 _
  prod : IsPullback p₁ p₂ M.p M.p
  smP : P.Sm
  smY : Y.Sm
  D : E.LineData Y.X
  loc : sSup (𝒱D D) = ⊤
  blow : Nonempty (Blow P.q (Model.genMap Δ hΔ) (Model.genMap π hπ) (genD D) d)

def SqEx : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (M : Model l K)
  (d : ℕ), M.Sm → SmoothOfRelativeDimension (d + 1) M.p → Nonempty (Sq M (d + 1))

def castT {M : Model l K} {i j : ℕ} (h : i = j) (x : M.T i) : M.T j := h ▸ x

def DiagEt : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (M : Model l K)
  (d : ℕ), M.Sm → SmoothOfRelativeDimension (d + 1) M.p → ∀ (S : Sq M (d + 1)) (r : E.Roots l) (v : S.Y.T 2), IsEtaleFirstChernUntwisted r S.D v →
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

def EtFin : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] (M : Model l K),
  M.Sm → ∀ n, FiniteDimensional ℚ_[l] (M.V n)

def Surj (P : HTPre l K) (M : Model l K) (n : ℕ) : Prop :=
  ∀ {m : ℕ → ℕ} (b : ∀ a, Module.Basis (Fin (m a)) K (Hdg M.q a n)) (z : ∀ a, Fin (m a) → ℂ_[l]),
    (∀ v : M.V n, ∑ a ∈ Finset.range (n + 1), ∑ s, z a s * P.h M a n v ((b a).coord s) = 0) → ∀ a ≤ n, z a = 0

def HodgeTateSurjectivePositiveDim : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  (P : HTPre l K) (M : Model l K) (d : ℕ), M.Sm → SmoothOfRelativeDimension (d + 1) M.p → P.Inj M (2 + 2 * d) → ∀ n, Surj P M n

def HodgeTateDimensionEquality : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K]
  (P : HTPre l K) (M : Model l K) (n : ℕ), M.Sm → FiniteDimensional ℚ_[l] (M.V n) → P.Inj M n → Surj P M n →
  Module.finrank ℚ_[l] (M.V n) = ∑ a ∈ Finset.range (n + 1), Module.finrank K (Hdg M.q a n)

def OntoOf : Prop := CupLaws → Slant → HodgeKill → SqEx → DiagEt → EtFin → HodgeTateSurjectivePositiveDim

def KillOf : Prop := CupLaws → RelLift → RelInj → RelKill → HodgeKill

end CrystallineSemistableComparison.Onto

end
