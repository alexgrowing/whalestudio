import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped InnerProductSpace ENNReal NNReal
open Matrix

set_option linter.dupNamespace false

namespace Formalism.L2.SG.WuDecay

def opn {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) M‖

variable {D : D7} (X : HidaSetting D)

def normInf (g : X.B.I.Ginf) : ℝ := ∏ v, opn (uMat (g v))

def nuInf (u : D.what₂.Word) (x : X.B.I.Ginf) : ℝ := ⨅ t : X.SinfU u, normInf X ((t : X.B.I.Ginf) * x)

def N1 : ℝ :=
  4 * (X.B.I.n : ℝ) ^ 2 * Real.sqrt (2 * ((Finset.univ.sup fun v => X.B.I.qAt v : ℕ) : ℝ))

def WuReprod (u : D.what₂.Word) : Prop :=
  ∃ (α : X.B.I.Ginf → ℂ) (Ωi : Set X.B.I.Ginf) (a : ℝ≥0), IsCompact Ωi ∧ (1 : X.B.I.Ginf) ∈ Ωi ∧
    Measurable α ∧ (∀ z, α z ≠ 0 → z ∈ Ωi) ∧ (∀ z, ‖α z‖ ≤ a) ∧
    ∀ x, Integrable (fun z => α z • X.Wu u (x * z)) (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
      ∫ z, α z • X.Wu u (x * z) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = X.Wu u x

def WuWeighted (u : D.what₂.Word) : Prop :=
  ∫⁻ x, ‖X.Wu u x‖ₑ * ENNReal.ofReal (nuInf X u x ^ N1 X) ∂(X.nuQ u) < ⊤

def WuDecay : Prop := ∀ u : D.what₂.Word, WuReprod X u ∧ WuWeighted X u

def FoldOK (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) : Prop :=
  (∃ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf)) ∧
  ∃ (Ω₀ : Set X.B.I.GA) (a : ℝ≥0), IsCompact Ω₀ ∧ (1 : X.B.I.GA) ∈ Ω₀ ∧ ∀ T : Cu X u hK,
    (∀ Ω : Set X.B.I.GA, IsCompact Ω → Ω₀ ⊆ Ω →
      Formalism.L2.SG.PoincareSeriesSquareIntegrable.IsFoldDatum (X.B.I.muA X.B.μf) (Srat X u) Ω a (Ph X u hK T)) ∧
    ∀ Ω : Set X.B.I.GA, IsCompact Ω → ∀ Fs : Set X.B.I.GA,
      IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) →
        Formalism.L2.SG.PoincareSeriesSquareIntegrable.multiplicityLIntegral (X.B.I.muA X.B.μf) (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) Ω Fs (Ph X u hK T) < ⊤

end Formalism.L2.SG.WuDecay
