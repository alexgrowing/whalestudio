import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.BridgeC

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Metric NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal Formalism.MainNotions.S Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

def reimV {V : Type} {n m : ℕ} (M : V → Matrix (Fin n) (Fin m) ℂ) : EuclideanSpace ℝ (V × Fin n × Fin m × Bool) :=
  (WithLp.equiv 2 (V × Fin n × Fin m × Bool → ℝ)).symm fun p =>
    if p.2.2.2 then (M p.1 p.2.1 p.2.2.1).re else (M p.1 p.2.1 p.2.2.1).im

def BetaIso : Prop := ∀ {D : D7} (X : HidaSetting D),
    ∃ Bc : EuclideanSpace ℝ (KapI X) ≃L[ℝ]
        EuclideanSpace ℝ (InfinitePlace X.B.I.F × Fin X.B.I.n × Fin (D.R.rS + 1 + D.R.rS) × Bool),
      ∀ Y : TupI X, Bc (tupCoord X Y) = reimV (fun v => betaV X v Y)

def MuBridge : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    μinf.map (fun Y => reimV (fun v => betaV X v Y)) =
      ENNReal.ofReal (2 ^ (X.B.I.n * (D.R.rS + 1 + D.R.rS) * Fintype.card (InfinitePlace X.B.I.F))) • volume

def NuBridge : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∃ (κ : Type) (_ : Fintype κ) (Hh : EuclideanSpace ℝ κ →ₗ[ℝ]
        (InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ))
      (Tc : HmI X ≃ₜ EuclideanSpace ℝ κ),
      (∀ s v, (Hh s v)ᴴ = Hh s v) ∧ (∀ s, ∑ v, ∑ i, ∑ j, ‖Hh s v i j‖ ^ 2 = ‖s‖ ^ 2) ∧
      (∀ M : InfinitePlace X.B.I.F → Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) ℂ,
        (∀ v, (M v)ᴴ = M v) → ∃ s, Hh s = M) ∧
      (∀ S T, Tc (S + T) = Tc S + Tc T) ∧
      (∀ S v, Hh (Tc S) v = (S : Matrix _ _ _).map (PI.AprimeInfU.thetaInf X v)) ∧
      νinf.map Tc = volume

def DKForm : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)) {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (NumberField.InfinitePlace X.B.I.F → Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)),
    StdConj X hb u' c S → LieCompl X S L →
    ∀ x v, betaV X v ((tupCoord X).symm (fderiv ℝ (KapOrb X u' (kap0 X hb c L)) 0 x)) =
      uMat (c v) * L x v * uMat (c v)⁻¹ * betaV X v (Y0 X u')

def RowsZ : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (c : X.B.I.Ginf)
    (S : NumberField.InfinitePlace X.B.I.F → Finset (Fin X.B.I.n)), StdConj X hb u' c S →
    ∀ v, ∀ i ∈ S v, ∀ b, (uMat (c v)⁻¹ * betaV X v (Y0 X u')) i b = 0

def DetT : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf
    fibInf, PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ v : InfinitePlace X.B.I.F, ‖X.B.I.φ v (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det‖ = Tw u'

def PlaceJacAll : Prop := ∀ (V : Type) [Fintype V] (n m : ℕ) (ε : V → Fin n → Bool) (S : V → Finset (Fin n))
    (w : V → Matrix (Fin n) (Fin m) ℂ) (c : V → Matrix (Fin n) (Fin n) ℂ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin n) (Fin n) ℂ))
    (H : EuclideanSpace ℝ κ →ₗ[ℝ] (V → Matrix (Fin m) (Fin m) ℂ)),
    (∀ v, n = m + (S v).card) → (∀ v, ∀ i ∈ S v, ∀ b, w v i b = 0) →
    (∀ v, ((w v)ᴴ * Formalism.REAL.Jm (ε v) * w v).det ≠ 0) →
    (∀ v, (c v)ᴴ * Formalism.REAL.Jm (ε v) * c v = Formalism.REAL.Jm (ε v)) →
    (∀ x v, (L x v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * L x v = 0 ∧ ∀ i ∈ S v, ∀ j ∈ S v, L x v i j = 0) →
    (∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2) →
    (∀ M : V → Matrix (Fin n) (Fin n) ℂ, (∀ v, (M v)ᴴ * Formalism.REAL.Jm (ε v) + Formalism.REAL.Jm (ε v) * M v = 0 ∧
      ∀ i ∈ S v, ∀ j ∈ S v, M v i j = 0) → ∃ x, L x = M) →
    (∀ t v, (H t v)ᴴ = H t v) → (∀ t, ∑ v, ∑ i, ∑ j, ‖H t v i j‖ ^ 2 = ‖t‖ ^ 2) →
    (∀ M : V → Matrix (Fin m) (Fin m) ℂ, (∀ v, (M v)ᴴ = M v) → ∃ t, H t = M) →
    ∃ Fe : (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) ≃L[ℝ] EuclideanSpace ℝ (V × Fin n × Fin m × Bool),
      (∀ z, Fe z = reimV (fun v => c v * (L z.1 v * w v +
        (1 / 2 : ℂ) • (w v * ((w v)ᴴ * Formalism.REAL.Jm (ε v) * w v)⁻¹ * H z.2 v)))) ∧
      (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ)).map Fe =
        ENNReal.ofReal (∏ v, 2 ^ (n * m) / ‖((w v)ᴴ * Formalism.REAL.Jm (ε v) * w v).det‖ ^ (S v).card) • volume

end PI.AprimeInfW
