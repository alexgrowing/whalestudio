import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.AinfValueOf

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

abbrev TupI {D : D7} (X : HidaSetting D) : Type :=
  Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E

def IndI {D : D7} (X : HidaSetting D) : Set (TupI X) :=
  {Y | LinearIndependent (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) Y}

def PushHyp {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (μinf : Measure (TupI X)) (νinf : Measure (HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS)))
    (fibInf : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) → Measure (TupI X)) : Prop :=
  (∃ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf) (u : D.what₂.Word),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u') ∧ Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧
    Formalism.L2.SG.LocVol.IsStdChar ψ ∧ (∀ v, Formalism.MainNotions.S.Gauge.GaugeDens (X.B.I.ε v)) ∧
    SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS) μinf ∧
    SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS) νinf ∧
    IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val (IndI X) νinf Set.univ fibInf

def TI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) :
    HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) :=
  hermOf (Ainf X.B.I.F) X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))) hT

def FbI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) : Set (TupI X) :=
  gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J ⁻¹' {((TI X u' hT : HermR _ _ _) : Matrix _ _ _)} ∩ IndI X

def InvI {D : D7} (X : HidaSetting D) (ν : Measure (TupI X)) : Prop :=
  ∀ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, ν.map (fun y => g • y) = ν

def LFI {D : D7} (X : HidaSetting D) (ν : Measure (TupI X)) : Prop :=
  ∀ K : Set (TupI X), IsCompact K → K ⊆ IndI X → ν K < ⊤

def InvPush : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    InvI X (X.measG.μGinf.map (orbM X u'))

def InvFib : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    InvI X (fibInf (TI X u' hT))

def LFPush : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    X.measG.μGinf.map (orbM X u') (FbI X u' hT)ᶜ = 0 ∧ LFI X (X.measG.μGinf.map (orbM X u'))

def LFFib : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    LFI X (fibInf (TI X u' hT))

def OrbUniq : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ ν₁ ν₂ : Measure (TupI X), InvI X ν₁ → InvI X ν₂ → ν₁ (FbI X u' hT)ᶜ = 0 → ν₂ (FbI X u' hT)ᶜ = 0 →
      LFI X ν₁ → LFI X ν₂ → ν₂ ≠ 0 → ∃ c : ENNReal, ν₁ = c • ν₂

def ConstTest : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∃ φ : TupI X → ENNReal, Measurable φ ∧ 0 < ∫⁻ y, φ y ∂(fibInf (TI X u' hT)) ∧
      ∫⁻ y, φ y ∂(fibInf (TI X u' hT)) < ⊤ ∧
      ∫⁻ y, φ y ∂(X.measG.μGinf.map (orbM X u')) = ENNReal.ofReal (KVal X u') * ∫⁻ y, φ y ∂(fibInf (TI X u' hT))

theorem pushInf_of (h1 : InvPush) (h2 : InvFib) (h3 : LFPush) (h4 : LFFib) (h5 : OrbUniq) (h6 : ConstTest) :
    PushInf := by
  intro D X hb FdN FdN' u u' ψ hX hM hS hG hT μinf νinf fibInf hμ hν hfib
  have hP : PushHyp X u' ψ hT μinf νinf fibInf := ⟨⟨hb, FdN, FdN', u, hX⟩, hM, hS, hG, hμ, hν, hfib⟩
  obtain ⟨φ, hφ, hp, hf, he⟩ := h6 X u' ψ hT μinf νinf fibInf hP
  have hsupp : fibInf (TI X u' hT) (FbI X u' hT)ᶜ = 0 := hfib.1 _
  have hne : fibInf (TI X u' hT) ≠ 0 := by
    intro h; rw [h, lintegral_zero_measure] at hp; exact lt_irrefl _ hp
  obtain ⟨c, hc⟩ := h5 X u' ψ hT μinf νinf fibInf hP _ _ (h1 X u' ψ hT μinf νinf fibInf hP)
    (h2 X u' ψ hT μinf νinf fibInf hP) (h3 X u' ψ hT μinf νinf fibInf hP).1 hsupp
    (h3 X u' ψ hT μinf νinf fibInf hP).2 (h4 X u' ψ hT μinf νinf fibInf hP) hne
  have e2 : ∫⁻ y, φ y ∂(X.measG.μGinf.map (orbM X u')) = c * ∫⁻ y, φ y ∂(fibInf (TI X u' hT)) := by
    rw [hc, lintegral_smul_measure, smul_eq_mul]
  have hcK : c = ENNReal.ofReal (KVal X u') :=
    (ENNReal.mul_left_inj hp.ne' hf.ne).1 (e2.symm.trans he)
  rw [hc, hcK]
  rfl

end PI.AprimeInfW
