import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ClauseUnique

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def KVal {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : ℝ :=
  Formalism.MainNotions.S.AutInst.gaugeU X.B.I * Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) *
    Tw u' ^ (-((D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F) : ℕ) : ℤ))

theorem aVal_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) :
    aVal X u' = KVal X u' / (X.muH u' Set.univ).toReal := rfl

def orbM {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :
    Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E :=
  g • ratTup (Ainf X.B.I.F) (tupH (frameOf X u'))

def ExInf : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u' → Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ → Formalism.L2.SG.LocVol.IsStdChar ψ →
  AllSome (SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS))
    fun μinf =>
  AllSome (SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS)) fun νinf =>
  ∃ fibInf : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) →
        Measure (Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E),
      IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val
        {Y | LinearIndependent (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) Y} νinf Set.univ fibInf

def PushInf : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u' → Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ → Formalism.L2.SG.LocVol.IsStdChar ψ →
    (∀ v, Formalism.MainNotions.S.Gauge.GaugeDens (X.B.I.ε v)) →
    ∀ (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) μinf νinf fibInf,
    SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS) μinf →
    SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS) νinf →
    IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val
        {Y | LinearIndependent (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) Y} νinf Set.univ fibInf →
    X.measG.μGinf.map (orbM X u') =
      ENNReal.ofReal (KVal X u') • fibInf (hermOf (Ainf X.B.I.F) X.B.I.cm.sig
        (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))) hT)

def WeilInf : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u' →
    ∀ f : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → ENNReal, Measurable f →
    ∀ s : (Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      (∀ y, (∃ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, g • ratTup (Ainf X.B.I.F) (tupH (frameOf X u')) = y) →
        s y • ratTup (Ainf X.B.I.F) (tupH (frameOf X u')) = y) →
      ∫⁻ g, f g ∂X.measG.μGinf = ((X.measW u').μHinf Set.univ)⁻¹ *
        ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∂(X.measW u').μHinf
          ∂(X.measG.μGinf.map (orbM X u'))

def HtotInf : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u' →
    (X.measW u').μHinf Set.univ = X.muH u' Set.univ ∧ 0 < X.muH u' Set.univ ∧ X.muH u' Set.univ < ⊤

theorem ainfValue_of (hE : ExInf) (hP : PushInf) (hW : WeilInf) (hH : HtotInf) : AinfValue := by
  intro D X hb FdN FdN' u u' ψ hX hM hS hG hT
  obtain ⟨e1, e2, e3⟩ := hH X hb FdN FdN' u u' hX
  have ex := hE X hb FdN FdN' u u' ψ hX hM hS
  refine ⟨ex.1, fun μ hμ => ⟨(ex.2 μ hμ).1, fun ν hν => ⟨(ex.2 μ hμ).2 ν hν, fun fib hfib f hf s hs => ?_⟩⟩⟩
  rw [hW X hb FdN FdN' u u' hX f hf s hs, hP X hb FdN FdN' u u' ψ hX hM hS hG hT μ ν fib hμ hν hfib,
    lintegral_smul_measure, e1, aVal_eq]
  have ht : 0 < (X.muH u' Set.univ).toReal := ENNReal.toReal_pos e2.ne' e3.ne
  rw [ENNReal.ofReal_div_of_pos ht, ENNReal.ofReal_toReal e3.ne, div_eq_mul_inv]
  ring

end PI.AprimeInfW
