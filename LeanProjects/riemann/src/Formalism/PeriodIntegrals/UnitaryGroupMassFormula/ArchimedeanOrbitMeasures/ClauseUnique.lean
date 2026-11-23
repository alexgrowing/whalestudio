import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcReal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConst
import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def aVal {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : ℝ :=
  Formalism.MainNotions.S.AutInst.gaugeU X.B.I * Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) *
    Tw u' ^ (-((D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F) : ℕ) : ℤ)) / (X.muH u' Set.univ).toReal

def AprimeInfS : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u' → Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ → Formalism.L2.SG.LocVol.IsStdChar ψ →
    (∀ v, Formalism.MainNotions.S.Gauge.GaugeDens (X.B.I.ε v)) →
    ∀ hT a', 0 < a' → AinfClause X ψ u' hT a' → a' = aVal X u'

def AinfValue : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u' → Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ → Formalism.L2.SG.LocVol.IsStdChar ψ →
    (∀ v, Formalism.MainNotions.S.Gauge.GaugeDens (X.B.I.ε v)) → ∀ hT, AinfClause X ψ u' hT (aVal X u')

def GinfTest : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word),
    Formalism.L2.SG.TypedSets.HypX X hb FdN FdN' u u' →
    ∃ K, MeasurableSet K ∧ 0 < X.measG.μGinf K ∧ X.measG.μGinf K < ⊤

theorem ennreal_volume_ratio_step_cancel {x a b I : ENNReal} (h0 : 0 < x) (h1 : x < ⊤) (ea : x = a * I) (eb : x = b * I) : a = b := by
  have hI0 : I ≠ 0 := by
    intro h; rw [h, mul_zero] at ea; exact h0.ne' ea
  have hIt : I ≠ ⊤ := by
    intro h; rw [h] at ea
    rcases eq_or_ne a 0 with h2 | h2
    · rw [h2, zero_mul] at ea; exact h0.ne' ea
    · rw [ENNReal.mul_top h2] at ea; exact h1.ne ea
  exact (ENNReal.mul_left_inj hI0 hIt).1 (ea.symm.trans eb)

theorem clause_unique {D : D7} (X : HidaSetting D) (ψ : AddChar (AF X.B.I.F) ℂ) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    (K : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) (hK : MeasurableSet K)
    (h0 : 0 < X.measG.μGinf K) (h1 : X.measG.μGinf K < ⊤) (a b : ℝ)
    (ha : AinfClause X ψ u' hT a) (hb : AinfClause X ψ u' hT b) : ENNReal.ofReal a = ENNReal.ofReal b := by
  classical
  obtain ⟨⟨μ, hμ⟩, ha1⟩ := ha
  obtain ⟨⟨ν, hν⟩, ha2⟩ := ha1 μ hμ
  obtain ⟨⟨fib, hfib⟩, ha3⟩ := ha2 ν hν
  have hb3 := ((hb.2 μ hμ).2 ν hν).2 fib hfib
  have ha4 := ha3 fib hfib
  let s : (Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) →
      HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J := fun y =>
    if h : ∃ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      g • ratTup (Ainf X.B.I.F) (tupH (frameOf X u')) = y then h.choose else 1
  have hs : ∀ y, (∃ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      g • ratTup (Ainf X.B.I.F) (tupH (frameOf X u')) = y) →
      s y • ratTup (Ainf X.B.I.F) (tupH (frameOf X u')) = y := by
    intro y hy
    simp only [s, dif_pos hy]
    exact hy.choose_spec
  have hf : Measurable (K.indicator (1 : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → ENNReal)) :=
    measurable_const.indicator hK
  have ea := ha4 _ hf s hs
  have eb := hb3 _ hf s hs
  rw [lintegral_indicator_one hK] at ea eb
  exact ennreal_volume_ratio_step_cancel h0 h1 ea eb

theorem aprimeInfS_of (hV : AinfValue) (hG : GinfTest) : AprimeInfS := by
  intro D X hb FdN FdN' u u' ψ hH hM hS hGD hT a' ha' hAC
  obtain ⟨K, hK, h0, h1⟩ := hG X hb FdN FdN' u u' hH
  have e := clause_unique X ψ u' hT K hK h0 h1 a' (aVal X u') hAC (hV X hb FdN FdN' u u' ψ hH hM hS hGD hT)
  have hpos : 0 < ENNReal.ofReal (aVal X u') := e ▸ ENNReal.ofReal_pos.2 ha'
  exact (ENNReal.ofReal_eq_ofReal_iff ha'.le (ENNReal.ofReal_pos.1 hpos).le).1 e

end PI.AprimeInfW
