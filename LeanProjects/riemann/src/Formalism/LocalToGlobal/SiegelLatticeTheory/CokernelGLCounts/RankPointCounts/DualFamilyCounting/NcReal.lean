import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSplit

noncomputable section

namespace Formalism.L2.SG.Pf.NcReal

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.AdBridge
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D)

def AinfClause (ψ : AddChar (AF X.B.I.F) ℂ) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) (a' : ℝ) : Prop :=
  AllSome (SdW X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS))
    fun μinf =>
  AllSome (SdHerm X.B.I.F X.B.I.E X.B.I.cm.sig (Ainf X.B.I.F) (psiInf X.B.I.F ψ) (D.R.rS + 1 + D.R.rS)) fun νinf =>
  AllSome (fun fibInf : HermR (Ainf X.B.I.F) X.B.I.cm.sig (D.R.rS + 1 + D.R.rS) →
        Measure (Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) =>
      IsFibreFamily μinf (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) Subtype.val
        {Y | LinearIndependent (Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) Y} νinf Set.univ fibInf) fun fibInf =>
  ∀ f : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → ENNReal, Measurable f →
    ∀ s : (Fin (D.R.rS + 1 + D.R.rS) → Fin X.B.I.n → Ainf X.B.I.F ⊗[X.B.I.F] X.B.I.E) → HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J,
      (∀ y, (∃ g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J, g • ratTup (Ainf X.B.I.F) (tupH (frameOf X u')) = y) →
        s y • ratTup (Ainf X.B.I.F) (tupH (frameOf X u')) = y) →
      ∫⁻ g, f g ∂X.measG.μGinf = ENNReal.ofReal a' *
        ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∂(X.measW u').μHinf
          ∂(fibInf (hermOf (Ainf X.B.I.F) X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))) hT))

def eDF (k r : ℕ) : ℝ := -((8 * (r : ℝ) ^ 3 + 6 * (r : ℝ) ^ 2 + 6 * (k : ℝ) * (r : ℝ) ^ 2 + (r : ℝ)) / 3)

def RealBracket : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
    (ψ : AddChar (AF X.B.I.F) ℂ),
    HypX X hb FdN FdN' u u' → Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ → IsStdChar ψ →
    ∀ (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
        gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) (a' : ℝ), 0 < a' → AinfClause X ψ u' hT a' →
    Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (X.muH u Set.univ).toReal * (X.muN u FdN).toReal * (X.muN u' FdN').toReal =
      a' * 2 ^ (D.R.k * Fintype.card (InfinitePlace X.B.I.F)) *
        (Real.pi ^ D.R.k / ((D.R.k - 1).factorial : ℝ)) ^ Fintype.card (InfinitePlace X.B.I.F) *
        Formalism.L2.SG.RealObj.Tw u ^ (-((D.R.k * Fintype.card (InfinitePlace X.B.I.F) : ℕ) : ℤ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^ eDF D.R.k D.R.rS

end Formalism.L2.SG.Pf.NcReal
