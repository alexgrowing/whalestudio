import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GoodLoc

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def EqC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (t₁ t₂ : GT Y u), t₁.lam = t₂.lam → t₁.lam' = t₂.lam' →
    (∃ n ∈ NLam t₁.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₁.lam' (lf D (X.Fu u)), t₂.lin = n * t₁.lin * n') → t₁ = t₂

def GapC : Prop :=
  ∃ Cl₀ : ℝ, ∀ (C' Cl Cg cb Cw cT CT C0 : ℝ) (D : D7) (large₂ : SizeData₂ D), Cl₀ ≤ Cl →
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.ConcreteSettingExists.GapHyp D

def FundC : Prop := ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (t : GT Y u), ∃ K, FundR t K

def PullC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1) (t : GT Y u)
    (μ ν : D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
    (∀ τ, SigmaFinite (μ τ) ∧ IsHaarOn (Rset D.R.k D.R.rS (gamT C t τ)⁻¹) (μ τ) ∧ SigmaFinite (ν τ) ∧
      ν τ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0 ∧
      IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) ((μ τ).map (Formalism.QuantumDeterminants.conjM (gamT C t τ)⁻¹)) (ν τ)) →
    ∃ (μR : Measure X.B.I.Ginf) (νl : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))),
      (∀ v, SigmaFinite (νl v)) ∧ IsHaarOnSet X.B.I (Formalism.L2.SG.TermOp.Vanish.Rset t) μR ∧
      IsQuotMeasS X.B.I μR (Measure.pi νl) ∧ (∀ K, MeasurableSet K → μR K = Measure.pi μ (trI C '' K)) ∧
      ∀ τ, (νl (vOf X τ)).map (Formalism.L2.SG.Pf.LocJEq.Smap C τ (t.pt.1 (vOf X τ))) = ν τ

def TensC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (γ : X.B.I.Ginf)
    (νl : ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))), (∀ v, SigmaFinite (νl v)) →
    ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
              OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) γ)‖ ≤
      ∏ v, Real.sqrt (hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (γ v)))

def ConstC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB →
    covN C Y u ≠ ⊤ → (∀ τ, 0 < cOf hB u τ ∧ sclOf hB u u τ = 1) ∧
      (scl (Y.FN u) (Y.FN u) (X := X) (u := u) (u' := u) * X.volK2) * (∏ τ, cOf hB u τ) * (covN C Y u).toReal ≤ 1

def FactC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB →
    covN C Y u ≠ ⊤ → ∀ (t : GT Y u), t.relevant →
    ∀ (μ ν : D.what₂.Tau → Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) (K : Set X.B.I.Ginf),
    (∀ τ, SigmaFinite (μ τ) ∧ IsHaarOn (Rset D.R.k D.R.rS (gamT C t τ)⁻¹) (μ τ) ∧ SigmaFinite (ν τ) ∧
      ν τ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)} = 0 ∧
      IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) ((μ τ).map (Formalism.QuantumDeterminants.conjM (gamT C t τ)⁻¹)) (ν τ)) → FundR t K →
    ‖(Y.tO u u).vec t‖ * (covN C Y u).toReal ≤ Formalism.L2.SG.TermOp.wt t * ((Measure.pi μ (trI C '' K)).toReal *
      ∏ τ, Real.sqrt (hsNormSq ((locS hB u u τ).J (ν τ) (gamT C t τ))))
end GlobalTheory.TypeAsm
