import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ProjRows

noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace

namespace Formalism.L2.SG.RowsDef

open Formalism.MainNotions.S Formalism.L2.SG.ProjRows

section Defs

variable (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)

def HH (Re T : I.L2 μf fund →L[ℂ] I.L2 μf fund) : Submodule ℂ (I.L2 μf fund) :=
  LinearMap.range ((Re.comp T : I.L2 μf fund →L[ℂ] I.L2 μf fund) : I.L2 μf fund →ₗ[ℂ] I.L2 μf fund)

def evAt {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (w₀ : Hs) :
    I.eHom σs μf fund R Re →ₗ[ℂ] I.L2 μf fund :=
  ((ContinuousLinearMap.apply ℂ (I.L2 μf fund) w₀ : (Hs →L[ℂ] I.L2 μf fund) →L[ℂ] I.L2 μf fund) :
      (Hs →L[ℂ] I.L2 μf fund) →ₗ[ℂ] I.L2 μf fund).comp (I.eHom σs μf fund R Re).subtype

end Defs

def RowsProj : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund →
    ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R →
    ∀ (e : I.Gf → ℂ) (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund),
      IsLocallyConstant e → I.convF μf e e = e → (∀ x, e x⁻¹ = star (e x)) →
      I.IsRConvF μf fund R e Re →
    ∀ (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
      (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (dv : InfinitePlace I.F → ℝ) (w : ∀ v, H v),
      (∀ v, IsURepOn (UJset (I.ε v)) (σ v)) → (∀ v, IsFdeg (Formalism.REAL.muG (I.ε v)) (σ v) (dv v)) →
      (∀ v, ‖w v‖ = 1) → (∀ v, Integrable (phLoc (ε := I.ε v) (σ v) (w v) (dv v)) (Formalism.REAL.muG (I.ε v))) →
      ∀ T : I.L2 μf fund →L[ℂ] I.L2 μf fund,
        IsOpInt (muInf I) (fun g => R (g, 1)) (phInf I σ w dv) T →
        Re.comp T = T.comp Re ∧
        I.IsRConv μf fund R (fun g => phInf I σ w dv g.1 * e g.2) (Re.comp T) ∧
        (∀ x y : I.L2 μf fund, ⟪(Re.comp T) x, y⟫_ℂ = ⟪x, (Re.comp T) y⟫_ℂ) ∧
        (Re.comp T).comp (Re.comp T) = Re.comp T

def RowsBij : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund →
    ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R →
    ∀ (e : I.Gf → ℂ) (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRConvF μf fund R e Re →
    ∀ (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
      [∀ v, CompleteSpace (H v)]
      (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (dv : InfinitePlace I.F → ℝ) (w : ∀ v, H v),
      (∀ v, IsURepOn (UJset (I.ε v)) (σ v)) → (∀ v, IsIrredOn (UJset (I.ε v)) (σ v)) →
      (∀ v, IsFdeg (Formalism.REAL.muG (I.ε v)) (σ v) (dv v)) →
      (∀ v, ‖w v‖ = 1) → (∀ v, Integrable (phLoc (ε := I.ε v) (σ v) (w v) (dv v)) (Formalism.REAL.muG (I.ε v))) →
      ∀ T : I.L2 μf fund →L[ℂ] I.L2 μf fund,
        IsOpInt (muInf I) (fun g => R (g, 1)) (phInf I σ w dv) T →
      ∀ (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
        (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs), I.IsHilbTensor σ σs tens →
        Function.Injective (evAt I μf fund σs R Re (tens w)) ∧
          LinearMap.range (evAt I μf fund σs R Re (tens w)) = HH I μf fund Re T

def RowsFinDim : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund →
    ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R →
    ∀ (e : I.Gf → ℂ) (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund),
      IsLocallyConstant e → (∀ x, e x ≠ 0 → x ∈ I.Kset) → I.IsRConvF μf fund R e Re →
    ∀ (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
      [∀ v, CompleteSpace (H v)]
      (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (dv : InfinitePlace I.F → ℝ) (w : ∀ v, H v),
      (∀ v, IsURepOn (UJset (I.ε v)) (σ v)) → (∀ v, IsIrredOn (UJset (I.ε v)) (σ v)) →
      (∀ v, IsFdeg (Formalism.REAL.muG (I.ε v)) (σ v) (dv v)) →
      (∀ v, ‖w v‖ = 1) → (∀ v, Integrable (phLoc (ε := I.ε v) (σ v) (w v) (dv v)) (Formalism.REAL.muG (I.ε v))) →
      ∀ T : I.L2 μf fund →L[ℂ] I.L2 μf fund,
        IsOpInt (muInf I) (fun g => R (g, 1)) (phInf I σ w dv) T →
        FiniteDimensional ℂ (HH I μf fund Re T)

section Count

variable {I : AutInst} {μf : Measure I.Gf} [SigmaFinite μf] {fund : Set I.GA}
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σs : I.Ginf → (Hs →L[ℂ] Hs)} {R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)}
  {Re T : I.L2 μf fund →L[ℂ] I.L2 μf fund} {w₀ : Hs}

def eHomEquivHH (hinj : Function.Injective (evAt I μf fund σs R Re w₀))
    (hran : LinearMap.range (evAt I μf fund σs R Re w₀) = HH I μf fund Re T) :
    I.eHom σs μf fund R Re ≃ₗ[ℂ] HH I μf fund Re T :=
  (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hran)

theorem finrank_HH_eq_Dcount (hinj : Function.Injective (evAt I μf fund σs R Re w₀))
    (hran : LinearMap.range (evAt I μf fund σs R Re w₀) = HH I μf fund Re T) :
    Module.finrank ℂ (HH I μf fund Re T) = I.Dcount σs μf fund R Re :=
  ((eHomEquivHH hinj hran).finrank_eq).symm

theorem rank_HH_eq (hinj : Function.Injective (evAt I μf fund σs R Re w₀))
    (hran : LinearMap.range (evAt I μf fund σs R Re w₀) = HH I μf fund Re T) :
    Module.rank ℂ (HH I μf fund Re T) = Module.rank ℂ (I.eHom σs μf fund R Re) :=
  ((eHomEquivHH hinj hran).rank_eq).symm

theorem finiteDimensional_eHom (hinj : Function.Injective (evAt I μf fund σs R Re w₀))
    (hran : LinearMap.range (evAt I μf fund σs R Re w₀) = HH I μf fund Re T)
    [hfin : FiniteDimensional ℂ (HH I μf fund Re T)] :
    FiniteDimensional ℂ (I.eHom σs μf fund R Re) :=
  LinearEquiv.finiteDimensional (eHomEquivHH hinj hran).symm

theorem Dcount_pos_iff (hinj : Function.Injective (evAt I μf fund σs R Re w₀))
    (hran : LinearMap.range (evAt I μf fund σs R Re w₀) = HH I μf fund Re T)
    [hfin : FiniteDimensional ℂ (HH I μf fund Re T)] :
    0 < I.Dcount σs μf fund R Re ↔ HH I μf fund Re T ≠ ⊥ := by
  rw [← finrank_HH_eq_Dcount hinj hran, Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]

theorem finiteDimensional_HH_of_eHom (hinj : Function.Injective (evAt I μf fund σs R Re w₀))
    (hran : LinearMap.range (evAt I μf fund σs R Re w₀) = HH I μf fund Re T)
    [hfin : FiniteDimensional ℂ (I.eHom σs μf fund R Re)] :
    FiniteDimensional ℂ (HH I μf fund Re T) :=
  LinearEquiv.finiteDimensional (eHomEquivHH hinj hran)

end Count

section Bundle

open Formalism.MainNotions.S

abbrev HHB (B : RowsAut) (T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund) :
    Submodule ℂ (B.I.L2 B.μf B.fund) :=
  HH B.I B.μf B.fund B.Re T

theorem RowsAut.D_eq_finrank_HH (hB : RowsBij) (B : RowsAut) (dv : InfinitePlace B.I.F → ℝ)
    (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v)) (hIrr : ∀ v, IsIrredOn (UJset (B.I.ε v)) (B.σ v))
    (hF : ∀ v, IsFdeg (Formalism.REAL.muG (B.I.ε v)) (B.σ v) (dv v)) (hw : ∀ v, ‖B.w v‖ = 1)
    (hint : ∀ v, Integrable (phLoc (ε := B.I.ε v) (B.σ v) (B.w v) (dv v)) (Formalism.REAL.muG (B.I.ε v)))
    (T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund)
    (hT : IsOpInt (muInf B.I) (fun g => B.R (g, 1)) (phInf B.I B.σ B.w dv) T) :
    B.D = Module.finrank ℂ (HHB B T) ∧
      Nonempty (B.I.eHom B.σs B.μf B.fund B.R B.Re ≃ₗ[ℂ] HHB B T) := by
  obtain ⟨hinj, hran⟩ := hB B.I B.μf B.fund B.fund_spec B.R B.R_spec B.e B.Re B.Re_spec B.H B.σ dv B.w
    hU hIrr hF hw hint T hT B.Hs B.σs B.tens B.tens_spec
  exact ⟨(finrank_HH_eq_Dcount hinj hran).symm, ⟨eHomEquivHH hinj hran⟩⟩

end Bundle

end Formalism.L2.SG.RowsDef
