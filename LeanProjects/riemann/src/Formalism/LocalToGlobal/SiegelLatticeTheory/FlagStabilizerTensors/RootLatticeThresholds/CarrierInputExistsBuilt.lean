import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def instCMT2 (D : D7) : IsCMField D.host.E := D.host.isCMField_hostE

attribute [local instance] instCMT2

section hermitianSpaces

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem isBuilt_of_builtPlace {Cb Cc : ℝ} {S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq}
    {p : ∀ v, Formalism.FourierDecayAlt.KB.Pl (Formalism.FourierDecayAlt.D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}
    (h : Formalism.FourierDecayAlt.KB.IsLeadingFormPlace Cb Cc S p f χ A₀) :
    Formalism.FourierDecayAlt.D.IsBuilt S (Formalism.FourierDecayAlt.KB.plT S p) f χ (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p)
      (Formalism.FourierDecayAlt.KB.plTop S p) A₀ := by
  obtain ⟨⟨-, -, -, hχ, -, -, -, -, -, -, -, -, -, -, -, hv⟩, hE, -⟩ := h
  exact ⟨hχ, fun v => ⟨(hv v).2.2.1, (p v).hT, (p v).hF, (p v).hP, (hv v).2.2.2.2, hE v⟩⟩

end hermitianSpaces

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def CarrierDataBound (u u' : D.what₂.Word) (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (FdN FdN' : Set X.B.I.Ginf) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (jn CA : ℝ)
    (G0 : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)) (de de' : ℕ → ℝ) (l : ℕ) (C₆ Cc Cb : ℝ) : Prop :=
  ∃ (Wp Wq : InfinitePlace D.host.E → Type) (_ : ∀ x, NormedAddCommGroup (Wp x)) (_ : ∀ x, InnerProductSpace ℂ (Wp x))
    (_ : ∀ x, NormedAddCommGroup (Wq x)) (_ : ∀ x, InnerProductSpace ℂ (Wq x)) (_ : ∀ x, FiniteDimensional ℂ (Wp x))
    (_ : ∀ x, FiniteDimensional ℂ (Wq x))
    (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq)
    (p : ∀ v, Formalism.FourierDecayAlt.KB.Pl (Formalism.FourierDecayAlt.D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ j : Fin S.f, Formalism.FourierDecayAlt.B.Mat S.G.k S.G.r → (Wq (S.pl j) →L[ℂ] Wp (S.pl j))) (χ : ℝ → ℝ)
    (A₀ : ℝ) (c : Formalism.FourierDecayAlt.LE.Cut)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * S.G.r + S.G.k + 1)) ℂ)
    (Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin X.B.I.n) ℂ)
    (eP : ∀ v, Wp (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v) (eQ : ∀ v, Wq (S.pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v),
    S.CA = CA ∧ S.G = G0 ∧ S.de = de ∧ S.de' = de' ∧ S.l = l ∧ Formalism.L2.SG.DataInst.Compat S u u' ∧
    Formalism.FourierDecayAlt.KB.IsLeadingFormPlace Cb Cc S p f χ A₀ ∧ Formalism.FourierDecayAlt.JCT.SliceBudget S A₀ ∧ c.χ = χ ∧
    (∀ v, C₆ * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2) ≤
      S.cutHi v - S.cutLo v) ∧
    Formalism.FourierDecayAlt.JCT.VtTensor S (Formalism.FourierDecayAlt.KB.plT S p) f (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p)
      (VtPt X u u' sc i0 i0' FdN FdN' νq) ∧
    BuiltFromX X S u u' (Formalism.FourierDecayAlt.KB.plT S p) f τ Q Qi eP eQ ∧
    BaseFromX X S u u' i0 i0' τ Q Qi (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p) ∧
    TopTie X S u u' sc i0 i0' FdN FdN' νq τ ∧
    VJoint X S u u' sc i0 i0' νq (Formalism.FourierDecayAlt.KB.plT S p) f (Formalism.FourierDecayAlt.KB.plν S p) (Formalism.FourierDecayAlt.KB.plm S p) τ eP eQ ∧
    ∀ (L : ∀ v : Fin S.f, Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.MA.A (Formalism.FourierDecayAlt.D.parOf S v)
        (Formalism.FourierDecayAlt.MA.DQ (Formalism.FourierDecayAlt.D.parOf S v))) (Formalism.FourierDecayAlt.D.parOf S v).r)
      (j : ∀ v : Fin S.f, Formalism.FourierDecayAlt.M.Ty (Formalism.FourierDecayAlt.D.parOf S v) →
        Formalism.FourierDecayAlt.MA.SmQ (Formalism.FourierDecayAlt.D.parOf S v).r (Formalism.FourierDecayAlt.D.parOf S v).TT)
      (lam : ∀ v : Fin S.f, Fin ((Formalism.FourierDecayAlt.D.parOf S v).k + 2 * (Formalism.FourierDecayAlt.D.parOf S v).r + 1) → ℝ)
      (Cm σ : Fin S.f → ℝ),
      (∀ v, Formalism.FourierDecayAlt.JC.IsModelPlace S (Formalism.FourierDecayAlt.KB.plT S p) f χ v (L v) (j v) (lam v) c (Cm v) (σ v)) →
      (∏ v, Formalism.FourierDecayAlt.JCT.jvModel S j Cm v) = jn

end Formalism.L2.SG.Pf.CarrierT
