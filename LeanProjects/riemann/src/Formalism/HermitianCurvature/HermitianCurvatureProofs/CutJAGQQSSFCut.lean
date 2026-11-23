import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCore
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCGenToQQ

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

def GQBridge : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e → GQQ P Bs e →
    ∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (X.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)

def GQKap : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    (∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)) →
    ∀ f : M.Ty P → ℂ, Gauge.GC.Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f)

def GQSS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    2 ≤ P.k → ∀ (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    ActHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    (∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b)) →
    (∀ f : M.Ty P → ℂ, Gauge.GC.Intw P Bs e (d.κ f) (MA.kap P (MA.DQ P) f)) →
    ∀ l ∈ Finset.Icc 1 (P.k - 1),
      Gauge.GC.Intw P Bs e (d.SS l) (MA.SS P (MA.DQ P) l) ∧
      Gauge.GC.Intw P Bs e (star (d.SS l)) (star (MA.SS P (MA.DQ P) l))

def GQQSSFOfCut : Prop := GQBridge → GQKap → GQSS → GQQSSF

theorem gQQSSF_of_cut : GQQSSFOfCut := by
  intro hB hK hS Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hg
  have hQ : ∀ (Y : ℝ) (a b : Fin 2), Gauge.GC.Intw P Bs e (d.QQ (Y : ℂ) a b) (MA.QQr P (MA.DQ P) (Y : ℂ) a b) := by
    intro Y a b
    rw [← hA.2.2.2.2 (Y : ℂ)]
    exact hB Wp Wq P Bs hk X d hA e he hg Y a b
  have hκ := hK Wp Wq P Bs hk X d hA e he hQ
  intro l hl Φ
  exact ⟨(hS Wp Wq P Bs hk X d hA e he hQ hκ l hl).1 Φ, (hS Wp Wq P Bs hk X d hA e he hQ hκ l hl).2 Φ⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
