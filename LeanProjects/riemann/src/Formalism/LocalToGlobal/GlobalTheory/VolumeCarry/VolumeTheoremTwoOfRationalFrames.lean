import Formalism.LocalToGlobal.GlobalTheory.VolumeCarry.VolumeTheoremTwoOfC3Stable
import Mathlib
import Formalism.PeriodIntegrals.GaugeGap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameIso.MulFirstColumnOfUnitColumn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.VolumeCarry

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def frameMat (D : D7) (W W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V) :
    Matrix (Fin W.rank) (Fin W'.rank) D.host.E :=
  fun i j => W.frame.repr (ι (W'.frame j)) i

def CarryFrame (D : D7) : Prop :=
  ∀ (W : HSpace D.host.E), W.SigOK → 3 ≤ W.rank → ∀ (x : W.V) (β : D.host.F), β ≠ 0 →
    W.hT x x = algebraMap D.host.F D.host.E β →
    ∀ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
      HSpace.IsIsomEmb W' W ι → LinearMap.range ι = LinearMap.ker (W.hT x) → W'.SigOK →
      W.rank = W'.rank + 1 →
    ∃ e : Hstab (AF D.host.F) D.sp.cm.sig W.gram (crd1 D W x) ≃* HA (AF D.host.F) D.sp.cm.sig W'.gram,
      (∀ g : Hstab (AF D.host.F) D.sp.cm.sig W.gram (crd1 D W x), FrameRel W.gram W'.gram (frameMat D W W' ι)
        (g : HA (AF D.host.F) D.sp.cm.sig W.gram) (e g)) ∧
      Continuous e ∧ Continuous e.symm ∧
      (∀ g, g ∈ HstabFin (AF D.host.F) D.sp.cm.sig W.gram (crd1 D W x) ↔
        e g ∈ HFinIn (AF D.host.F) D.sp.cm.sig W'.gram)

def CarryMeas (D : D7) : Prop :=
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∀ x : W.V, W.hT x x = (if s then 1 else -1) →
    ∀ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
      HSpace.IsIsomEmb W' W ι → LinearMap.range ι = LinearMap.ker (W.hT x) → W'.SigOK →
      (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1))) →
    ∀ e : Hstab (AF D.host.F) D.sp.cm.sig W.gram (crd1 D W x) ≃* HA (AF D.host.F) D.sp.cm.sig W'.gram,
      (∀ g : Hstab (AF D.host.F) D.sp.cm.sig W.gram (crd1 D W x), FrameRel W.gram W'.gram (frameMat D W W' ι)
        (g : HA (AF D.host.F) D.sp.cm.sig W.gram) (e g)) →
      Continuous e → Continuous e.symm →
      ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
      ∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram), IsVolMeas D W P Q μ →
      ∀ ν : Measure (Fin 1 → Fin W.rank → AF D.host.F ⊗[D.host.F] D.host.E),
        IsDxDq D.host.F D.host.E D.sp.cm.sig W.rank W.gram ψ (if s then 1 else -1) ν →
      ∀ μ' : Measure (HA (AF D.host.F) D.sp.cm.sig W'.gram),
        IsVolMeas D W' (if s then P - 1 else P) (if s then Q else Q - 1) μ' →
        Carries D.host.F D.host.E D.sp.cm.sig W.rank W.gram (crd1 D W x) μ
          (ENNReal.ofReal (Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E W.rank) • μ'.map e.symm) ν

section Gen

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

def FrameRat : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E),
    IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
    (∀ j, hE σ J (x 0) (fun i => B i j) = 0) →
    J' = Formalism.UG.cT (σ : E →+* E) B * J * B → IsHermND σ J' →
    ∀ (g : Hstab (AF F) σ J x) (g' : HA (AF F) σ J'), FrameRel J J' B (g : HA (AF F) σ J) g' →
      (g ∈ HstabFin (AF F) σ J x ↔ g' ∈ HFinIn (AF F) σ J')

def FrameRatAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    PI.GaugeGap.IsQuadInv σ → FrameRat F E σ

end Gen

theorem gram_frameMat (D : D7) (W W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V)
    (h1 : HSpace.IsIsomEmb W' W ι) :
    W'.gram = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat D W W' ι) * W.gram * frameMat D W W' ι := by
  ext i j
  have e1 : W'.gram i j = W.hT (ι (W'.frame i)) (ι (W'.frame j)) := (h1 _ _).symm
  rw [e1, ← hE_repr D W]
  simp only [hE, Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, frameMat,
    Finset.sum_mul]
  rw [Finset.sum_comm]

end Formalism.L2.GlobalTheoryTheory.VolumeCarry

end
