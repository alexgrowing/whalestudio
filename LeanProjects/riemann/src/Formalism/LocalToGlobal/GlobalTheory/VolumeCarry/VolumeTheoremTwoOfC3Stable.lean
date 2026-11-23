import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramFibrationFormulas.SiegelWeilFiniteVolumeCase
import Formalism.SharpRestriction.CuspSpanNormBounds.MassRatioBoundPower
import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.VolumeCarry

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def crd1 (D : D7) (W : HSpace D.host.E) (x : W.V) : Fin 1 → Fin W.rank → D.host.E :=
  fun _ => ⇑(W.frame.repr x)

theorem sig_apply (D : D7) (a : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) a = star a := rfl

theorem hE_repr (D : D7) (W : HSpace D.host.E) (x y : W.V) :
    hE D.sp.cm.sig W.gram (W.frame.repr x) (W.frame.repr y) = W.hT x y := by
  conv_rhs => rw [← W.frame.sum_repr x, ← W.frame.sum_repr y]
  simp only [hE, Formalism.UG.hform, HSpace.gram, map_sum, LinearMap.map_smulₛₗ₂, LinearMap.sum_apply,
    map_smul, smul_eq_mul, sig_apply, starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

section Gen

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def TransAt (x : Fin 1 → Fin M → E) (β : F) : Prop :=
  ∀ y : Fin 1 → Fin M → AF F ⊗[F] E, qR (AF F) σ J (y 0) = algebraMap F (AF F) β →
    ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y

end Gen

def TransA (D : D7) : Prop :=
  ∀ (W : HSpace D.host.E), W.SigOK → ∀ (x : W.V) (β : D.host.F), β ≠ 0 →
    W.hT x x = algebraMap D.host.F D.host.E β →
    TransAt D.host.F D.host.E D.sp.cm.sig W.rank W.gram (crd1 D W x) β

def StabVol (D : D7) : Prop :=
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∀ x : W.V, W.hT x x = (if s then 1 else -1) →
    ∀ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
      HSpace.IsIsomEmb W' W ι → LinearMap.range ι = LinearMap.ker (W.hT x) → W'.SigOK →
      (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1))) →
    ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
    ∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram), IsVolMeas D W P Q μ →
    ∀ ν : Measure (Fin 1 → Fin W.rank → AF D.host.F ⊗[D.host.F] D.host.E),
      IsDxDq D.host.F D.host.E D.sp.cm.sig W.rank W.gram ψ (if s then 1 else -1) ν →
    ∀ μ'' : Measure (Hstab (AF D.host.F) D.sp.cm.sig W.gram (crd1 D W x)), μ''.IsHaarMeasure →
      Carries D.host.F D.host.E D.sp.cm.sig W.rank W.gram (crd1 D W x) μ μ'' ν →
    ∀ 𝓕'' : Set (Hstab (AF D.host.F) D.sp.cm.sig W.gram (crd1 D W x)),
      IsFundamentalDomain (HstabFin (AF D.host.F) D.sp.cm.sig W.gram (crd1 D W x)) 𝓕'' μ'' →
    ∀ (μ' : Measure (HA (AF D.host.F) D.sp.cm.sig W'.gram)) (𝓕' : Set (HA (AF D.host.F) D.sp.cm.sig W'.gram)),
      IsVolMeas D W' (if s then P - 1 else P) (if s then Q else Q - 1) μ' →
      IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W'.gram) 𝓕' μ' →
      μ'' 𝓕'' = ENNReal.ofReal (Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E W.rank) * μ' 𝓕'

end Formalism.L2.GlobalTheoryTheory.VolumeCarry

end
