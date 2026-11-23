import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis

noncomputable section

namespace GlobalTheory.RowLev

open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev ModInst (D : D7) (V : HSp D) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (pl : InfinitePlace D.host.F ≃ D.what₂.Tau) : Type :=
  InstData D.sp.cm V (fun v => M.ε (pl v)) (fun v => tauE D (pl v))

def IsSwitch {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    {pl : InfinitePlace D.host.F ≃ D.what₂.Tau} (X : ModInst D V M pl)
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (T : GA D V ≃* X.inst.GA) : Prop :=
  (letI : TopologicalSpace X.inst.Gf := X.inst.topf; Continuous T ∧ Continuous T.symm) ∧
    (∀ h, h ∈ GQ V ↔ T h ∈ X.inst.GFset) ∧
    (∀ h, X.inst.fmat (T h).2 =
      (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram h).map (Algebra.TensorProduct.comm D.host.F _ _)) ∧
    ∀ v h, uMat ((T h).1 v) = M.fr (pl v) * Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ (pl v)) h * (M.fr (pl v))⁻¹

def levHom (I : AutInst) {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (J : Set I.Gf) (χ : I.Gf → ℂ) :
    Set (Hs →L[ℂ] I.L2 μf fund) :=
  {A | A ∈ I.HomS σs μf fund R ∧ ∀ k ∈ J, (R (1, k)).comp A = χ k • A}

def IsCuspHom (I : AutInst) {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    {μf : Measure I.Gf} [SigmaFinite μf] {fund : Set I.GA} (A : Hs →L[ℂ] I.L2 μf fund) : Prop :=
  ∀ u, I.IsCuspFn (I.muA μf) (I.ext (A u))

def Represents {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    {pl : InfinitePlace D.host.F ≃ D.what₂.Tau} {X : ModInst D V M pl} (T : GA D V ≃* X.inst.GA)
    {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (tens : (∀ v, M.H (pl v)) → Hs)
    (μf : @Measure X.inst.Gf X.inst.instMeasurableSpaceGf) [@SigmaFinite _ X.inst.instMeasurableSpaceGf μf] {fund : Set X.inst.GA}
    (A : Hs →L[ℂ] X.inst.L2 μf fund) (Φ : MMap M) : Prop :=
  ∀ u : M.Vec, ∀ᵐ x ∂(X.inst.muA μf), Φ u (T.symm x) = X.inst.ext (A (tens fun v => (u (pl v) : M.H (pl v)))) x

end GlobalTheory.RowLev
