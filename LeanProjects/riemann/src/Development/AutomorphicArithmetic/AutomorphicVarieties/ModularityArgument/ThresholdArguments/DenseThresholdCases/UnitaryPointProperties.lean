import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocDataT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.AtLOf

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
open UpperTheory.V.HV (Coef)
section Alg
variable {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] (n : ℕ) {V : Type} [Fintype V] (S : V → Plc L)
variable {n S}
end Alg
namespace HSet
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c)
variable (A : Type) [CommRing A] [Algebra c.O A]
variable {A} (θ : H.X.I.T →* Aˣ)
variable (ι : Qbar l ≃+* ℂ)
structure PartAltAlt (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) : Type 1 where
  Y : Submodule ℂ (Fin H.m → H.X.Fn ℂ d)
  le : Y ≤ H.Big ι ξ
  ne : Y ≠ ⊥
  σl : ∀ v : H.V, SmIrr (GLw n (H.Sl v))
  isoL : ∀ v, IsoSum (H.atV d v) Y (σl v)
  σq : ∀ q : H.Q, SmIrr (GLw n (H.wq q))
  isoQ : ∀ q : H.Q, IsoSum (H.atW ι d (H.wq q)) Y (σq q)
  a : H.Wp → ℕ → ℂ
  a_zero : ∀ w, a w 0 = 1
  sph : ∀ (w : H.Wp) j, ∀ F ∈ Y, sphOp (H.atW ι d w.1) j F = a w j • F
  r : H.Gq →* GL (Fin n) (Qbar l)
  cont : Continuous r
  ss : IsSSRep r
  frob : ∀ (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
    (r (H.prj σ⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = heckePol n (normV w.1) (a w)
  atL : ∀ v, _root_.UpperTheory.V.Z.Ord.AtLT ι (H.ovr v) (r.comp (H.dec v)) lam (σl v)
  atQ : ∀ (q : H.Q) (B : ValuationSubring Ω) (h : IsPlaceOver B (H.wq q)) (rc : IrrGL ((H.wq q).adicCompletion L) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc →
    _root_.UpperTheory.V.Z.Win.WOT ι (r.comp H.prj) (rc (algNorm (σq q)))
def AutomorphicHeckeSet (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop) : Prop :=
  ∀ lam ∈ H.admitted, ∀ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), IsAlgWt ι lam ξ → ∀ F ∈ H.Big ι ξ,
    (∃ K, F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K)) → (∃ e, F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e)) →
    F ∈ ⨆ Y : {Y : H.PartAltAlt ι lam ξ // P lam Y.r}, Y.1.Y
variable [IsLocalRing A] (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))]
end HSet
end UpperTheory.V.Hi
end
end
