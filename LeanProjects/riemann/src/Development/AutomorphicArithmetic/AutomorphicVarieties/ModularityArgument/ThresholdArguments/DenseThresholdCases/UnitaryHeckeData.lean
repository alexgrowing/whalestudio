import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Hi
section Type_
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {St : Type} {wt : St → Plc L} {At : St → ValuationSubring Ω} (ht : ∀ u, IsPlaceOver (At u) (wt u))
def IsTypeAlt {m : ℕ} (τ₀ : KT n wt →* GL (Fin m) ℂ) (χ : ∀ u, Fin n → Ine (F := L) (At u) →* ℂˣ) : Prop :=
  IsOpen (τ₀.ker : Set (KT n wt)) ∧
  ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [Nontrivial M] (ρ : Representation ℂ (GV n wt) M) (σ : ∀ u, SmIrr (GLw n (wt u))),
    (∀ u, IsoSum (by classical exact ρ.comp (MonoidHom.mulSingle (fun u => GLw n (wt u)) u)) ⊤ (σ u)) →
    ((∃ F : Fin m → M, F ≠ 0 ∧ ∀ (k : KT n wt) i, ∑ j, τ₀ k i j • ρ k (F j) = F i) ↔
      ∀ u rc, _root_.UpperTheory.Zero.LLC.IsRecT (ht u) rc → IsTypeWD (ht u) (χ u) (rc (algNorm (σ u))))
end Type_
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
namespace CaseU
variable (l L) (n : ℕ)
variable {l L}
variable (s : HidaSetting l L Ω)
variable {s} (V : s.Lev)
variable {V} (Q : QData V)
variable {n} {c : Coef l} {m : ℕ}
variable (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ)
def TypeForAlt (τ₀ : KT n (wt s) →* GL (Fin m) c.O) : Prop :=
  ∀ t, r.IsTeich t → _root_.UpperTheory.V.Hi.IsTypeAlt (fun u : s.St => s.hw u)
    ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀)
    fun u i => W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l))) ((t i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype))
variable (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
structure UnitaryPointProperties (lam : Wt L l n) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) : Prop where
  form : ∃ P, V.frame.IsForm c.O n ρ P
  type : ∀ t, r.IsTeich t → ∀ u : s.St, ∃ g : GL (Fin n) (Qbar l), ∀ x ∈ V.frame.Iu u,
    ((g * ρ x * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      Matrix.diagonal fun i => algebraMap c.O (Qbar l) (t i x)
  cusp : Af.IsIrr ρ → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (ρ.comp V.pr) π ∧ HasWt ι s π lam
  aut : ∃ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ ∧ (∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → _root_.UpperTheory.V.Z.Win.LocGlobT ι (ρ.comp V.pr) w τ) ∧
    (∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual) ∧
    (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w) ∧
    (∀ w, IsSplitAt w → ∃ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ) ∧
    ∃ τ : SmIrr (GLw n (s.w s.v0)), IsCompAlong σ (locU n (s.w s.v0)) ((cLoc (s.w s.v0)).comp (locU n (s.w s.v0)).subtype) τ.ρ ∧
      fixd τ.ρ (Kc _ n 1) ≠ ⊥
variable {lam : Wt L l n} {d : ℕ}
  (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
variable {r} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r)
structure UnitaryHeckeData : Type where
  m : ℕ
  τ₀ : KT n (wt s) →* GL (Fin m) c.O
  type : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀
  θ : (hset Q τ₀).X.I.T →* Λ.Λˣ
  theta : IsTheta Q τ₀ Λ θ
  isWt : (hset Q τ₀).IsWt θ
  a : (hset Q τ₀).Op → c.O
  res : IsRes Q r τ₀ a
variable {Q ι Λ} (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev)
abbrev UnitaryHeckeData.M := (hset Q R.τ₀).MK R.θ R.a K
def UnitaryHeckeData.IsJ (J : Ideal B.B) : Prop := (hset Q R.τ₀).IsJ R.θ R.a K B.u.D B.u.ψ (Λ.toPair B.u) J
end CaseU
end UpperTheory.V.Hi
end
end
