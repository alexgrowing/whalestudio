import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z.J.D
namespace UpperTheory.V.Z.Desc.V0
section Abs
variable {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W]
end Abs
section Set
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c)
variable {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ)
variable (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (K : H.Lev) {G : Type} [Group G] (β : G →* H.Ga) (a : G →₀ ℤ) (N : ℕ)
def IsDimEAlt (D : ℕ) : Prop :=
  ∃ (x : A →ₐ[c.O] Qbar l) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d)
    (ev : H.Op → ℂ), H.IsSpec θ ι x.toRingHom lam ξ c0 sp ∧ (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) ∧
    zPart H θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ ∧
    (∀ Y : H.PartAltAlt ι lam ξ, Y.Y ⊓ zPart H θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → Af.IsIrr Y.r) ∧
    D = Module.finrank ℂ ↥(zPart H θ ι x.toRingHom lam ξ K c0 ev ⊓ ePart ((trF H d).comp β) a N)
end Set
section U
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {n : ℕ} {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {m : ℕ}
variable {r : Resid V.frame c.O n} (B : W.UniversalOrdinaryDeterminantRing r)
end U
def CountEAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 → ∀ (ι : Qbar l ≃+* ℂ) (lam : Wt L l n), ∃ a₀ : ℕ,
    ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ →
    ∀ (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q τ₀).X.I.T →* Aˣ) (x : A →ₐ[c.O] Qbar l) (c0 : ℕ)
    (sp : (hset Q τ₀).X.Fn A m → Fin m → (hset Q τ₀).X.Fn ℂ d), (hset Q τ₀).IsWt θ → (hset Q τ₀).IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (K : (hset Q τ₀).Lev) (ev : (hset Q τ₀).Op → ℂ), (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) →
    zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → (∀ Y : (hset Q τ₀).PartAltAlt ι lam ξ, Y.Y ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → Af.IsIrr Y.r) →
    ∃ (π : CuspSub L n) (σ : Submodule ℂ (UA L n → ℂ)) (C : Comps V σ), (∀ u : s.St, π.IsLocComp (s.w u) (C.u u)) ∧
      π.IsLocComp (s.w s.v0) C.o ∧ YOf Q ι τ₀ e ξ σ ≠ ⊥ ∧ IsAutRepU σ ∧
      ∀ (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ), (∀ g ∈ a.support, g ∈ KO _ (Fin n)) →
        (Module.finrank ℂ ↥(zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ⊓ eC Q τ₀ d a N) : Cardinal) = a₀ * Module.rank ℂ (cInv C ι τ₀ a N)
def ZEqDimEAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 →
    ∃ (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ), IsE (KO _ (Fin n)) (Kc _ n 1) a N ∧ ¬ l ∣ N ∧
    ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ)
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A]
    (θ : (hset Q τ₀).X.I.T →* Aˣ), (hset Q τ₀).IsWt θ → ∀ (lam : Wt L l n) (K : (hset Q τ₀).Lev) (D D' : ℕ),
    _root_.UpperTheory.V.Z.Desc.V0.IsDimEAlt (hset Q τ₀) θ ι lam K (sec0 n s) a N D → _root_.UpperTheory.V.Z.Desc.V0.IsDimEAlt (hset Q τ₀) θ ι lam K (sec0 n s) a N D' → 1 ≤ D ∧ D = D'
def NumJEAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 → ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (B : W.UniversalOrdinaryDeterminantRing r)
    (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev) (J : Ideal B.B), IsDomain Λ.Λ → R.IsJ B K J → J.IsRadical →
    NumE B Λ J
end UpperTheory.V.Z.Desc.V0
end
end
