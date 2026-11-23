import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.AbsGood

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

namespace UpperTheory.V.Z.J.D

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ)
  (lam : Wt L l n) (K : H.Lev) (P : (H.Gq →* GL (Fin n) (Qbar l)) → Prop)

def IsDim (N : ℕ) : Prop :=
  ∃ (x : A →ₐ[c.O] Qbar l) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d)
    (ev : H.Op → ℂ), H.IsSpec θ ι x.toRingHom lam ξ c0 sp ∧ (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) ∧
    zPart H θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ ∧
    (∀ Y : H.Part ι lam ξ, Y.Y ⊓ zPart H θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → P Y.r) ∧
    N = Module.finrank ℂ (zPart H θ ι x.toRingHom lam ξ K c0 ev)

end

def MuZ : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → ∀ (K : H.Lev) (a : H.Op → c.O) [Fact (CommOn (H.MK θ a K) (H.op A))]
    (B : Type) [CommRing B] [Algebra c.O B] (j : A →ₐ[c.O] B) (f : B →ₐ[c.O] H.TK θ a K), Function.Surjective f →
    ∀ [Module B (H.MK θ a K)] (hs : ∀ (b : A) (m : H.MK θ a K), b • m = j b • m), (∀ (b : B) (m : H.MK θ a K), b • m = (f b).1 m) →
    ∀ z : H.TK θ a K →ₐ[c.O] Qbar l, z.toRingHom.comp (algebraMap A _) = x.toRingHom →
    zPart H θ ι x.toRingHom lam ξ K c0 (fun i => ι (z (H.gen θ a K i))) ≠ ⊥ ∧
    UpperTheory.V.J.mu j (H.MK θ a K) hs (z.comp f) =
      Module.finrank ℂ (zPart H θ ι x.toRingHom lam ξ K c0 fun i => ι (z (H.gen θ a K i)))

def ZEqDim : Prop :=
  Af.HypothesesH → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 → ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ)
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O), TypeFor r ι τ₀ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A]
    (θ : (hset Q τ₀).X.I.T →* Aˣ), (hset Q τ₀).IsWt θ → ∀ (lam : Wt L l n) (K : (hset Q τ₀).Lev) (N N' : ℕ),
    IsDim (hset Q τ₀) θ ι lam K (fun ρ => Af.IsIrr ρ ∧ ∀ g ∈ V.frame.I0, ρ g = 1) N →
    IsDim (hset Q τ₀) θ ι lam K (fun ρ => Af.IsIrr ρ ∧ ∀ g ∈ V.frame.I0, ρ g = 1) N' → N = N'

def NumJ : Prop :=
  Af.HypothesesH → Mult → CompOf → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → n ≤ 4 → ∀ (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (B : W.UniversalOrdinaryDeterminantRing r)
    (Λ : LamObj r) (R : HD Q ι Λ) (K : (hset Q R.τ₀).Lev) (J : Ideal B.B), r.V0ok → IsDomain Λ.Λ → R.IsJ B K J → J.IsRadical →
    UpperTheory.V.J.Num B Λ J

end UpperTheory.V.Z.J.D
