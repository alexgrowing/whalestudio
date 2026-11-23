import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.FlagJ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.IrrArithPointsAutomorphicAway

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Gal.projectedFormsSystemPart

open UpperTheory.V.Z.Ord UpperTheory.Zero.LLC

def TypePlain : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ), 1 ≤ n →
    ∀ (π : CuspSub E n) (w : Plc E) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : SmIrr (GLw n w)), π.IsLocComp w σ →
    ∀ rc : IrrGL (w.adicCompletion E) → WD h, IsRecT h rc → ∀ χ : Fin n → G E Ω →* ℂˣ,
      IsTypeWD h (fun i => (χ i).comp (Ine (F := E) A).subtype) (rc (algNorm σ)) →
      GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred)

def PartLink : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ)
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O), TypeFor r ι τ₀ → ∀ (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ → YOf Q ι τ₀ e ξ σ ≠ ⊥ →
    ∃ Y : (hset Q τ₀).Part ι lam ξ, Y.Y = YOf Q ι τ₀ e ξ σ ∧ (Af.IsIrr (Y.r.comp V.pr) →
      ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι (Y.r.comp V.pr) π ∧
        (∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B) ∧
        ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), π.IsLocComp w τ →
          IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ)

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

def AwayOk (s : HidaSetting l L Ω) {n : ℕ} (ι : Qbar l ≃+* ℂ) (ρ : G L Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ Af.AttC ι ρ π ∧
    ∀ w : Plc L, ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → w.under (𝓞 (Lp L)) ≠ s.v0 → TU π w

end UpperTheory.Gal.projectedFormsSystemPart

end
