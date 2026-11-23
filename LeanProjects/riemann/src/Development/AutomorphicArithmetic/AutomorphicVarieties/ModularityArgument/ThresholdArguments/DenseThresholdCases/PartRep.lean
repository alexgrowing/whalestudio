import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT

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
namespace UpperTheory.V.Z.J.D
def Ord1Alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) W),
    GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → ∀ (b : ℕ) (φ : Fin n → Uo k → ℂ) (μ : Fin n → ℂ),
    (∀ i (y : Uo k), (y : kˣ) ∈ Uc k (b + 1) → φ i y = 1) → Reg k μ → Module.rank ℂ (locEig π b φ μ) ≤ 1
def SphSameAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q τ₀).X.I.T →* Aˣ) (x : A →ₐ[c.O] Qbar l) (c0 : ℕ)
    (sp : (hset Q τ₀).X.Fn A m → Fin m → (hset Q τ₀).X.Fn ℂ d), (hset Q τ₀).IsWt θ → (hset Q τ₀).IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (K : (hset Q τ₀).Lev) (ev : (hset Q τ₀).Op → ℂ), (∀ v j, ‖ι.symm (ev (.inr (v, j)))‖ = 1) → ∀ σ σ', IsAutRepU σ → IsAutRepU σ' →
    (∀ w, IsSplitAt w → ∃ τ, Cp σ w τ ∧ Cp σ' w τ) → YOf Q ι τ₀ e ξ σ ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ →
    YOf Q ι τ₀ e ξ σ' ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev = YOf Q ι τ₀ e ξ σ' ⊓ zL (hset Q τ₀) θ ι x.toRingHom lam c0 ev d ((hset Q τ₀).X.rpF ℂ d m)
def AtSameAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev), V.S' = s.S → ∀ (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q τ₀).X.I.T →* Aˣ) (x : A →ₐ[c.O] Qbar l) (c0 : ℕ)
    (sp : (hset Q τ₀).X.Fn A m → Fin m → (hset Q τ₀).X.Fn ℂ d), (hset Q τ₀).IsWt θ → (hset Q τ₀).IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (K : (hset Q τ₀).Lev) (ev : (hset Q τ₀).Op → ℂ), ∀ σ σ', IsAutRepU σ → IsAutRepU σ' → YOf Q ι τ₀ e ξ σ ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ →
    YOf Q ι τ₀ e ξ σ' ⊓ zPart (hset Q τ₀) θ ι x.toRingHom lam ξ K c0 ev ≠ ⊥ → ∀ π : CuspSub L n, At π σ → At π σ'
def BcOfAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.BCT.Unr E →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ →
    ∀ ρ : G E Ω →* GL (Fin n) (Qbar l), Continuous ρ → Af.IsIrr ρ →
    (∀ᶠ w : Plc E in cofinite, IsSplitAt w → ∀ τ, Cp σ w τ → _root_.UpperTheory.V.Z.Win.LocGlobT ι ρ w τ) →
    ∃ π : CuspSub E n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ At π σ ∧
      (∀ φ lam, HasWeightAt σ φ lam → π.HasInfChar φ (infOfWeight lam)) ∧ ∀ w, IsUnramU σ w → ∃ B, (CG.mk π).HasSat w B
def PartRepAlt : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l)
    (H : HSet L Ω l n c), H.Ax → ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp → ∀ (K : H.Lev) (a : H.Op → c.O) [Fact (CommOn (H.MK θ a K) (H.op A))] [Module.Free A (H.MK θ a K)] [Module.Finite A (H.MK θ a K)]
    (z : H.TK θ a K →ₐ[c.O] Qbar l), z.toRingHom.comp (algebraMap A _) = x.toRingHom → ∀ (I : Ideal (H.TK θ a K)) (D : W.GDet n (H.TK θ a K) H.Gq)
    (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K I D ψ → ∀ ρ : H.Gq →* GL (Fin n) (Qbar l), Continuous ρ →
    Af.IsIrr ρ → D.map z.toRingHom = W.GDet.ofRep (W.mat ρ) → ∀ Y : H.PartAltAlt ι lam ξ,
    Y.Y ⊓ zPart H θ ι x.toRingHom lam ξ K c0 (fun i => ι (z (H.gen θ a K i))) ≠ ⊥ → ∃ g : GL (Fin n) (Qbar l), ∀ h, Y.r h = g * ρ h * g⁻¹
end UpperTheory.V.Z.J.D
end
end
