import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.ZeroDimMemIwahoriFixed

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open UpperTheory.V.Z.J.D
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

open private vs_ne part_eq rank_of from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.ZeroDimMemIwahoriFixed

namespace UpperTheory.V.Z.Desc.V0

section Comp

variable {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] {m : ℕ}
  {ρ : Representation ℂ G M} {ρF : Representation ℂ G (Fin m → M)}

private theorem opE_pi (h : ∀ g F i, ρF g F i = ρ g (F i)) (a : G →₀ ℤ) (F : Fin m → M) (i : Fin m) :
    opE ρF a F i = opE ρ a (F i) := by
  simp only [opE, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply, h]

private theorem ePart_pi (h : ∀ g F i, ρF g F i = ρ g (F i)) (a : G →₀ ℤ) (N : ℕ) (F : Fin m → M) :
    F ∈ ePart ρF a N ↔ ∀ i, F i ∈ ePart ρ a N := by
  have hn : ∀ (i : Fin m), ((N : Module.End ℂ (Fin m → M)) F) i = (N : Module.End ℂ M) (F i) := fun i => by
    simp [Module.End.natCast_apply]
  simp only [ePart, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  constructor
  · intro e i
    rw [← opE_pi h, e, hn]
  · intro e
    funext i
    rw [opE_pi h, e i, hn]

end Comp

section U

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {n : ℕ} {s : HidaSetting l L Ω} {V : s.Lev} {lam : Wt L l n} {d : ℕ}

private theorem eC_eq (Q : QData V) {c : Coef l} {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) :
    eC Q τ₀ d a N = Submodule.pi Set.univ fun _ =>
      ePart (((actS n V d).comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)) a N := by
  ext F
  refine Iff.trans (ePart_pi (m := m) (M := Ga l L n × GL' n V → Fin d → ℂ) (ρF := (trF (hset Q τ₀) d).comp (sec0 n s))
    (ρ := ((actS n V d).comp (MonoidHom.inr _ _)).comp (MonoidHom.inr _ _)) (fun g F i => rfl) a N F) ?_
  exact ⟨fun h i _ => h i, fun h i => h i trivial⟩

private theorem part_eqE (hS : SecS) (hn : 1 ≤ n) (hV : V.S' = s.S) (Q : QData V) {c : Coef l} (ι : Qbar l ≃+* ℂ) {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (σ : Submodule ℂ (UA L n → ℂ))
    (R : Submodule ℂ (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ)) (hR : R = VS V ι e ξ Q τ₀ σ) (b : ℕ)
    (φ : ∀ v : V.frame.Vl, Fin n → Uo ((s.w v.1).adicCompletion L) → ℂ) (μ : V.frame.Vl → Fin n → ℂ)
    (a : GLw n (s.w s.v0) →₀ ℤ) (N : ℕ) :
    YOf Q ι τ₀ e ξ σ ⊓ eigL (fun v : V.frame.Vl => s.w v.1) ((hset Q τ₀).X.rpF ℂ d m) b φ μ ⊓ eC Q τ₀ d a N =
      invE (KT n (wt s)) (Kc _ n 1) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀)
        ((actS n V d).comp (MonoidHom.inr _ _)) a N ⊓ Submodule.pi Set.univ fun _ =>
        R ⊓ eigL (fun v : V.frame.Vl => s.w v.1) ((actS n V d).comp (MonoidHom.inl _ _)) b φ μ := by
  rw [part_eq hS hn hV Q ι τ₀ e ξ σ R hR b φ μ, eC_eq, invE]
  exact inf_right_comm _ _ _

end U

end UpperTheory.V.Z.Desc.V0

set_option maxHeartbeats 1600000 in
open UpperTheory.V.Z.Desc.V0 in
theorem UpperTheory.V.Z.Desc.V0.yDimE :
    UpperTheory.V.Z.J.D.Flath → EigBoxE → UpperTheory.V.Z.J.D.SecS → YDimE := by
  intro hFl hEB hS l _ L Ω _ _ _ _ _ _ s n hn V hV Q c ι m τ₀ lam d e ξ hb σ hσ hun hwt C b φ μ a N
  have hne := vs_ne hn hV Q ι τ₀ e ξ hb hσ hun hwt
  have h0 := hFl l L Ω s n hn V hV Q c ι m τ₀ lam d e ξ hb σ hσ hne C
  refine Exists.elim h0 fun f hf => ?_
  have h1 := part_eqE hS hn hV Q ι τ₀ e ξ σ _ hf.2.1 b φ μ a N
  have h2 := hEB L n V.frame.Vl (fun v => s.w v.1) _ _ _ _ _ C.repL C.repS (actS n V d) f hf.1 hf.2.2 m (KT n (wt s)) (Kc _ n 1)
    ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) b φ μ a N
  exact rank_of h1 h2
