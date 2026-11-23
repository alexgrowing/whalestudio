import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionHeisenbergInvariant

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.HeisExchange

open GlobalTheory.Unf.ContrHeis

variable {D : D7}

theorem kappa_mul {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D) (g : GA D S)
    (w : WO S B'.L) : l.κ S (w ⬝ mt S g⁻¹) = mt S g ⬝ l.κ S w := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  exact (GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)).2.2.2.1 g w

theorem sympl_resT {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (c d : WO S L) :
    symplOH S T ((o.resT S).symm (0, c)) ((o.resT S).symm (0, d)) = symplOH S L c d := by
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]

theorem sympl_resS {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (c d : WO L S) :
    symplOH T S ((o.resS S).symm (0, c)) ((o.resS S).symm (0, d)) = symplOH L S c d := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]

theorem act_resT {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (g : GA D S) (a : GA D A) (c : WO S L) :
    actO S T g (o.emb (a, 1)) ((o.resT S).symm (0, c)) = (o.resT S).symm (0, c ⬝ mt S g⁻¹) := by
  rw [AddEquiv.eq_symm_apply, o.resT_actO, AddEquiv.apply_symm_apply]
  simp only [actO_eq, mt_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul]

theorem act_resS {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (g : GA D S) (a : GA D A) (c : WO L S) :
    actO T S (o.emb (a, 1)) g ((o.resS S).symm (0, c)) = (o.resS S).symm (0, mt S g ⬝ c) := by
  rw [AddEquiv.eq_symm_apply, o.resS_actO, AddEquiv.apply_symm_apply]
  simp only [actO_eq, inv_one, mt_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one]

theorem quasi_resT {ψ : AddChar (AF D.host.F) ℂ} {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {γ : WO S L} (hγ : γ ∈ ratMx D L.rank S.rank) (v : WO S L) :
    f ((o.resT S).symm (0, γ + v)) = ψ (-symplOH S L γ v) * f ((o.resT S).symm (0, v)) := by
  have r : (o.resT S).symm (0, γ) ∈ ratMx D T.rank S.rank := by
    refine (o.mem_ratL_resT S _).2 ?_
    rw [AddEquiv.apply_symm_apply]
    exact ⟨zero_mem _, hγ⟩
  obtain ⟨γ₂, hγ₂⟩ := r
  have q := hf.quasi γ₂ ((o.resT S).symm (0, v))
  have e : ratW T S γ₂ = (o.resT S).symm (0, γ) := hγ₂
  rwa [e, ← map_add, Prod.mk_add_mk, zero_add, sympl_resT] at q

theorem quasi_resS {ψ : AddChar (AF D.host.F) ℂ} {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {f : WO T S → ℂ}
    (hf : IsThetaFunO ψ T S f) {γ : WO L S} (hγ : γ ∈ ratMx D S.rank L.rank) (v : WO L S) :
    f ((o.resS S).symm (0, γ + v)) = ψ (-symplOH L S γ v) * f ((o.resS S).symm (0, v)) := by
  have r : (o.resS S).symm (0, γ) ∈ ratMx D S.rank T.rank := by
    refine (o.mem_ratL_resS S _).2 ?_
    rw [AddEquiv.apply_symm_apply]
    exact ⟨zero_mem _, hγ⟩
  obtain ⟨γ₂, hγ₂⟩ := r
  have q := hf.quasi γ₂ ((o.resS S).symm (0, v))
  have e : ratW S T γ₂ = (o.resS S).symm (0, γ) := hγ₂
  rwa [e, ← map_add, Prod.mk_add_mk, zero_add, sympl_resS] at q

theorem integral_exchange {ψ : AddChar (AF D.host.F) ℂ} {S L : HSp D} (vL : VolM D L.rank S.rank) (T Y : WO S L → ℂ)
    (hT : ∀ γ ∈ ratMx D L.rank S.rank, ∀ v, T (γ + v) = ψ (-symplOH S L γ v) * T v)
    (hY : ∀ γ ∈ ratMx D L.rank S.rank, ∀ v, Y (γ + v) = ψ (symplOH S L γ v) * Y v) (x : WO S L) :
    ∫ v in vL.𝓕, T v * (ψ (-symplOH S L v x) * Y (v + x)) ∂vL.μ =
      ∫ v in vL.𝓕, ψ (symplOH S L v (-x)) * T (v + -x) * Y v ∂vL.μ := by
  have neg : ∀ v y : WO S L, symplOH S L v (-y) = -symplOH S L v y := by
    intro v y
    have h := GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := L) v y (-y)
    rw [add_neg_cancel, symplOH_zero_right] at h
    linear_combination -h
  rw [← covolOne_integral_add vL.covol (fun v => ψ (symplOH S L v (-x)) * T (v + -x) * Y v) ?_ x]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show _ = ψ (symplOH S L (v + x) (-x)) * T (v + x + -x) * Y (v + x)
    rw [add_neg_cancel_right, neg, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_self, add_zero]
    ring
  · intro γ hγ a
    show ψ (symplOH S L (γ + a) (-x)) * T (γ + a + -x) * Y (γ + a) = ψ (symplOH S L a (-x)) * T (a + -x) * Y a
    rw [add_assoc, hT γ hγ, hY γ hγ, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right,
      AddChar.map_add_eq_mul]
    have e : ψ (symplOH S L γ (-x)) * ψ (-(symplOH S L γ a + symplOH S L γ (-x))) * ψ (symplOH S L γ a) = 1 := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_zero_eq_one ψ]
      congr 1
      ring
    linear_combination (ψ (symplOH S L a (-x)) * T (a + -x) * Y a) * e

theorem besselFourierJacobi_unfolding_heisenberg_exchange : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ), IsContAut B.A φ →
    ∀ (Ξ : WO B.V₀ J.W₀ → ℂ) (Θ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ → IsThetaFunO ψ J.W₀ B'.V₀ Θ → ∀ w₀ : WO J.W₀ B'.L,
      hand0 s₁ s₂ l vL φ (heisO ψ B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w₀)) Ξ) Θ =
        hand0 s₁ s₂ l vL φ Ξ (heisO ψ J.W₀ B'.V₀ ((B'.o.resT J.W₀).symm (0, -w₀)) Θ) := by
  intro D ψ σ B J B' s₁ s₂ l vL φ _ Ξ Θ hΞ hΘ w₀
  funext h₁
  refine integral_congr_ae (Filter.Eventually.of_forall fun h₀ => ?_)
  have key := integral_exchange (ψ := ψ) vL
    (fun v => s₂.om₀ (h₀, B'.o.emb (h₁, 1)) Θ ((B'.o.resT J.W₀).symm (0, v)))
    (fun v => liftA B.o s₁.om₀ B.vA φ Ξ h₀ (l.κ J.W₀ v))
    (fun γ hγ v => quasi_resT B'.o J.W₀ (s₂.weil₀.om_pres _ _ hΘ) hγ v)
    (fun γ hγ v => by
      simp only [liftA]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      beta_reduce
      rw [kappa_add, quasi_resS B.o J.W₀ (s₁.weil₀.om_pres _ _ hΞ) (kappa_rat l _ γ hγ), symplOH_kappa, neg_neg]
      ring) (w₀ ⬝ mt J.W₀ h₀⁻¹)
  simp only [pairKer, contractT, thPair, handBF_eq, RCLike.star_def, Complex.conj_conj]
  refine Eq.trans ?_ (key.trans ?_)
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    beta_reduce
    congr 1
    simp only [liftA]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    beta_reduce
    rw [s₁.weil₀.om_heis _ _ _ _ hΞ, act_resS, ← kappa_mul, heisO, sympl_resS, symplOH_kappa, ← map_add,
      Prod.mk_add_mk, add_zero, ← kappa_add]
    ring
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    beta_reduce
    rw [s₂.weil₀.om_heis _ _ _ _ hΘ, act_resT, heisO, sympl_resT, ← map_add, Prod.mk_add_mk, add_zero, Matrix.neg_mul]

end GlobalTheory.FinPl.HeisExchange

end
