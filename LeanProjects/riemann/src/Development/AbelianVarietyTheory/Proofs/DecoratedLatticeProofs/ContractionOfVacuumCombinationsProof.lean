import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHZeroRight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionHeisenbergInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIntegrandContinuousPeriodicStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPa
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfGeneratedPointActsScalarOnLatticeVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionLeClosureIsotropicHalvesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaPreservesSupportedMatricesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLineTranslateOffLatticeKillsContractionStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ContrOpProof

variable {D : D7}

theorem mxAt_mul_right {P : Pl D → Prop} {m n r : ℕ} {u : Mx D m n} (hu : MxAt P u) (N : Mx D n r) :
    MxAt P (u * N) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hu i k)

theorem mxAt_mul_left {P : Pl D → Prop} {m n r : ℕ} (N : Mx D r m) {u : Mx D m n} (hu : MxAt P u) :
    MxAt P (N * u) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hu k j)

theorem mxAt_sub {P : Pl D → Prop} {m n : ℕ} {u v : Mx D m n} (hu : MxAt P u) (hv : MxAt P v) : MxAt P (u - v) :=
  fun i j => by simpa only [Matrix.sub_apply] using Ideal.sub_mem _ (hu i j) (hv i j)

theorem mxAt_neg {P : Pl D → Prop} {m n : ℕ} {u : Mx D m n} (hu : MxAt P u) : MxAt P (-u) :=
  fun i j => by simpa only [Matrix.neg_apply] using Submodule.neg_mem _ (hu i j)

theorem fin_of_mxAt {P : Pl D → Prop} {m n : ℕ} {u : Mx D m n} (hu : MxAt P u) : u.map (infPart D) = 0 := by
  ext i j
  exact RingHom.mem_ker.1 (Ideal.mem_inf.1 (hu i j)).1

theorem contr_smul_left {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (c : ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) :
    GlobalTheory.Unf.contr l S vL (c • f₁) f₂ = c • GlobalTheory.Unf.contr l S vL f₁ f₂ := by
  funext u v
  simp only [GlobalTheory.Unf.contr, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem biComb_single (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (a : WO A S) (a' : WO S A') (r : ℂ)
    (C : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    biComb ψ A S A' (Finsupp.single a r) (Finsupp.single a' 1) C u v =
      r * heisO ψ A S a (fun u' => heisO ψ S A' a' (C u') v) u := by
  by_cases hr : r = 0
  · subst hr
    simp [biComb, comb]
  · simp [biComb, comb, Finsupp.support_single_ne_zero _ hr]

theorem symplOH_self {S T : HSp D} (x : WO S T) : symplOH S T x (-x) = 0 := by
  have h1 := GlobalTheory.SplitScalar.symplOH_skew S T x x
  have h2 := GlobalTheory.SplitScalar.symplOH_add_self S T x x
  have h3 : symplO S T x x = 0 := by
    rw [← h2]
    nth_rewrite 2 [h1]
    exact add_neg_cancel _
  have h4 : symplOH S T x x = 0 := by rw [symplOH, h3, mul_zero]
  have h5 := GlobalTheory.SplitScalar.symplOH_add_right S T x x (-x)
  rw [add_neg_cancel, GlobalTheory.ContrComb.symplOH_zero_right, h4, zero_add] at h5
  exact h5.symm

theorem heisO_neg_cancel (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (x : WO S T) (g : WO S T → ℂ) :
    heisO ψ S T x (heisO ψ S T (-x) g) = g := by
  rw [GlobalTheory.SplitScalar.heisO_heisO, add_neg_cancel, GlobalTheory.SplitScalar.heisO_zero, symplOH_self, AddChar.map_zero_eq_one,
    one_smul]

theorem line_step {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ)
    (hf₁ : IsThetaFunO ψ B.V₀ S f₁) (hf₂ : IsThetaFunO ψ S B'.V₀ f₂) (y : WO B.L S) (w : WO S B'.L)
    (hy : ((B.o.resS S).symm (0, y)).map (infPart D) = 0)
    (hk : (-(B.o.resS S).symm (0, l.κ S w)).map (infPart D) = 0) (c : ℂ)
    (hc : GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y - l.κ S w)) f₁) f₂ =
      c • GlobalTheory.Unf.contr l S vL f₁ f₂) :
    GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) (heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, w)) f₂) =
      (ψ (symplOH B.V₀ S (-(B.o.resS S).symm (0, l.κ S w)) ((B.o.resS S).symm (0, y))) * c) •
        GlobalTheory.Unf.contr l S vL f₁ f₂ := by
  have hth : IsThetaFunO ψ B.V₀ S (heisO ψ B.V₀ S (-(B.o.resS S).symm (0, l.κ S w))
      (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁)) :=
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 hk (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 hy hf₁)
  have hmove := GlobalTheory.T.besselLineContraction_heisenberg_invariant D ψ hψ ρ σ B B' l S vL _ f₂ hth hf₂ w
  rw [heisO_neg_cancel] at hmove
  rw [hmove, GlobalTheory.SplitScalar.heisO_heisO, contr_smul_left]
  have he : -(B.o.resS S).symm (0, l.κ S w) + (B.o.resS S).symm (0, y) = (B.o.resS S).symm (0, y - l.κ S w) := by
    rw [← map_neg, ← map_add, Prod.neg_mk, neg_zero, Prod.mk_add_mk, zero_add, neg_add_eq_sub]
  rw [he, hc, smul_smul]

open Classical in

def cstL (ψ : AddChar (AF D.host.F) ℂ) {ρ : ℕ} (B : BesLev D ρ) (S : HSp D) (M : Lat B.V₀) (LS : Lat S) (P : Pl D → Prop)
    (y : WO B.L S) : ℂ :=
  if (B.o.resS S).symm (0, y) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P then
    (if h : ∃ c : ℂ, ∀ f, Vac ψ B.V₀ S M LS P f → heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f = c • f
      then h.choose else 0) else 0

def coefL (ψ : AddChar (AF D.host.F) ℂ) {ρ σ : ℕ} (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D)
    (M : Lat B.V₀) (LS : Lat S) (P : Pl D → Prop) (u : WO B.V₀ S) (u' : WO S B'.V₀) : ℂ :=
  ψ (symplOH B.V₀ S (-(B.o.resS S).symm (0, l.κ S (B'.o.resT S u').2)) ((B.o.resS S).symm (0, (B.o.resS S u).2))) *
    cstL ψ B S M LS P ((B.o.resS S u).2 - l.κ S (B'.o.resT S u').2)

set_option maxHeartbeats 2000000 in
theorem contrOp : ∀ D : D7, ContrOp D := by
  intro D k _ _ _ _ ι p I P hP n' n'' _ _ _ _ ψ hψ ρ σ B B' l S vL α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr e₁ e₂ he₁ he₂
  classical
  have key : ∀ y, MxAt P y → ∀ f₁ f₂, Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ →
      GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂ =
        cstL ψ B S M LS P y • GlobalTheory.Unf.contr l S vL f₁ f₂ := by
    intro y hy f₁ f₂ h₁ h₂
    by_cases hin : (B.o.resS S).symm (0, y) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P
    · have hex : ∃ c : ℂ, ∀ f, Vac ψ B.V₀ S M LS P f → heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f = c • f := by
        obtain ⟨c, hc⟩ := GlobalTheory.T.halfGenerated_point_acts_scalar_on_latticeVacua D ψ B.V₀ S _ _ (GlobalTheory.T.homLatticeCompletion_le_closure_isotropicHalves D k ι p I P hP B.V₀ S _ _ _ hin)
        exact ⟨c, fun f hf => hc f hf.2⟩
      have hcst : cstL ψ B S M LS P y = hex.choose := by simp only [cstL, if_pos hin, dif_pos hex]
      rw [hcst, hex.choose_spec f₁ h₁, contr_smul_left]
    · have hcst : cstL ψ B S M LS P y = 0 := by simp only [cstL, if_neg hin]
      rw [hcst, zero_smul, GlobalTheory.T.thetaLine_translate_off_lattice_kills_contraction D k ι p I P hP n' n'' ψ hψ ρ σ B B' l S vL α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr
        y hy hin f₁ f₂ h₁ h₂]
  let s := e₁.support ×ˢ e₂.support
  refine ⟨⟨s.card, fun i => Finsupp.single (B.o.resS S (s.equivFin.symm i).1.1).1
      (e₁ (s.equivFin.symm i).1.1 * e₂ (s.equivFin.symm i).1.2 *
        coefL ψ B B' l S M LS P (s.equivFin.symm i).1.1 (s.equivFin.symm i).1.2),
    fun i => Finsupp.single (B'.o.resT S (s.equivFin.symm i).1.2).1 1⟩, ?_, ?_⟩
  · intro i
    have hq := (s.equivFin.symm i).2
    rw [Finset.mem_product] at hq
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
      exact mxAt_mul_right (he₁ _ hq.1) _
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
      exact mxAt_mul_left _ (he₂ _ hq.2)
  intro f₁ f₂ h₁ h₂
  have hth₁ : ∀ u, MxAt P u → IsThetaFunO ψ B.V₀ S (heisO ψ B.V₀ S u f₁) := fun u hu =>
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_mxAt hu) h₁.1
  have hth₂ : ∀ u, MxAt P u → IsThetaFunO ψ S B'.V₀ (heisO ψ S B'.V₀ u f₂) := fun u hu =>
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_mxAt hu) h₂.1
  have hint : ∀ g₁ g₂, IsThetaFunO ψ B.V₀ S g₁ → IsThetaFunO ψ S B'.V₀ g₂ → ∀ (u : WO B.A S) (v : WO S B'.A),
      IntegrableOn (fun x => g₂ ((B'.o.resT S).symm (v, x)) * g₁ ((B.o.resS S).symm (u, l.κ S x))) vL.𝓕 vL.μ := by
    intro g₁ g₂ hg₁ hg₂ u v
    obtain ⟨hc, hp⟩ := GlobalTheory.T.theta_contraction_integrand_continuous_periodic D ρ σ B B' l S ψ g₁ g₂ hg₁ hg₂
    exact (GlobalTheory.Unf.ParCont.parCont D B'.L.rank S.rank vL (WO B.A S × WO S B'.A)
      (fun x q => g₂ ((B'.o.resT S).symm (q.2, x)) * g₁ ((B.o.resS S).symm (q.1, l.κ S x))) hc
      (fun γ' hγ x q => hp γ' hγ x q.1 q.2)).1 (u, v)
  have hLR : ∀ (g₁ : WO B.V₀ S → ℂ) (g₂ : WO S B'.V₀ → ℂ) (b : WO B.A S) (b' : WO S B'.A),
      GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (b, 0)) g₁) (heisO ψ S B'.V₀ ((B'.o.resT S).symm (b', 0)) g₂) =
        fun u₀ v₀ => heisO ψ B.A S b (fun u'' => heisO ψ S B'.A b' (GlobalTheory.Unf.contr l S vL g₁ g₂ u'') v₀) u₀ := by
    intro g₁ g₂ b b'
    funext u₀ v₀
    rw [← GlobalTheory.ContrComb.heis_left ψ l S vL g₁ _ b u₀ v₀]
    congr 1
    funext u''
    rw [GlobalTheory.ContrComb.heis_right]
  have heL : ∀ z : WO B.L S, MxAt P z → MxAt P ((B.o.resS S).symm (0, z)) := by
    intro z hz
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
    exact mxAt_mul_right hz _
  have pair : ∀ u, MxAt P u → ∀ u', MxAt P u' →
      GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S u f₁) (heisO ψ S B'.V₀ u' f₂) =
        fun u₀ v₀ => coefL ψ B B' l S M LS P u u' * heisO ψ B.A S (B.o.resS S u).1
          (fun u'' => heisO ψ S B'.A (B'.o.resT S u').1 (GlobalTheory.Unf.contr l S vL f₁ f₂ u'') v₀) u₀ := by
    intro u hu u' hu'
    have hsL : u = (B.o.resS S).symm ((B.o.resS S u).1, 0) + (B.o.resS S).symm (0, (B.o.resS S u).2) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, AddEquiv.symm_apply_apply]
    have hsR : u' = (B'.o.resT S).symm ((B'.o.resT S u').1, 0) + (B'.o.resT S).symm (0, (B'.o.resT S u').2) := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, AddEquiv.symm_apply_apply]
    have hoL : symplO B.V₀ S ((B.o.resS S).symm ((B.o.resS S u).1, 0)) ((B.o.resS S).symm (0, (B.o.resS S u).2)) = 0 := by
      rw [B.o.symplO_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.SplitScalar.symplO_zero_right,
        GlobalTheory.SplitScalar.symplO_zero_left, add_zero]
    have hoR : symplO S B'.V₀ ((B'.o.resT S).symm ((B'.o.resT S u').1, 0)) ((B'.o.resT S).symm (0, (B'.o.resT S u').2)) = 0 := by
      rw [B'.o.symplO_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.SplitScalar.symplO_zero_right,
        GlobalTheory.SplitScalar.symplO_zero_left, add_zero]
    have hy : MxAt P (B.o.resS S u).2 := mxAt_mul_right hu _
    have hw : MxAt P (B'.o.resT S u').2 := mxAt_mul_left _ hu'
    have hkw : MxAt P (l.κ S (B'.o.resT S u').2) := GlobalTheory.T.besselLink_kappa_preserves_supported_matrices D ρ B B'.L B'.ζ l S P _ hw
    have hline := line_step ψ hψ l S vL f₁ f₂ h₁.1 h₂.1 (B.o.resS S u).2 (B'.o.resT S u').2 (fin_of_mxAt (heL _ hy))
      (fin_of_mxAt (mxAt_neg (heL _ hkw))) _ (key _ (mxAt_sub hy hkw) f₁ f₂ h₁ h₂)
    have e1 : heisO ψ B.V₀ S u f₁ = heisO ψ B.V₀ S ((B.o.resS S).symm ((B.o.resS S u).1, 0))
        (heisO ψ B.V₀ S ((B.o.resS S).symm (0, (B.o.resS S u).2)) f₁) := by
      rw [← GlobalTheory.SplitScalar.heisO_add_of_orth ψ _ _ hoL, ← hsL]
    have e2 : heisO ψ S B'.V₀ u' f₂ = heisO ψ S B'.V₀ ((B'.o.resT S).symm ((B'.o.resT S u').1, 0))
        (heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, (B'.o.resT S u').2)) f₂) := by
      rw [← GlobalTheory.SplitScalar.heisO_add_of_orth ψ _ _ hoR, ← hsR]
    rw [e1, e2, hLR, hline]
    funext u₀ v₀
    simp only [coefL, heisO, Pi.smul_apply, smul_eq_mul]
    ring
  funext u₀ v₀
  have hexp : GlobalTheory.Unf.contr l S vL (comb ψ _ _ e₁ f₁) (comb ψ _ _ e₂ f₂) u₀ v₀ =
      ∑ u' ∈ e₂.support, ∑ u ∈ e₁.support, (e₂ u' * e₁ u) *
        GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S u f₁) (heisO ψ S B'.V₀ u' f₂) u₀ v₀ := by
    simp only [GlobalTheory.Unf.contr, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul_sum]
    have hI : ∀ u' ∈ e₂.support, ∀ u ∈ e₁.support, IntegrableOn (fun x =>
        e₂ u' * heisO ψ S B'.V₀ u' f₂ ((B'.o.resT S).symm (v₀, x)) *
          (e₁ u * heisO ψ B.V₀ S u f₁ ((B.o.resS S).symm (u₀, l.κ S x)))) vL.𝓕 vL.μ := by
      intro u' hu' u hu
      refine Integrable.congr ((hint _ _ (hth₁ u (he₁ u hu)) (hth₂ u' (he₂ u' hu')) u₀ v₀).const_mul (e₂ u' * e₁ u))
        (ae_of_all _ fun x => ?_)
      simp only
      ring
    rw [integral_finset_sum _ fun u' hu' => integrable_finset_sum _ fun u hu => hI u' hu' u hu]
    refine Finset.sum_congr rfl fun u' hu' => ?_
    rw [integral_finset_sum _ fun u hu => hI u' hu' u hu]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hexp, Finset.sum_comm]
  simp only [BiOp.app, Finset.sum_apply]
  rw [Equiv.sum_comp s.equivFin.symm (fun q : s => biComb ψ B.A S B'.A
      (Finsupp.single (B.o.resS S q.1.1).1 (e₁ q.1.1 * e₂ q.1.2 * coefL ψ B B' l S M LS P q.1.1 q.1.2))
      (Finsupp.single (B'.o.resT S q.1.2).1 1) (GlobalTheory.Unf.contr l S vL f₁ f₂) u₀ v₀),
    Finset.sum_coe_sort s (fun q => biComb ψ B.A S B'.A
      (Finsupp.single (B.o.resS S q.1).1 (e₁ q.1 * e₂ q.2 * coefL ψ B B' l S M LS P q.1 q.2))
      (Finsupp.single (B'.o.resT S q.2).1 1) (GlobalTheory.Unf.contr l S vL f₁ f₂) u₀ v₀), Finset.sum_product]
  refine Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun u' hu' => ?_
  rw [pair u (he₁ u hu) u' (he₂ u' hu'), biComb_single]
  ring

end GlobalTheory.FinPl.ContrOpProof
