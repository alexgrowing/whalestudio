import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem comb_sum_mul (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) {n : ℕ} (a : Fin n → ℂ)
    (F : Fin n → WO S T → ℂ) :
    comb ψ S T c (fun w => ∑ i, a i * F i w) = fun w => ∑ i, a i * comb ψ S T c (F i) w := by
  funext w
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => by ring

theorem comb_pureTensorO (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS sT BS BT) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (c : WO S T →₀ ℂ)
    (hc : IsFinComb c) (P : PolF D T.rank S.rank) :
    comb ψ S T c (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (comb ψ S T c f) P := by
  let e := c.support.equivFin
  have key := (GlobalTheory.T.heisenberg_combination_comm_fockPolynomialVectors D ψ θ S T hψ hθ sS sT BS BT f hf c.support.card (fun i => c (e.symm i).1)
    (fun i => (e.symm i).1) (fun i => hc _ (e.symm i).2) P).1
  have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ c.support, c u • g u = ∑ i, c (e.symm i).1 • g (e.symm i).1 := by
    intro g
    rw [← Finset.sum_coe_sort c.support]
    exact (Equiv.sum_comp e.symm (fun u : c.support => c u.1 • g u.1)).symm
  simp only [comb]
  rw [h1, h1]
  exact key

theorem integrableOn_kernel {S T : HSp D} (hS : CoCpt S) (v : Vol S) {ψ : AddChar (AF D.host.F) ℂ}
    {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hw : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {φ : GA D S → ℂ} (hφ : IsContAut S φ) (h : GA D T) :
    IntegrableOn (fun g => om (g, h) f 0 * φ g) v.𝓕 v.μ := by
  have hc : Continuous fun g : GA D S => om (g, h) f 0 :=
    (hw.om_cont f hf 0).comp (by fun_prop : Continuous fun g : GA D S => (g, h))
  refine (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hS v Unit (fun g _ => om (g, h) f 0 * φ g) ((hc.mul hφ.2).comp continuous_fst) ?_).1 ()
  intro γ hγ g _
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply, hw.om_aut γ hγ 1 (one_mem _) _ (hw.om_pres _ _ hf), hφ.1 γ hγ g]

theorem biLift_biComb_fockSum : ∀ (D : D7), BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → ∀ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank) (C : WO A S → WO S A' → ℂ), (∀ u v, C u v = ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u * pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v) → ∀ φ, IsContAut A φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) = ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ) := by
  intro D _ _ hL ψ θ hθ A S A' x y z hx hy hz k k' hk hk' n P P' C hC φ hφ
  obtain ⟨χA, χS, hwA⟩ := hk.weil
  obtain ⟨χS', χA', hwB⟩ := hk'.weil
  have hX : ∀ i, IsThetaFunO ψ A S (k.pt ψ θ x y (P i)) := fun i => (hL ψ θ hθ A S x y hx hy k hk (P i)).1
  have hY : ∀ i, IsThetaFunO ψ S A' (k'.pt ψ θ y z (P' i)) := fun i => (hL ψ θ hθ S A' y z hy hz k' hk' (P' i)).1
  have hLc : ∀ i, IsContAut S (k.lift ψ θ x y (P i) φ) := fun i => (hL ψ θ hθ A S x y hx hy k hk (P i)).2.1 φ hφ
  have hcX : ∀ i, comb ψ A S k.c (pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i)) = k.pt ψ θ x y (P i) := fun i =>
    comb_pureTensorO ψ θ A S hwA.std hθ _ _ _ _ k.vac hk.vac.2.theta k.c hk.fin (P i)
  have hcY : ∀ i, comb ψ S A' k'.c (pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i)) = k'.pt ψ θ y z (P' i) :=
    fun i => comb_pureTensorO ψ θ S A' hwB.std hθ _ _ _ _ k'.vac hk'.vac.2.theta k'.c hk'.fin (P' i)
  have hbi : biComb ψ A S A' k.c k'.c C = fun u v => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v := by
    funext u v
    simp only [biComb]
    have e1 : (fun u' => comb ψ S A' k'.c (C u') v) = fun u' => ∑ i,
        comb ψ S A' k'.c (pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i)) v *
          pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u' := by
      funext u'
      have : C u' = fun v => ∑ i, pureTensorO ψ θ A S x.s y.s x.B y.B k.vac (P i) u' *
          pureTensorO ψ θ S A' y.s z.s y.B z.B k'.vac (P' i) v := funext (hC u')
      rw [this, comb_sum_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e1, comb_sum_mul]
    simp only [hcX, hcY]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hint : ∀ h₀ h₁ h₂, k'.om (h₁, h₂) (fun v => k.om (h₀, h₁)
      (fun u => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v) 0) 0 =
      ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 * k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 := by
    intro h₀ h₁ h₂
    have e1 : ∀ v, (fun u => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v) =
        ∑ i, k'.pt ψ θ y z (P' i) v • k.pt ψ θ x y (P i) := by
      intro v; funext u; simp [Finset.sum_apply, mul_comm]
    have e2 : (fun v => k.om (h₀, h₁) (fun u => ∑ i, k.pt ψ θ x y (P i) u * k'.pt ψ θ y z (P' i) v) 0) =
        ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 • k'.pt ψ θ y z (P' i) := by
      funext v; rw [e1 v, map_sum]; simp [Finset.sum_apply, mul_comm]
    rw [e2, map_sum]; simp [Finset.sum_apply]
  funext h₂
  have hin : ∀ h₁, ∫ h₀ in x.vol.𝓕, φ h₀ * ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 *
      k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 ∂x.vol.μ =
      ∑ i, k.lift ψ θ x y (P i) φ h₁ * k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 := by
    intro h₁
    have e : (fun h₀ => φ h₀ * ∑ i, k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 *
        k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0) = fun h₀ => ∑ i,
          k.om (h₀, h₁) (k.pt ψ θ x y (P i)) 0 * φ h₀ * k'.om (h₁, h₂) (k'.pt ψ θ y z (P' i)) 0 := by
      funext h₀; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, integral_finset_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_mul_const]
      rfl
    · intro i _
      exact (integrableOn_kernel hx.cpt x.vol hwA (hX i) hφ h₁).mul_const _
  simp only [biLift, hbi, hint, hin, Finset.sum_apply]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [KerDat.lift, liftT_apply]
    congr 1
    funext h₁
    exact mul_comm _ _
  · intro i _
    have := (integrableOn_kernel hy.cpt y.vol hwB (hY i) (hLc i) h₂)
    exact Integrable.congr this (Filter.Eventually.of_forall fun h₁ => mul_comm _ _)

end GlobalTheory.SeeSaw
