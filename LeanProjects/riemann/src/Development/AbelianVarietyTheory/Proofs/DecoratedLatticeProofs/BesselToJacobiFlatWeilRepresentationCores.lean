import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaIntegrandLocallyUniformMajorant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmIntegralComm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.FlatCommBF

variable {D : D7}

theorem sFinite_of_haar {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (ν : Measure G) (h : ν.IsHaarMeasure) : SFinite ν := by
  haveI := h
  infer_instance

theorem continuous_psiUni (ψ : AddChar (AF D.host.F) ℂ) (hψ : Continuous ψ) (ρ : ℕ) :
    Continuous fun u : UX D ρ => psiUni ψ u.1 := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hv : Continuous fun u : UX D ρ => u.1.1 := Units.continuous_val.comp continuous_subtype_val
  unfold psiUni psiE upSum
  refine hψ.comp (ht.comp ?_)
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  split_ifs
  · exact (continuous_apply j).comp ((continuous_apply i).comp hv)
  · exact continuous_const

theorem jacT_integral (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (y : Mx D S.rank ρ) (n : GA D T) {U : Type} [MeasurableSpace U] (m : Measure U) (G : U → WO S T₀ → ℂ)
    (w : WO S T₀) : jacT ψ d S y n (fun w' => ∫ u, G u w' ∂m) w = ∫ u, jacT ψ d S y n (G u) w ∂m := by
  simp only [jacT, heisO, Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, integral_const_mul]

theorem jacT_smul (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (y : Mx D S.rank ρ) (n : GA D T) (c : ℂ) (f : WO S T₀ → ℂ) :
    jacT ψ d S y n (c • f) = c • jacT ψ d S y n f := by
  funext w
  simp only [jacT, heisO, Pi.smul_apply, smul_eq_mul]
  ring

set_option maxHeartbeats 400000 in

theorem flatBF_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → ∀ h₀, ∀ n ∈ radX J.d, ∀ h', flatBF s (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ)) := by
  intro D ψ ρ B J s om' hom' Ψ hΨ h₀ n hn h'
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  obtain ⟨hloc, hsc, -⟩ := GlobalTheory.UnitU.topology D ρ
  haveI := hloc
  haveI := hsc
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : SFinite s.vU.ν := @sFinite_of_haar (UX D ρ) _ _ _ hloc hsc s.vU.ν s.vU.unit.1
  obtain ⟨hbase, -, hx0, -⟩ := GlobalTheory.Unf.base_point D J.W J.W₀ ρ J.d
  have hlin : LinearIndependent D.host.E J.d.e.transpose := hbase.1
  have hev := GlobalTheory.Unf.evalAt_xZero_yZero D ψ ρ B J s om' hom' Ψ hΨ
  have hom1 : s.om 1 Ψ = Ψ := by rw [map_one]; rfl

  have e3 : ∀ u : UX D ρ, evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (1, h') (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
    intro u
    have h := hev.1 u 1 1 (one_mem _) h'
    rw [map_one, one_mul, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one] at h
    rw [h]
    simp only [opA, jacT_one]
    rfl
  have e2 : ∀ u : UX D ρ, evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) = opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ
      (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
    intro u
    have h := hev.1 u 1 n hn h'
    rw [map_one, ← Prod.one_eq_mk, map_one, ← Prod.one_eq_mk, map_one] at h
    exact h

  have hmix := GlobalTheory.MixValues.mixed_values D ψ hstd
  have thev : ∀ Φ, IsThetaFunO ψ B.V J.W Φ → ∀ u : UX D ρ, IsThetaFunO ψ B.V₀ J.W₀
      (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Φ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) :=
    fun Φ hΦ u => hmix.2 B.V₀ J.W J.W₀ ρ J.d s.vT.μ s.vT.𝓕 s.vT.covol _
      (hmix.1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Φ hΦ _) _
  have thom : ∀ p, IsThetaFunO ψ B.V J.W (s.om p Ψ) := fun p => s.weil.om_pres p Ψ hΨ
  have hFL := GlobalTheory.Unf.Flat.flatLaw D ψ hstd B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e hlin
    (yZero B.V₀ ρ (vecB B.o B.ζ))
  have thflat : ∀ p, IsThetaFunO ψ B.V₀ J.W₀ (flatBF s (s.om p Ψ)) := fun p => by
    have h := (hFL _ (thom p)).2
    rw [← hx0] at h
    exact h
  obtain ⟨M, hMi, hM⟩ := GlobalTheory.Unf.flatFun_majorant D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil s.vU J.d.e hlin
    Ψ hΨ {1, (1, J.d.emb0 h'), (1, n * J.d.emb0 h'), (embA B.d B.o h₀, n * J.d.emb0 h')} (Set.toFinite _).isCompact
  simp only [← hx0] at hM
  have bound : ∀ p ∈ ({1, (1, J.d.emb0 h'), (1, n * J.d.emb0 h'), (embA B.d B.o h₀, n * J.d.emb0 h')} :
      Set (GA D B.V × GA D J.W)), ∀ (u : UX D ρ) w, ‖star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om p Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w‖ ≤ M u :=
    fun p hp u w => hM p hp _ w u
  have hmc := GlobalTheory.MixCont.mixed_coords_continuous D ψ B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.χV s.χW s.om s.weil Ψ hΨ
  have hxu : Continuous fun u : UX D ρ => xZero J.d ⬝ u.1.1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  have cont : ∀ p, Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => star (psiUni ψ q.1.1) *
      evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om p Ψ) (xZero J.d ⬝ q.1.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) q.2 := by
    intro p
    have h1 : Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => ((p, xZero J.d ⬝ q.1.1.1, yZero B.V₀ ρ (vecB B.o B.ζ), q.2) :
        (GA D B.V × GA D J.W) × Mx D J.W.rank ρ × Mx D B.V₀.rank ρ × WO B.V₀ J.W₀) :=
      continuous_const.prodMk ((hxu.comp continuous_fst).prodMk (continuous_const.prodMk continuous_snd))
    have h2 := hmc.2.comp h1
    have h3 : Continuous fun q : UX D ρ × WO B.V₀ J.W₀ => star (psiUni ψ q.1.1) :=
      ((continuous_psiUni ψ hstd.1.1 ρ).comp continuous_fst).star
    exact h3.mul h2
  have hci := GlobalTheory.CommInt.om_integral_comm D ψ B.V₀ J.W₀ s.χV s.χW s.om₀ s.weil₀ (UX D ρ) s.vU.ν

  have hF : ∀ u : UX D ρ, (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) = star (psiUni ψ u.1) • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) :=
    fun u => rfl
  have hG : ∀ (u : UX D ρ) w, s.om₀ (1, h') (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) w =
      star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w := by
    intro u w
    rw [hF, map_smul, e3]
    rfl
  have step1 : ∀ w, s.om₀ (1, h') (flatBF s Ψ) w = ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    intro w
    have h := hci (fun u w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) (1, h') M
      (fun u => by rw [hF]; exact GlobalTheory.OrientedHeis.theta_smul _ (thev Ψ hΨ u))
      (by have h := cont 1; rw [hom1] at h; exact h)
      (by simp only [hG]; exact cont _)
      hMi
      (fun u w => ⟨by have h := bound 1 (by simp) u w; rw [hom1] at h; exact h, by rw [hG]; exact bound _ (by simp) u w⟩)
      (by have h := thflat 1; rw [hom1] at h; exact h) w
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => hG u w))

  have hF2 : ∀ u : UX D ρ, (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) =
      star (psiUni ψ u.1) • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := fun u => rfl
  have hG2 : ∀ (u : UX D ρ) w, s.om₀ (B.o.emb (h₀, 1), 1) (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) w =
      star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w := by
    intro u w
    rw [hF2, map_smul, e2, hev.1 u h₀ n hn h']
    rfl
  have step2 : ∀ w, s.om₀ (B.o.emb (h₀, 1), 1) (fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν) w =
      ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    intro w
    have h := hci (fun u w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) (B.o.emb (h₀, 1), 1) M
      (fun u => by rw [hF2]; exact GlobalTheory.OrientedHeis.theta_smul _ (thev _ (thom _) u))
      (cont _)
      (by simp only [hG2]; exact cont _)
      hMi
      (fun u w => ⟨bound _ (by simp) u w, by rw [hG2]; exact bound _ (by simp) u w⟩)
      (thflat _) w
    exact h.trans (integral_congr_ae (Filter.Eventually.of_forall fun u => hG2 u w))

  have hopa : opA ψ J.d B.o B.ζ s.om₀ n h' (flatBF s Ψ) =
      fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν := by
    funext w
    have h1 : s.om₀ (1, h') (flatBF s Ψ) = fun w => ∫ u, star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν :=
      funext step1
    show jacT ψ J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) n (s.om₀ (1, h') (flatBF s Ψ)) w = _
    rw [h1, jacT_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have h2 : (fun w => star (psiUni ψ u.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w) =
        star (psiUni ψ u.1) • s.om₀ (1, h') (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))) := by
      rw [e3]; rfl
    dsimp only
    rw [h2, jacT_smul, e2]
    rfl
  rw [hopa]
  funext w
  exact (step2 w).symm

end GlobalTheory.Unf.FlatCommBF
