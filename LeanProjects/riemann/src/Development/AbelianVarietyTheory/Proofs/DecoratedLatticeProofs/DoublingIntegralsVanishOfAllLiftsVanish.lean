import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqSetIntegralFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteUnitaryQuotientCompactFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepAverageKillsThetaOfDenseFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapSpanDenseHeisenbergStableStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Kill

variable {D : D7}

theorem exists_bound_of_fundamentalDomain {A : HSp D} {m : Measure (GA D A)} [m.IsHaarMeasure] {X K : Set (GA D A)}
    (hX : IsFundamentalDomain (GQ A) X m) (hK : IsCompact K) (hXK : X ⊆ K) {u : GA D A → ℂ} (hu : Continuous u)
    (hi : ∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) : ∃ C : ℝ, ∀ g, ‖u g‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hu.continuousOn
  refine ⟨C, fun g => ?_⟩
  by_contra hg
  push_neg at hg
  have hopen : IsOpen {x | C < ‖u x‖} := isOpen_lt continuous_const hu.norm
  have hpos : 0 < m {x | C < ‖u x‖} := hopen.measure_pos m ⟨g, hg⟩
  have hnull : m {x | C < ‖u x‖} = 0 := by
    have hcov := hX.ae_covers
    rw [ae_iff] at hcov
    refine measure_mono_null (fun x hx => ?_) hcov
    simp only [Set.mem_setOf_eq, not_exists]
    intro γ hγ
    have h1 := hC _ (hXK hγ)
    rw [Subgroup.smul_def, smul_eq_mul, hi _ γ.2] at h1
    exact absurd h1 (not_le.2 hx)
  exact hpos.ne' hnull

theorem thetaKO_rat {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h : GA D T) :
    ∀ γ ∈ GQ S, ∀ g, thetaKO om (γ * g) h f = thetaKO om g h f := fun γ hγ g => by
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by simp
  simp only [thetaKO]
  rw [e, map_mul, Module.End.mul_apply]
  exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ f hf)

theorem continuous_thetaKO {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h : GA D T) :
    Continuous fun g => thetaKO om g h f :=
  (hom.om_cont f hf 0).comp (continuous_id.prodMk continuous_const)

theorem kills_of_noLift : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A W : HSp D) (χA χW : (AE D)ˣ →* Circle)
    (om : WRep A W) (omh : WRep (dblSp A) W), HSpace.SigOK A → HSpace.IsPosDef A → IsWeilDatumO ψ A W χA χW om →
    IsWeilDatumO ψ (dblSp A) W 1 χW omh → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u →
    (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → NoLift ψ om m u → Kills ψ χW omh m u := by
  intro D ψ A W χA χW om omh hsig hpos hom homh m hm u hu hui hno φ hφ h
  haveI := hm
  obtain ⟨-, X, K, hXm, hX, hK, hXK⟩ := GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain D A hsig hpos m hm
  have hTC := GlobalTheory.T.doublingMap_thetaIdentity_any_weilData D ψ A W χA χW om omh hom homh
  obtain ⟨C, hC⟩ := exists_bound_of_fundamentalDomain hX hK hXK hu hui
  have hχ : IsHeckeChar D χW := hom.hecT
  have hχi : IsHeckeChar D χW⁻¹ :=
    ⟨continuous_inv.comp hχ.1, fun x => by rw [MonoidHom.inv_apply, hχ.2 x, inv_one]⟩

  have hEc : Continuous fun g => thetaKO omh g h φ := continuous_thetaKO homh hφ h
  have hEi : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ (dblSp A)) fun g => thetaKO omh g h φ := thetaKO_rat homh hφ h
  have hcu : Continuous fun g => conj (u g) := Complex.continuous_conj.comp hu
  have hcui : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) fun g => conj (u g) := fun γ hγ g => by
    simp only [hui γ hγ g]

  have hFc := Eis.continuous_dblIntegrand (V := A) hχi hEc hcu hcu
  have hFi := Eis.leftInv_dblIntegrand (V := A) hχi hEi hcui hcui
  have hFint : IntegrableOn (Eis.dblIntegrand A χW⁻¹ (fun g => thetaKO omh g h φ) (fun g => conj (u g))
      (fun g => conj (u g))) (X ×ˢ X) (m.prod m) :=
    (hFc.continuousOn.integrableOn_compact (hK.prod hK)).mono_set (Set.prod_mono hXK hXK)
  have hconv := (Eis.dblConv_iff hFi hFc.measurable hX).2 hFint
  show Eis.dblInt A χW⁻¹ m (fun g => thetaKO omh g h φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0
  rw [(hconv.dblInt_eq hX).2, ← Measure.prod_restrict]
  haveI : IsFiniteMeasure (m.restrict X) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (measure_mono hXK).trans_lt hK.measure_lt_top⟩

  set μ : Measure (GA D A × GA D A) := (m.restrict X).prod (m.restrict X) with hμ
  set c : GA D A × GA D A → ℂ := fun g => u g.1 * conj (u g.2) * (χW (detA A g.2) : ℂ) with hc
  set p : GA D A × GA D A → GA D (dblSp A) × GA D W := fun g => (io A g, h) with hp
  have hint : ∀ G : GA D A × GA D A → ℂ, Continuous G → Integrable G μ := fun G hG => by
    rw [hμ, Measure.prod_restrict]
    exact (hG.continuousOn.integrableOn_compact (hK.prod hK)).mono_set (Set.prod_mono hXK hXK)
  have hFeq : ∀ g, Eis.dblIntegrand A χW⁻¹ (fun g => thetaKO omh g h φ) (fun g => conj (u g))
      (fun g => conj (u g)) g = c g * omh (p g) φ 0 := fun g => by
    simp only [Eis.dblIntegrand, hc, hp, thetaKO, MonoidHom.inv_apply, Circle.coe_inv, inv_inv, Complex.conj_conj]
    ring
  simp_rw [hFeq]
  have hcc : Continuous c :=
    ((hu.comp continuous_fst).mul (Complex.continuous_conj.comp (hu.comp continuous_snd))).mul
      (continuous_subtype_val.comp (hχ.1.comp (Eis.continuous_detA.comp continuous_snd)))
  have hcb : ∀ g, ‖c g‖ ≤ C * C := fun g => by
    simp only [hc, norm_mul, Complex.norm_conj, Circle.norm_coe, mul_one]
    exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC g.1))
  have hpc : Continuous p := (continuous_io A).prodMk continuous_const
  have hK' : IsCompact (p '' (K ×ˢ K)) := (hK.prod hK).image hpc
  have hae : ∀ᵐ x ∂μ, p x ∈ p '' (K ×ˢ K) := by
    rw [hμ, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (hXm.prod hXm)] with x hx
    exact ⟨x, Set.prod_mono hXK hXK hx, rfl⟩

  set M : Submodule ℂ (WO (dblSp A) W → ℂ) := Submodule.span ℂ
    {φ | ∃ f₁ f₂, IsThetaFunO ψ A W f₁ ∧ IsThetaFunO ψ A W f₂ ∧ φ = delta A W f₁ f₂} with hM
  have h83 : (∀ g ∈ M, IsThetaFunO ψ (dblSp A) W g) ∧ (∀ g ∈ M, ∀ w, heisO ψ (dblSp A) W w g ∈ M) ∧
      ∀ f, IsThetaFunO ψ (dblSp A) W f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit M f := GlobalTheory.T.doublingMap_span_dense_heisenbergStable D ψ A W hom.std
  obtain ⟨hMθ, hMh, hMlim⟩ := h83

  have hintθ : ∀ g, IsThetaFunO ψ (dblSp A) W g → Integrable (fun x => c x * omh (p x) g 0) μ := fun g hg =>
    hint _ (hcc.mul ((homh.om_cont g hg 0).comp hpc))

  have hup : ∀ f, IsThetaFunO ψ A W f → ∫ g, thetaKO om g h f * u g ∂(m.restrict X) = 0 := fun f hf => by
    have hinv : ∀ γ ∈ GQ A, ∀ g, thetaKO om (γ * g) h f * u (γ * g) = thetaKO om g h f * u g := fun γ hγ g => by
      rw [thetaKO_rat hom hf h γ hγ g, hui γ hγ g]
    rw [← GlobalTheory.ChainOnto.integral_autMeasure_eq_setIntegral D A m X hm hX (fun g => thetaKO om g h f * u g) hinv
      ((continuous_thetaKO hom hf h).mul hu).aestronglyMeasurable]
    exact hno f hf h
  have hkill : ∀ g ∈ M, ∫ x, c x * omh (p x) g 0 ∂μ = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f₁, f₂, h₁, h₂, rfl⟩ := hx
      have e : ∀ x : GA D A × GA D A, c x * omh (p x) (delta A W f₁ f₂) 0 =
          (thetaKO om x.1 h f₁ * u x.1) * conj (thetaKO om x.2 h f₂ * u x.2) := by
        rintro ⟨x₁, x₂⟩
        have t := ((hTC f₁ f₂ h₁ h₂).2 x₁ x₂ h).2
        have hz : (χW (detA A x₂) : ℂ) ≠ 0 := Circle.coe_ne_zero _
        change c (x₁, x₂) * thetaKO omh (io A (x₁, x₂)) h (delta A W f₁ f₂) = _
        rw [t, Circle.coe_inv, hc]
        simp only [map_mul]
        field_simp
      simp_rw [e]
      rw [hμ, integral_prod_mul (fun g => thetaKO om g h f₁ * u g) (fun g => conj (thetaKO om g h f₂ * u g)),
        hup f₁ h₁, zero_mul]
    | zero => simp
    | add x y hx hy ihx ihy =>
      simp only [map_add, Pi.add_apply, mul_add]
      rw [integral_add (hintθ x (hMθ x hx)) (hintθ y (hMθ y hy)), ihx, ihy, add_zero]
    | smul a x hx ih =>
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_left_comm _ a]
      rw [integral_const_mul, ih, mul_zero]
  exact GlobalTheory.T.weilRep_average_kills_theta_of_dense_family D ψ (dblSp A) W 1 χW omh homh (GA D A × GA D A) μ p c (p '' (K ×ˢ K)) hpc hcc ⟨C * C, hcb⟩ hK'
    hae M hMθ hMh hkill φ hφ (hMlim φ hφ)

end GlobalTheory.Core.Rk.Kill

end
