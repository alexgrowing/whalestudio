import Formalism.LocalToGlobal.InertKernelTheory.OneCopyTh1S
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ReBase
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.RenameBlockSingleVariableSeries
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.SubstSingleVar
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ConstantCoeffInVarEqZero
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.CoeffSubstLgFOfDegreeOne
import Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.ScaledNorms.GcmHostPf

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.KerInert

namespace MMScale

open NumberField Formalism.BasicNotions Formalism.L2.Ker Classical
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (CmOK cmL matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual StdData Th alphaQ kernel4 tens4)
open Formalism.L2.DIV.C.X (gcm_mem_map_smul gcm_relIdx_map_smul gcm_opU_scale gcm_alphaQ_scale gcm_dualLat_scale gcm_matH_scale
  blockFour_smul gcm_stdH_scale gcm_stdLat_scale gcm_imgLat_scale gcm_scalePair_scalePair gcm_kernel4_scale)

theorem thetaU_smul {K : Type} [Field K] (ι : ℂ →+* K) {lg : PowerSeries K}
    (hlg : PowerSeries.constantCoeff lg = 0) {n : Type} [Fintype n] [DecidableEq n] (B' : Matrix n n K)
    (s : ℂ) (G : (n → ℂ) → ℂ) (hG : AnalyticAt ℂ G 0) :
    Formalism.L2.Th1.H.thetaU ι lg B' (fun z => G (s • z)) =
      MvPowerSeries.subst (fun i => ∑ j, MvPowerSeries.C (ι s * B' i j) * (at1 j lg : MvPowerSeries n K))
        (MvPowerSeries.map ι (Formalism.L2.Th1.H.taylorMv G)) := by
  have ha : MvPowerSeries.HasSubst (fun i => ∑ j, MvPowerSeries.C (B' i j) * (at1 j lg : MvPowerSeries n K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      Formalism.L2.Th1.H.FormalGroupLawNegation.cc_lin (B' i) fun j => Formalism.L2.Th1.E.CompatibleChartOperations.constantCoeff_inVar_eq_zero j hlg
  have hb : MvPowerSeries.HasSubst (fun i => ∑ j, MvPowerSeries.C (((Matrix.diagonal fun _ : n => s).map ι) i j) *
      (MvPowerSeries.X j : MvPowerSeries n K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      Formalism.L2.Th1.H.FormalGroupLawNegation.cc_lin _ fun j => MvPowerSeries.constantCoeff_X _
  have hmv : (fun z : n → ℂ => G (s • z)) = fun w => G ((Matrix.diagonal fun _ : n => s).mulVec w) := by
    funext w
    congr 1
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl
  unfold Formalism.L2.Th1.H.thetaU
  rw [hmv, Formalism.L2.Th1.H.taylorMvComp n n _ G hG, Formalism.L2.Th1.H.FormalGroupLawNegation.map_linSubst]
  unfold Formalism.L2.Th1.H.linSubst
  rw [MvPowerSeries.subst_comp_subst_apply hb ha]
  congr 1
  funext i
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum, Finset.sum_eq_single i]
  · rw [map_mul, MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_C, MvPowerSeries.subst_X ha, Matrix.map_apply,
      Matrix.diagonal_apply_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, ← map_mul]
  · intro j _ hj
    rw [Matrix.map_apply, Matrix.diagonal_apply_ne _ (Ne.symm hj), map_zero, map_zero, zero_mul, map_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem stdData_cm {a₀ : ℕ} {b₀ c₀ : ℤ} {d : ℕ} (ha : 0 < a₀) (hd : 0 < d) {lam : ℂ} (hlam : lam ≠ 0)
    (hcm : CmOK a₀ b₀ c₀ d) {L : PeriodPair} (hL : L.lattice = (cmL a₀ b₀ d ha hd lam hlam).lattice)
    {ω₀ : ℂ} (hω : (ω₀ - lam * a₀) / 2 ∈ (cmL a₀ b₀ d ha hd lam hlam).lattice) (hn : ω₀ / 2 ∉ L.lattice)
    {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hiso : IsIsom (matH (blk4 h)) (stdH L (Fin 4 × n)) (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
    (hsd : IsSelfDual (matH h) Λ) (hst : ∀ x ∈ Λ, Formalism.L2.Th1.F.cmTheta b₀ d • x ∈ Λ)
    (i1 : relIdx (stdLat L (Fin 4 × n)) (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ≠ 0)
    (i2 : relIdx (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) (stdLat L (Fin 4 × n)) ≠ 0) :
    StdData L ω₀ h Λ (alphaQ (Real.sqrt d / 2) (matH h)) (alphaQ (Real.sqrt d / 2) (stdH L (Fin 4 × n))) g := by
  rw [KS.stdH_congr hL] at hiso ⊢
  rw [ReBase.stdLat_congr hL] at i1 i2
  exact ReBase.stdData_congr hL hω hn
    (Formalism.L2.Th1.H.stdDataCm a₀ b₀ c₀ d ha hd lam hlam hcm.1 hcm.2.1 hcm.2.2.1 n h Λ g hiso hsd hst i1 i2)

end MMScale

open NumberField Formalism.BasicNotions Formalism.L2.Ker Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.H (CmOK cmL matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual StdData Th alphaQ kernel4 tens4)
open Formalism.L2.DIV.C.X (gcm_mem_map_smul gcm_relIdx_map_smul gcm_opU_scale gcm_alphaQ_scale gcm_dualLat_scale gcm_matH_scale
  blockFour_smul gcm_stdH_scale gcm_stdLat_scale gcm_imgLat_scale gcm_scalePair_scalePair gcm_kernel4_scale)

theorem scale_integrality : ScaleInt := by
  intro D cc δ B hcc hδ p _ h5 hj ι c hc g2 g3 ε s2 hLT hg2 hg3 hdisc hε hth g₁ e hI σ hσ hN γ B' hFr t N hN0 hpN ht
  obtain ⟨hiso, hndvd, i2, he, hten⟩ := hI
  obtain ⟨a₀, gg, b₀, c₀, ha, hd, hl, B'', hcm, -, hIs, hlat, -, -, -, hω, -, -⟩ :=
    ReBase.theta_change_of_base D cc δ B hcc
  have i1 : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
      (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ≠ 0 := by
    intro h0
    exact hndvd (h0 ▸ dvd_zero p)

  have hLB : B.L.lattice = (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ) hl).lattice := by
    rw [← hlat, hIs.1]
  have hωB : (B.ω₀ - (gg : ℂ) * δ * a₀) / 2 ∈ (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ) hl).lattice := by
    rw [← hIs.2, ← hIs.1, hlat]
    exact hω
  have hsd := Kap.kap_selfDual_lamM B hcc hδ
  have hst := Kap.kap_stable_lamM B b₀ (Kap.kap_odd hcm)

  have S1 : StdData B.L B.ω₀ (hOne B.L D.what₂.Tau) B.lamM
      (alphaQ (Real.sqrt D.host.d / 2) (matH (hOne B.L D.what₂.Tau)))
      (alphaQ (Real.sqrt D.host.d / 2) (stdH B.L (Fin 4 × D.what₂.Tau))) g₁ :=
    MMScale.stdData_cm ha hd hl hcm hLB hωB (Base.half_not_mem B) _ _ g₁ hiso hsd hst i1 i2

  have hH' := gcm_matH_scale c (hOne B.L D.what₂.Tau)
  have hcmL : cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ * c) (mul_ne_zero hl hc) =
      Formalism.L2.Th1.F.scalePair (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ) hl) c hc :=
    (gcm_scalePair_scalePair _ ((gg : ℂ) * δ) c hl hc).symm
  have hL2 : (Formalism.L2.Th1.F.scalePair B.L c hc).lattice =
      (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ * c) (mul_ne_zero hl hc)).lattice := by
    rw [hcmL]
    ext z
    rw [(Formalism.L2.Th1.F.homogeneity _ c hc).1, (Formalism.L2.Th1.F.homogeneity _ c hc).1, hLB]
  have hω2 : (c * B.ω₀ - (gg : ℂ) * δ * c * a₀) / 2 ∈
      (cmL a₀ b₀ D.host.d ha hd ((gg : ℂ) * δ * c) (mul_ne_zero hl hc)).lattice := by
    rw [hcmL, (Formalism.L2.Th1.F.homogeneity _ c hc).1]
    have e1 : c⁻¹ * ((c * B.ω₀ - (gg : ℂ) * δ * c * a₀) / 2) = (B.ω₀ - (gg : ℂ) * δ * a₀) / 2 := by
      field_simp
    rw [e1]
    exact hωB
  have hn2 : c * B.ω₀ / 2 ∉ (Formalism.L2.Th1.F.scalePair B.L c hc).lattice := by
    rw [(Formalism.L2.Th1.F.homogeneity _ c hc).1]
    have e1 : c⁻¹ * (c * B.ω₀ / 2) = B.ω₀ / 2 := by
      field_simp
    rw [e1]
    exact Base.half_not_mem B
  have hiso2 : IsIsom (matH (blk4 (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau)))
      (stdH (Formalism.L2.Th1.F.scalePair B.L c hc) (Fin 4 × D.what₂.Tau))
      (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) := by
    intro x y
    rw [gcm_stdH_scale, blockFour_smul, gcm_matH_scale]
    have := hiso (c⁻¹ • x) (c⁻¹ • y)
    rw [map_smul (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) c⁻¹ x,
      map_smul (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) c⁻¹ y] at this
    exact this
  have hsd2 : IsSelfDual (matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau))
      (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c)) := by
    show Formalism.L2.Th1.H.dualLat _ _ = _
    rw [gcm_dualLat_scale hc hH', hsd]
  have hst2 : ∀ x ∈ B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c),
      Formalism.L2.Th1.F.cmTheta b₀ D.host.d • x ∈ B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c) := by
    intro x hx
    rw [gcm_mem_map_smul hc] at hx ⊢
    rw [smul_comm]
    exact hst _ hx
  have j1 : relIdx (stdLat (Formalism.L2.Th1.F.scalePair B.L c hc) (Fin 4 × D.what₂.Tau))
      (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
        (pow4 (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c)))) =
      relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
        (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) := by
    rw [gcm_stdLat_scale, gcm_imgLat_scale _ hc, gcm_relIdx_map_smul hc]
  have j2 : relIdx (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
        (pow4 (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c))))
      (stdLat (Formalism.L2.Th1.F.scalePair B.L c hc) (Fin 4 × D.what₂.Tau)) =
      relIdx (imgLat (g₁ : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
        (stdLat B.L (Fin 4 × D.what₂.Tau)) := by
    rw [gcm_stdLat_scale, gcm_imgLat_scale _ hc, gcm_relIdx_map_smul hc]
  have S2 := MMScale.stdData_cm ha hd (mul_ne_zero hl hc) hcm hL2 hω2 hn2 _ _ g₁ hiso2 hsd2 hst2
    (j1 ▸ i1) (j2 ▸ i2)

  have hspec := B.thMM_spec (B.stdOK hcc hδ)
  have hmem : B.thMM ∈ Th (matH (hOne B.L D.what₂.Tau)) (alphaQ (Real.sqrt D.host.d / 2) (matH (hOne B.L D.what₂.Tau)))
      B.lamM := hspec.1
  have hmem2 : (fun x => B.thMM (c⁻¹ • x)) ∈ Th (matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau))
      (alphaQ (Real.sqrt D.host.d / 2) (matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau)))
      (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c)) := by
    refine ⟨fun z _ => ?_, fun x hx z => ?_⟩
    · have hlin : AnalyticAt ℂ (fun w : D.what₂.Tau → ℂ => c⁻¹ • w) z :=
        (analyticAt_id (𝕜 := ℂ)).const_smul (c := c⁻¹)
      exact AnalyticAt.comp (f := fun w : D.what₂.Tau → ℂ => c⁻¹ • w) (hmem.1 (c⁻¹ • z) (Set.mem_univ _)) hlin
    · show alphaQ _ (matH _) x * Formalism.L2.Th1.H.opU (matH _) x (fun w => B.thMM (c⁻¹ • w)) z = B.thMM (c⁻¹ • z)
      rw [gcm_alphaQ_scale hH', gcm_opU_scale hH']
      exact hmem.2 _ ((gcm_mem_map_smul hc B.lamM x).1 hx) _
  have hF1 := (Formalism.L2.Th1.H.product_theta_mem' _ B.ω₀ (Fin 4 × D.what₂.Tau) S1.per S1.half _ S1.betaStd).1.2
  have hten2 : tens4 (fun x => B.thMM (c⁻¹ • x)) = e • kernel4 (Formalism.L2.Th1.F.scalePair B.L c hc) (c * B.ω₀)
      (B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c))
      (alphaQ (Real.sqrt D.host.d / 2) (stdH (Formalism.L2.Th1.F.scalePair B.L c hc) (Fin 4 × D.what₂.Tau))) g₁ := by
    funext z
    have ht0 : tens4 (fun x => B.thMM (c⁻¹ • x)) z = tens4 B.thMM (c⁻¹ • z) := rfl
    rw [ht0, hten, Pi.smul_apply, Pi.smul_apply, gcm_kernel4_scale _ c hc _ _ B.lamM g₁ S1.betaSemi hF1 i1]
    rfl
  have ht2 : (N : ℂ) • (c • t) ∈ B.lamM.map (DistribSMul.toAddMonoidHom (D.what₂.Tau → ℂ) c) := by
    rw [gcm_mem_map_smul hc, smul_comm, inv_smul_smul₀ hc]
    exact ht

  have hK := Formalism.L2.Th1.Top.local_kappa_shape_holds p h5 _ ι g2 g3 ε s2 hLT hg2 hg3 hdisc hε hth (c * B.ω₀) S2.per S2.half
    D.what₂.Tau _ _ _ _ g₁ S2 (by rw [j1]; exact hndvd) e he _ hmem2 hten2 (c • t) N hN0 hpN ht2 σ γ B' hFr
  obtain ⟨σ0, F, -, -, -, -, -, hF, -⟩ := Formalism.L2.Th1.Top.InhA.joint p h5 1 0 0
  have hInt := Formalism.L2.Th1.Top.kappa_integral p h5 g2 g3 ε s2 hg2 hg3 hε hth σ hσ F hF hN D.what₂.Tau _ γ hFr.1 hK

  have hGan : AnalyticAt ℂ (Formalism.L2.Th1.H.opU (matH (hOne B.L D.what₂.Tau)) t B.thMM) 0 :=
    Formalism.L2.Th1.H.opUAnalytic (D.what₂.Tau → ℂ) (matH (hOne B.L D.what₂.Tau)) t B.thMM hmem.1 0 (Set.mem_univ _)
  have hfun : Formalism.L2.Th1.H.opU (matH (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau)) (c • t)
      (fun x => B.thMM (c⁻¹ • x)) = fun z => Formalism.L2.Th1.H.opU (matH (hOne B.L D.what₂.Tau)) t B.thMM (c⁻¹ • z) := by
    funext z
    rw [gcm_opU_scale hH', inv_smul_smul₀ hc]
  have hread : Formalism.L2.Th1.Top.thetaH p ι B' (((Complex.normSq c : ℝ) : ℂ)⁻¹ • hOne B.L D.what₂.Tau) (c • t)
      (fun x => B.thMM (c⁻¹ • x)) =
      ReadTh1 p (fun τ j => (ι c)⁻¹ * B' τ j)
        (MvPowerSeries.map (ι : ℂ →+* ℂ_[p])
          (Formalism.L2.Th1.H.taylorMv (Formalism.L2.Th1.H.opU (matH (hOne B.L D.what₂.Tau)) t B.thMM))) := by
    unfold Formalism.L2.Th1.Top.thetaH ReadTh1
    rw [hfun, MMScale.thetaU_smul (ι : ℂ →+* ℂ_[p]) (Formalism.InvariantFactorPaths.G7.FormalGroupLaws.constantCoeff_lgF p (by omega)) B' c⁻¹ _ hGan]
    simp only [RingEquiv.coe_toRingHom, map_inv₀]
  rw [← hread]
  exact hInt

end Formalism.L2.KerInert
