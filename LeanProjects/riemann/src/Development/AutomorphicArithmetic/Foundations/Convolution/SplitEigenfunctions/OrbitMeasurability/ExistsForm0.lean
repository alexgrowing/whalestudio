import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbitMeasurability.PerCont
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandsSpan
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ClsBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.CuspRegions.ExCusp
import GroundTheory.AutomorphicForms.GL2.GJGlobalMean

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent

noncomputable section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

private theorem exists_form0 {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    {v : LL μ} (hv : v ∈ cuspidalL2 μ) (h0 : v ≠ 0) :
    ∃ V, IsSummand μ V ∧ ∃ f ∈ formsIn μ V, inner ℂ v (clsL μ f) ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : (⨆ V : {V // IsSummand μ V}, V.1) ≤ (ℂ ∙ v)ᗮ := iSup_le fun V => by
    rw [← (formsIrr K n μ V.1 V.2).2.2.2]
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rintro _ ⟨f, hf, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hc _ V.2 f hf)
  have h2 := Submodule.topologicalClosure_minimal _ h1 (Submodule.isClosed_orthogonal _)
  rw [summandsSpan K n μ] at h2
  exact h0 (inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (h2 hv)))

private theorem oneInt (f : (AutomorphicForm.UPos 2 1 → A ℚ) → ℂ) :
    ∫ y in GroundTheory.Global.fundamentalSet ℚ, f (fun _ => y) ∂GroundTheory.Global.adeleMeasure ℚ =
      ∫ Y in unipFundamentalDomain ℚ 2 1, f Y ∂unipMeasure ℚ 2 1 := by
  letI : Unique (AutomorphicForm.UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
  have hm : MeasurePreserving (MeasurableEquiv.funUnique (AutomorphicForm.UPos 2 1) (A ℚ)) (unipMeasure ℚ 2 1)
      (GroundTheory.Global.adeleMeasure ℚ) := by
    convert measurePreserving_funUnique (GroundTheory.Global.adeleMeasure ℚ) (AutomorphicForm.UPos 2 1)
  rw [← hm.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _)]
  congr 1
  · congr 1
    ext Y
    simp [unipFundamentalDomain, Unique.forall_iff]
  · funext Y
    congr 1
    funext p
    simp [Subsingleton.elim p default]

private theorem unip_eq (y : A ℚ) : (unipGL (fun _ : AutomorphicForm.UPos 2 1 => y) : GL (Fin 2) (A ℚ)) = gl (nU y) := by
  ext i j
  change unipMatrix (fun _ : AutomorphicForm.UPos 2 1 => y) i j = (!![1, y; 0, 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j
  fin_cases i <;> fin_cases j <;> simp [unipMatrix, blockEntry_apply]

private theorem cusp_conj {F : GL (Fin 2) (A ℚ) → ℂ}
    (h : ∀ x, ∫ b in GroundTheory.Global.fundamentalSet ℚ, F (gl (nU b) * x) ∂(GroundTheory.Global.adeleMeasure ℚ) = 0) :
    IsCuspidal (fun x : AdelicGLn.AdelicGL ℚ 2 => starRingEnd ℂ (F x)) := by
  intro r hr hr2 g
  obtain rfl : r = 1 := by omega
  rw [constantTerm, ← oneInt (fun X => starRingEnd ℂ (F (unipGL X * g)))]
  simp only [unip_eq]
  rw [integral_conj, h g, map_zero]

private theorem exists_one {F : GL (Fin 2) (A ℚ) → ℂ} (hF : Bd F) (h0 : F ≠ 0) :
    ∃ x : normOneGL ℚ 2, F (x : AdelicGLn.AdelicGL ℚ 2) ≠ 0 := by
  obtain ⟨g, hg⟩ := Function.ne_iff.1 h0
  refine ⟨retractOne g, ?_⟩
  rw [coe_retractOne, ← centralSection_inv_mul_comm, ← map_inv, hF.cen]
  exact hg

end UpperTheory.ConvolutionTheory.RankTwoDescent.Cp

open UpperTheory.ConvolutionTheory.RankTwoDescent.Cp in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.pairL : UpperTheory.ConvolutionTheory.RankTwoDescent.Cp.PairL := by
  intro μ _ F hF hne hct
  have hfin := Reduction.isFiniteMeasure_quotientMeasure (K := ℚ) (n := 2) μ
  set ψ : AdelicGLn.AdelicGL ℚ 2 → ℂ := fun x => starRingEnd ℂ (F x) with hψdef
  have hψc : Continuous ψ := continuous_star.comp hF.cont
  have hψl : IsLeftInvariant ψ := fun γ g => congrArg (starRingEnd ℂ) (hF.left γ g)
  obtain ⟨C, hC⟩ := hF.bdd
  have hbd : ∃ C, ∀ g ∈ normOneGL ℚ 2, ‖ψ g‖ ≤ C := ⟨C, fun g _ => by simpa [hψdef] using hC g⟩
  have hm := GJGlobal.memLp_cuspQuot_of_bounded μ hψc hψl hbd
  have hv : hm.toLp _ ∈ cuspidalL2 μ := GJGlobal.toLp_cuspQuot_mem_cuspidalL2 μ hψc hψl (cusp_conj hct) hbd
  have hv0 : hm.toLp _ ≠ 0 := fun h => by
    obtain ⟨x, hx⟩ := exists_one hF hne
    have h1 : cuspQuot hψl =ᵐ[quotientMeasure (rationalGLOne ℚ 2) μ] 0 := by
      refine (MemLp.coeFn_toLp hm).symm.trans ?_
      rw [h]
      exact Lp.coeFn_zero _ _ _
    have h2 : (fun y : normOneGL ℚ 2 => ψ y) =ᵐ[μ] 0 := (quasiMeasurePreserving_mk _ μ).ae_eq h1
    have h3 : starRingEnd ℂ (F (x : AdelicGLn.AdelicGL ℚ 2)) = 0 :=
      congrFun ((Continuous.ae_eq_iff_eq μ (hψc.comp continuous_subtype_val) continuous_const).1 h2) x
    exact hx ((map_eq_zero _).1 h3)
  obtain ⟨V, hV, f, hf, hi⟩ := exists_form0 μ hv hv0
  obtain ⟨π, hπ, -⟩ := UpperTheory.ConvolutionTheory.Dr.exCusp ℚ 2 μ V hV
  refine ⟨π, ?_, Fb.ofCusp ℚ 2 f, Fb.mem_carrier.1 (hπ.carrier_eq ▸ hf), fun hz => hi ?_⟩
  · intro φ hφ s g
    rw [← Fb.map_carrier π] at hφ
    obtain ⟨ψ', hψ', rfl⟩ := hφ
    exact (hπ.carrier_eq ▸ hψ' : ψ' ∈ formsIn μ V).1 s g
  · rw [L2.inner_def, ← hz]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hm, (clsBasic ℚ 2 μ).2.2.2 f hf.1] with q e1 e2
    rw [e1, e2, RCLike.inner_apply]
    have e3 : cuspQuot hψl q = ψ (Quotient.out q : normOneGL ℚ 2) := by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [e3]
    simp [hψdef]
