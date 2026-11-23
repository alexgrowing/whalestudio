import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKModuleMapCuspFormsExtendsMultiplicitySpace
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIffStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFinAtZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAndHasSumKAvg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalCoeffSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

noncomputable section

namespace GlobalTheory.AvgCoeff

open MeasureTheory

theorem exists_finset_sep {K : Type} (S : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ S] :
    ∃ T : Finset K, ∀ s ∈ S, (∀ t ∈ T, s t = 0) → s = 0 := by
  classical
  let f : Finset K → Submodule ℂ S := fun T =>
    ⨅ t ∈ T, LinearMap.ker ((LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) t).comp S.subtype)
  obtain ⟨T, -, hT⟩ := (measure fun T => Module.finrank ℂ (f T)).wf.has_min Set.univ ⟨∅, trivial⟩
  refine ⟨T, fun s hs h0 => ?_⟩
  by_contra hne
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
  have hmem : ∀ T' : Finset K, ∀ u : S, u ∈ f T' ↔ ∀ t ∈ T', (u : K → ℂ) t = 0 := fun T' u => by
    simp [f, Submodule.mem_iInf]
  have hle : f (insert t T) ≤ f T := fun u hu =>
    (hmem T u).2 fun t' ht' => (hmem _ u).1 hu t' (Finset.mem_insert_of_mem ht')
  have hlt : f (insert t T) < f T := by
    refine lt_of_le_of_ne hle fun heq => ?_
    have h1 : (⟨s, hs⟩ : S) ∈ f T := (hmem T _).2 h0
    rw [← heq] at h1
    exact ht ((hmem _ _).1 h1 t (Finset.mem_insert_self t T))
  exact hT (insert t T) trivial (Submodule.finrank_lt_finrank_of_lt hlt)

theorem integral_mem {K K' : Type} [MeasurableSpace K'] (μ : Measure K') (S : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ S] (F : K' → K → ℂ) (hF : ∀ k', F k' ∈ S)
    (hi : ∀ k, Integrable (fun k' => F k' k) μ) : (fun k => ∫ k', F k' k ∂μ) ∈ S := by
  obtain ⟨T, hT⟩ := exists_finset_sep S
  let R : S →ₗ[ℂ] (T → ℂ) := LinearMap.pi fun t : T => (LinearMap.proj (R := ℂ) (φ := fun _ : K => ℂ) (t : K)).comp S.subtype
  have hker : LinearMap.ker R = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun u hu => Subtype.ext ?_
    refine hT u u.2 fun t ht => ?_
    have := congrFun hu ⟨t, ht⟩
    simpa [R] using this
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hker
  let b := Pi.basisFun ℂ T
  have hexp : ∀ s ∈ S, s = ∑ t : T, s t • ((L (b t) : S) : K → ℂ) := by
    intro s hs
    have h1 : (⟨s, hs⟩ : S) = L (R ⟨s, hs⟩) := by rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
    have h2 : R ⟨s, hs⟩ = ∑ t : T, s t • b t := by
      conv_lhs => rw [← b.sum_repr (R ⟨s, hs⟩)]
      simp [R, b]
    rw [h2, map_sum] at h1
    have h3 := congrArg (fun u : S => (u : K → ℂ)) h1
    simpa [Submodule.coe_sum, map_smul] using h3
  have : (fun k => ∫ k', F k' k ∂μ) = ∑ t : T, (∫ k', F k' t ∂μ) • ((L (b t) : S) : K → ℂ) := by
    funext k
    have hk : ∀ k', F k' k = ∑ t : T, F k' t * ((L (b t) : S) : K → ℂ) k := fun k' => by
      conv_lhs => rw [hexp (F k') (hF k')]
      simp [Finset.sum_apply]
    simp_rw [hk]
    rw [integral_finset_sum (f := fun (t : T) k' => F k' t * ((L (b t) : S) : K → ℂ) k) Finset.univ
      fun t _ => (hi t).mul_const _]
    simp [Finset.sum_apply, integral_mul_const]
  rw [this]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (L (b t)).2

theorem coeffSpan_finiteDimensional {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  first
  | exact @_root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan
  | exact _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan
  | (apply _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientSpanFiniteDimensional.finiteDimensional_coeffSpan ..)

theorem coeffSpan_mulRight {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) (k' : K)
    {f : K → ℂ} (hf : f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) : (fun k => f (k * k')) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ (GlobalTheory.Published.AutFin.coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ (· * k')) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨ℓ, w, rfl⟩
    exact Submodule.subset_span ⟨ℓ, ρ k' w, funext fun k => by simp [LinearMap.funLeft, map_mul]⟩
  exact this hf

end GlobalTheory.AvgCoeff

namespace GlobalTheory.CuspKFin

open Formalism.REAL GlobalTheory.Published.AutFin GlobalTheory.AvgCoeff

theorem kFinAt_avg_of_kFinAt : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ),
    IsAutFunSm θ N.V ψ → ∀ (τ τ' : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ') → ℂ),
    GlobalTheory.TypeSum.KFinFun (N.M.ε τ') e → GlobalTheory.CuspKFin.KFinAt θ N τ ψ →
    GlobalTheory.CuspKFin.KFinAt θ N τ (GlobalTheory.SeriesToClosure.avg θ N.V τ' (N.M.ε τ') (N.M.fr τ') e ψ) := by
  intro D θ hθ N ψ hψ τ τ' e he hK
  obtain ⟨W, i1, i2, i3, ρ, hρc, hρ⟩ := hK
  refine ⟨W, i1, i2, i3, ρ, hρc, fun x => ?_⟩
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI := coeffSpan_finiteDimensional ρ
  have hec : Continuous e := by
    obtain ⟨F, -, heF, hc, -⟩ := he
    exact hc e heF
  have hAc : Continuous fun k' : Formalism.REAL.KG (N.M.ε τ') => atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') :=
    (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ N.V τ').comp_continuous GlobalTheory.SeriesToClosure.continuous_conjK
      fun k => conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k
  have hmem : ∀ k' : Formalism.REAL.KG (N.M.ε τ'), (fun k => ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ'))) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
    intro k'
    by_cases h : τ' = τ
    · subst h
      have h2 := coeffSpan_mulRight ρ k' (hρ x)
      convert h2 using 2 with k
      rw [mul_assoc]
      congr 2
      simp only [kAt]
      rw [← GlobalTheory.SeriesToClosure.at_mul hθ (N.M.fr_unit τ') (N.M.fr_gram τ')
        (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k)) (GlobalTheory.TypeSum.K_le_UJ (GlobalTheory.TypeSum.toMK_mem_K k'))]
      rfl
    · have hc : ∀ k, kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k * atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') =
          atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ') * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k := fun k =>
        GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ N.V τ τ' (Ne.symm h) _
          (conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k) _ (conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k')
      have h2 := hρ (x * atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ'))
      convert h2 using 2 with k
      rw [mul_assoc, hc, ← mul_assoc]
  have hcont : ∀ k, Continuous fun k' : Formalism.REAL.KG (N.M.ε τ') => e k' * ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ')) := fun k =>
    hec.mul (hψ.cont.comp (continuous_const.mul hAc))
  have key := GlobalTheory.AvgCoeff.integral_mem (muK (N.M.ε τ')) (GlobalTheory.Published.AutFin.coeffSpan ρ)
    (fun k' k => e k' * ψ (x * kAt θ N.V τ (N.M.ε τ) (N.M.fr τ) k *
      atTau θ N.V τ' ((N.M.fr τ')⁻¹ * Formalism.REAL.toMK k' * N.M.fr τ')))
    (fun k' => Submodule.smul_mem _ (e k') (hmem k')) (fun k => GlobalTheory.ExpansionAverage.integrable_K (hcont k))
  exact key

end GlobalTheory.CuspKFin

end
