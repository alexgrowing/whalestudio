import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantTermHeisOAlongStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransvectionSubgroupCocompactHaarFundamentalDoma
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteUnitaryCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKOContinuousAndRatInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLiftCusp

theorem exists_bound {Z H : Type} [Group Z] [TopologicalSpace Z] [MeasurableSpace Z] [Group H] [TopologicalSpace H]
    (Γ : Subgroup Z) (Δ : Subgroup H) (μ : Measure Z) [μ.IsOpenPosMeasure] (𝓕 : Set Z)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hc : IsCompact (closure 𝓕)) (C : Set H) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Δ, ∃ c ∈ C, h = γ * c) (K : Z × H → ℂ) (hK : Continuous K)
    (hinv : ∀ γ ∈ Γ, ∀ δ ∈ Δ, ∀ z h, K (γ * z, δ * h) = K (z, h)) : ∃ B : ℝ, ∀ p, ‖K p‖ ≤ B := by
  obtain ⟨B, hB⟩ := (hc.prod hC).exists_bound_of_continuousOn hK.continuousOn
  refine ⟨B, fun ⟨z, h⟩ => ?_⟩
  obtain ⟨δ, hδ, c, hcC, rfl⟩ := hcov h
  have hae : ∀ᵐ z ∂μ, ‖K (z, δ * c)‖ ≤ B := by
    filter_upwards [h𝓕.ae_covers] with z hz
    obtain ⟨γ, hγ⟩ := hz
    have := hinv γ⁻¹ (inv_mem γ.2) δ hδ (γ * z) c
    rw [inv_mul_cancel_left] at this
    rw [this]
    exact hB _ ⟨subset_closure hγ, hcC⟩
  have hcl : IsClosed {z : Z | ‖K (z, δ * c)‖ ≤ B} :=
    isClosed_le (hK.comp (Continuous.prodMk_left _)).norm continuous_const
  exact hcl.closure_subset (μ.dense_of_ae hae z)

theorem swap_of_bound {Z H : Type} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (μ : Measure Z) (ν : Measure H) (A : Set Z) (B : Set H) (hA : μ A ≠ ⊤) (hB : ν B ≠ ⊤)
    (K : Z × H → ℂ) (hK : Continuous K) (c : ℝ) (hc : ∀ p, ‖K p‖ ≤ c) :
    ∫ z in A, ∫ h in B, K (z, h) ∂ν ∂μ = ∫ h in B, ∫ z in A, K (z, h) ∂μ ∂ν := by
  haveI : IsFiniteMeasure (μ.restrict A) := ⟨by rw [Measure.restrict_apply_univ]; exact hA.lt_top⟩
  haveI : IsFiniteMeasure (ν.restrict B) := ⟨by rw [Measure.restrict_apply_univ]; exact hB.lt_top⟩
  exact integral_integral_swap (f := fun z h => K (z, h))
    (Integrable.of_bound hK.aestronglyMeasurable c (Filter.Eventually.of_forall hc))

theorem continuous_family {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (H : IsWeilDatumO ψ S T χS χT om)
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ))
    (hL : ∀ x, IsThetaFunO ψ S T (L x)) :
    Continuous fun q : (GA D S × GA D T) × X => om q.1 (L q.2) 0 := by
  let b := Module.finBasis ℂ X
  have e : (fun q : (GA D S × GA D T) × X => om q.1 (L q.2) 0) =
      fun q => ∑ i, b.coord i q.2 * om q.1 (L (b i)) 0 := by
    funext q
    conv_lhs => rw [← b.sum_repr q.2, map_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul]
    rfl
  rw [e]
  exact continuous_finset_sum _ fun i _ =>
    ((b.coord i).continuous_of_finiteDimensional.comp continuous_snd).mul
      ((H.om_cont _ (hL _) 0).comp continuous_fst)

theorem zcusp_lift : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → (∀ x h g ξ, IsoVec T ξ → ∃ n : ℕ, 0 < n ∧ ∃ a : Fin n → Fin S.rank → AE D, ∑ k, heisO ψ S T (along S T ξ (a k)) (om (h, g) (L x)) = 0) → ZCusp T (lift om ν 𝓕 fun h => L (F h)) := by
  intro D ψ S T χS χT om H hpos X _ _ _ L hL F hF hFinv ν 𝓕 hν h𝓕 hav ξ hξ μ 𝓖 hμ h𝓖 g
  have i0 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig S.gram
  have i1 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig T.gram
  obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable S
  obtain ⟨_, _, _, _⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable T
  have : BorelSpace (ZI T ξ) := Subtype.borelSpace _
  have : SecondCountableTopology (ZI T ξ) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  obtain ⟨⟨μ₀, 𝓖₀, hμ₀, h𝓖₀, hc₀⟩, hfin, -⟩ := GlobalTheory.TransvMeasure.transvection_measure D θ T hθ ξ hξ
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hpos
  have hG : μ 𝓖 ≠ ⊤ := (hfin μ 𝓖 hμ h𝓖).2
  have hN : ν 𝓕 ≠ ⊤ := GlobalTheory.TransvMeasure.measure_ne_top_of_cocompact (GQ S) hC (fun x => by
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov x
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩) ν h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ]; exact hG.lt_top⟩

  have hint : ∀ f, IsThetaFunO ψ S T f →
      Integrable (fun z : ZI T ξ => om (1, (z : GA D T)) f 0) (μ.restrict 𝓖) := by
    intro f hf
    obtain ⟨hc, hi⟩ := GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om H f hf
    have hK : Continuous fun p : ZI T ξ × GA D S => thetaKO om p.2 (p.1 : GA D T) f :=
      hc.comp (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
    obtain ⟨B, hB⟩ := exists_bound _ (GQ S) μ₀ 𝓖₀ h𝓖₀ hc₀ C hC hcov _ hK
      fun γ hγ δ hδ z h => hi δ hδ γ hγ h z
    exact Integrable.of_bound (hK.comp (Continuous.prodMk_left 1)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun z => hB (z, 1))

  have hin : ∀ h x, ∫ z in 𝓖, thetaKO om h ((z : GA D T) * g) (L x) ∂μ = 0 := by
    intro h x
    have hf : IsThetaFunO ψ S T (om (h, g) (L x)) := H.om_pres _ _ (hL x)
    have e : ∀ z : ZI T ξ, thetaKO om h ((z : GA D T) * g) (L x) = om (1, (z : GA D T)) (om (h, g) (L x)) 0 := by
      intro z
      have h1 : om (h, (z : GA D T) * g) = om (1, (z : GA D T)) * om (h, g) := by
        rw [← map_mul, Prod.mk_mul_mk, one_mul]
      unfold thetaKO
      rw [h1]
      rfl
    simp only [e]
    obtain ⟨n, hn, a, ha⟩ := hav x h g ξ hξ
    have h1 := integral_finset_sum (μ := μ.restrict 𝓖) Finset.univ
      (fun (k : Fin n) _ => hint _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all H.std hf (along S T ξ (a k))))
    have h2 : ∀ z : ZI T ξ,
        ∑ k, om (1, (z : GA D T)) (heisO ψ S T (along S T ξ (a k)) (om (h, g) (L x))) 0 = 0 := by
      intro z
      rw [← Finset.sum_apply, ← map_sum, ha, map_zero]
      rfl
    simp only [h2, GlobalTheory.T.integral_om_heisO_along_eq_integral_om D ψ S T χS χT om H hpos ξ hξ μ 𝓖 hμ h𝓖 _ hf, integral_zero, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left (Nat.cast_ne_zero.2 hn.ne')
  have hK : Continuous fun p : ZI T ξ × GA D S => thetaKO om p.2 ((p.1 : GA D T) * g) (L (F p.2)) :=
    (continuous_family H L hL).comp
      ((continuous_snd.prodMk ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).prodMk
        (hF.comp continuous_snd))
  obtain ⟨B, hB⟩ := exists_bound _ (GQ S) μ₀ 𝓖₀ h𝓖₀ hc₀ C hC hcov _ hK fun γ hγ δ hδ z h => by
    have := (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om H _ (hL (F h))).2 δ hδ γ hγ h (z * g)
    rw [← this, ← mul_assoc]
    simp only [hFinv δ hδ]
    rfl
  have key := swap_of_bound μ ν 𝓖 𝓕 hG hN _ hK B hB
  simp only [hin, integral_zero] at key
  exact key

end GlobalTheory.DefLiftCusp
