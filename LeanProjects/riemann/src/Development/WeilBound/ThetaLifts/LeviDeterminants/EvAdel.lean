import Development.WeilBound.ThetaLifts.LeviDeterminants.ModelChangeOf
import Development.WeilBound.ThetaLifts.LeviDeterminants.MapEqOfSmul

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

theorem isEv_bij_of_adel (hA : PositivityTheory.Mix.AdelSt) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {n d r s r' s' : ℕ} {X : Spc F E n} {W : Spc F E d} {M M₁ : Model σ X W} (hB : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) :
    ∃ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e ∧
      Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) := by
  classical
  have hψ := hB.std
  have hr := ratRel_of_good hM hM₁
  have hr' := ratRel_of_good hM₁ hM
  obtain ⟨e₁, ei, ev, hsurj, hmaps, hheis, hSB, hvac, hstd, hpure⟩ :=
    PositivityTheory.Mix.darboux_model_rational_lattice_of hA F E σ B n d X W M r s r' s' hB hX hW hM M₁.co hM₁.rat
  choose c hc0 hc using fun v => vac_line hB hX hW M₁ v (hM₁.vac v) (φ' := ev v (M.vac v)) (hvac v)
  have hc1 : ∀ᶠ v in cofinite, c v = 1 := by
    filter_upwards [hstd, hM₁.std] with v h1 h2
    have h' := hc v
    rw [h1, h2] at h'
    have h := congrFun h' 0
    have hm : (0 : Fin n × Fin d → Fv F v) ∈ {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} :=
      fun i => zero_mem _
    rw [Pi.smul_apply, Set.indicator_of_mem hm, smul_eq_mul] at h
    simpa using h.symm
  have hfin0 : (Function.mulSupport c).Finite := Filter.eventually_cofinite.1 hc1
  have hk : (∏ᶠ v, c v)⁻¹ ≠ 0 := inv_ne_zero (finprod_ne_zero hc0)
  have hstd' : ∀ᶠ v in cofinite, ev v (Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) =
      Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hstd, hM.std] with v h1 h2
    rwa [h2] at h1
  have hpure' : ∀ f φ, (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
      e₁ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) := fun f φ h1 h2 =>
    hpure f φ h1 (by filter_upwards [h2, hM.std] with v e1 e2; rw [e1, e2])
  have hs := surjOn_of_pure e₁ ei ev hsurj (fun v => (hSB v).ge) hstd' hpure'
  have t₁ : Tw B.ψ M.co M₁.co e₁ := ⟨hmaps, hheis,
    Span.comp_mem_adm e₁ ei ev (fun v φ hφ => hSB v ▸ Submodule.mem_map_of_mem hφ) hstd' hpure', exists_ne_of_surjOn hs⟩
  have t := t₁.smul hk
  obtain ⟨e₀, t₀⟩ := twEx hA F B.ψ hψ _ _ _ M₁.co M.co
  obtain ⟨e', t', hl1, hl2⟩ := t.exists_inv hψ t₀ hr hr'
  refine ⟨_, ⟨t.maps, fun z Φ hΦ => ?_, fun u hu => absurd hu (Set.notMem_empty u), ei, fun v => (c v)⁻¹ • ev v, ?_, ?_, ?_⟩,
    ⟨t.maps, fun x hx y hy hxy => ?_, fun Φ hΦ => ⟨e' Φ, t'.maps Φ hΦ, hl2 Φ hΦ⟩⟩⟩
  · have h1 : ∀ m, incM F (1 : Matrix (Fin m) (Fin m) E) = 1 := fun m => Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1, h1, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
    exact t.Heisenberg₂ z Φ hΦ
  · intro h
    obtain ⟨b, hb⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F (Fin n × Fin d)
    obtain ⟨f, rfl⟩ := hsurj b
    exact hb (by rw [h]; rfl)
  · intro v
    refine ⟨?_, ?_⟩
    · rw [LinearMap.smul_apply, hc v, smul_smul, inv_mul_cancel₀ (hc0 v), one_smul]
    · rw [Submodule.map_smul _ _ _ (inv_ne_zero (hc0 v)), hSB v]
  · intro f φ hφ hφv
    funext y
    rw [LinearMap.smul_apply, hpure f φ hφ hφv]
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, LinearMap.smul_apply]
    have hfin1 : (Function.mulSupport fun v : Pl F => (c v)⁻¹).Finite := by
      refine hfin0.subset fun v hv h => hv ?_
      simp [h]
    have hfin2 := GlobalTheory.PureFactor.mulSupport_finite (κ := Fin n × Fin d) (fun v => ev v (φ v)) (by
      filter_upwards [hφv, hstd] with v h1 h2
      rw [h1, h2]) y
    rw [finprod_mul_distrib hfin1 hfin2, finprod_inv_distrib]
    ring
  · rw [← hl1 x hx, hxy, hl1 y hy]

theorem evBij_of_adel (hA : PositivityTheory.Mix.AdelSt) : EvBij := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP _ hM' =>
  isEv_bij_of_adel hA hP.base hP.herm hP.skew hP.good hM'

theorem evCone_of_adel (hA : PositivityTheory.Mix.AdelSt) : EvCone := evCone_of_bij (evBij_of_adel hA)

theorem evZero_of_adel (hA : PositivityTheory.Mix.AdelSt) (hDq : SchwartzDq) (h : AdaptedModelEvaluationAtZero) : EvZero := evZero_of_bij (evBij_of_adel hA) hDq h

end PositivityTheory.ThKF0
