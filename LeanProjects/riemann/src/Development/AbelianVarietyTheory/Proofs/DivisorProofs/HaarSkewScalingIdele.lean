import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabAtPair
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_skew_elem (h : IsCMExt F E σ) (hσ : ∀ e, σ (σ e) = e) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  have hne : ∃ y, σ y ≠ y := by
    by_contra hc
    push Not at hc
    have := h.2.1
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y =>
        (h.2.2.2 τ y).symm.trans (congrArg τ (hc y)))))
  obtain ⟨y, hy⟩ := hne
  exact ⟨y - σ y, sub_ne_zero.2 hy.symm, by rw [map_sub, hσ, neg_sub]⟩

theorem algebraMap_norm_cA (h : IsCMExt F E σ) (s : AE F E) :
    algebraMap (AF F) (AE F E) (Algebra.norm (AF F) s) = s * cA σ s :=
  GlobalTheory.Doubling.algebraMap_norm_eq h s

theorem mul_liftV (v : Pl F) (u : AF F) (a : Fv F v) :
    u * GlobalTheory.LatVac.liftV v a = GlobalTheory.LatVac.liftV v (evFin F v u * a) := by
  have h1 : At (evFin F v) (u * GlobalTheory.LatVac.liftV v a - GlobalTheory.LatVac.liftV v (evFin F v u * a)) := fun w hw => by
    have a1 := GlobalTheory.LatVac.at_liftV v a w hw
    have a2 := GlobalTheory.LatVac.at_liftV v (evFin F v u * a) w hw
    rw [smul_eq_mul] at a1 a2 ⊢
    rw [mul_sub, mul_left_comm, a1, a2, mul_zero, sub_zero]
  have h2 := partFin_of_at h1
  rw [partFin, smul_eq_mul, mul_comm] at h2
  have h3 := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) (u * GlobalTheory.LatVac.liftV v a - GlobalTheory.LatVac.liftV v (evFin F v u * a))
    (by rw [map_sub, map_mul, GlobalTheory.LatVac.evFin_liftV, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [smul_eq_mul, h2] at h3
  exact sub_eq_zero.1 h3

theorem exists_skewAt_equiv (h : IsCMExt F E σ) (hσ : ∀ e, σ (σ e) = e) (v : Pl F) :
    ∃ φ : Fv F v ≃ₜ+ skewAt σ (evFin F v), ∀ (u : AF F) (a : Fv F v), (φ (evFin F v u * a)).1 = u • (φ a).1 := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  obtain ⟨δ, hδ, hs⟩ := exists_skew_elem h hσ
  set d : AE F E := (1 : AF F) ⊗ₜ[F] δ with hd
  set d' : AE F E := (1 : AF F) ⊗ₜ[F] ((2 * δ)⁻¹) with hd'
  have hdd : 2 * (d' * d) = 1 := by
    rw [hd, hd', Algebra.TensorProduct.tmul_mul_tmul, two_mul, ← TensorProduct.tmul_add, one_mul,
      Algebra.TensorProduct.one_def]
    congr 1
    field_simp
    norm_num
  have hcd : cA σ d = -d := by
    rw [hd, ← TensorProduct.tmul_neg, ← hs]; rfl
  have hcd' : cA σ d' = -d' := by
    rw [hd', ← TensorProduct.tmul_neg, show -(2 * δ)⁻¹ = σ (2 * δ)⁻¹ by
      rw [map_inv₀, map_mul, hs, map_ofNat, mul_neg, inv_neg]]
    rfl
  let ℓ : AE F E → AF F := fun c => Algebra.norm (AF F) (1 + c * d') - 1 - Algebra.norm (AF F) (c * d')
  have hℓc : Continuous ℓ :=
    ((GlobalTheory.Doubling.continuous_norm_tens.comp (continuous_const.add (continuous_id.mul continuous_const))).sub
      continuous_const).sub (GlobalTheory.Doubling.continuous_norm_tens.comp (continuous_id.mul continuous_const))
  have hℓ : ∀ c, cA σ c = -c → algebraMap (AF F) (AE F E) (ℓ c) = 2 * (c * d') := fun c hc => by
    simp only [ℓ, map_sub, map_one, algebraMap_norm_cA h, map_add, map_mul (cA σ), hc, hcd']
    ring
  have hinj : Function.Injective (algebraMap (AF F) (AE F E)) :=
    Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (algebraMap F E).injective
  have hskew : ∀ u : AF F, cA σ (u • d) = -(u • d) := fun u => by rw [map_smul, hcd, smul_neg]
  have hℓd : ∀ u : AF F, ℓ (u • d) = u := fun u => hinj (by
    rw [hℓ _ (hskew u), Algebra.smul_def]
    linear_combination (algebraMap (AF F) (AE F E) u) * hdd)
  have hdℓ : ∀ c, cA σ c = -c → ℓ c • d = c := fun c hc => by
    rw [Algebra.smul_def, hℓ c hc]
    linear_combination c * hdd
  have hl : Continuous (GlobalTheory.LatVac.liftV v) :=
    Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v)
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have hld : Continuous fun a => GlobalTheory.LatVac.liftV v a • d :=
    (IsModuleTopology.continuous_of_linearMap (LinearMap.toSpanSingleton (AF F) (AE F E) d)).comp hl
  have he : Continuous (evFin F v) := (RestrictedProduct.continuous_eval v).comp continuous_snd
  refine ⟨{ toFun := fun a => ⟨GlobalTheory.LatVac.liftV v a • d, fun u hu => by
              rw [smul_smul, ← smul_eq_mul, GlobalTheory.LatVac.at_liftV v a u hu, zero_smul], hskew _⟩
            invFun := fun c => evFin F v (ℓ c.1)
            left_inv := fun a => by simp only [hℓd, GlobalTheory.LatVac.evFin_liftV]
            right_inv := fun c => Subtype.ext ?_
            map_add' := fun a b => Subtype.ext ?_
            continuous_toFun := Continuous.subtype_mk (show Continuous fun a => GlobalTheory.LatVac.liftV v a • d from
              hld) _
            continuous_invFun := he.comp (hℓc.comp continuous_subtype_val) }, fun u a => ?_⟩
  · show GlobalTheory.LatVac.liftV v (evFin F v (ℓ c.1)) • d = c.1
    rw [← mul_one (evFin F v (ℓ c.1)), ← mul_liftV, mul_comm, mul_smul, hdℓ _ c.2.2]
    exact partFin_of_at c.2.1
  · show GlobalTheory.LatVac.liftV v (a + b) • d = GlobalTheory.LatVac.liftV v a • d + GlobalTheory.LatVac.liftV v b • d
    rw [map_add, add_smul]
  · show GlobalTheory.LatVac.liftV v (evFin F v u * a) • d = u • GlobalTheory.LatVac.liftV v a • d
    rw [← mul_liftV, mul_smul]

theorem map_normSmul_inv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (hσ : ∀ e, σ (σ e) = e) (v : Pl F) (t : (AE F E)ˣ)
    (ht : t ∈ idelesAt E (evFin F v)) (ν : Measure (skewAt σ (evFin F v))) (hν : ν.IsAddHaarMeasure) :
    ν.map (normSmul hσ (t⁻¹ : (AE F E)ˣ).1) = absE F E t • ν := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨φ, hφ⟩ := exists_skewAt_equiv h hσ v
  set n : Fv F v := evFin F v (Algebra.norm (AF F) (t⁻¹ : (AE F E)ˣ).1) with hn
  have hmul : n * evFin F v (Algebra.norm (AF F) t.1) = 1 := by
    rw [hn, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  have hn0 : n ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have habs : absE F E t = (‖n‖₊)⁻¹ := by
    rw [absE_of_mem ht, GlobalTheory.Doubling.absEv_unitFin, eq_inv_of_mul_eq_one_right hmul, nnnorm_inv]
  have hμ : (ν.map φ.symm).IsAddHaarMeasure := φ.symm.isAddHaarMeasure_map ν
  have key := GlobalTheory.CompanionTheory.SW.ProdFormula.map_mul_left_finite v n hn0 (ν.map φ.symm) hμ
  have hm : Measurable φ := φ.continuous.measurable
  have hm' : Measurable φ.symm := φ.symm.continuous.measurable
  have hmn : Measurable fun x : Fv F v => n * x := (continuous_const_mul _).measurable
  have e : (normSmul hσ (t⁻¹ : (AE F E)ˣ).1 : skewAt σ (evFin F v) → skewAt σ (evFin F v)) =
      φ ∘ ((fun x => n * x) ∘ φ.symm) := by
    funext c
    apply Subtype.ext
    show (t⁻¹ : (AE F E)ˣ).1 * cA σ (t⁻¹ : (AE F E)ˣ).1 * c.1 = (φ (n * φ.symm c)).1
    rw [hn, hφ, ContinuousAddEquiv.apply_symm_apply, Algebra.smul_def, algebraMap_norm_cA h]
  have e2 : (ν.map φ.symm).map φ = ν := by
    rw [Measure.map_map hm hm', show φ ∘ φ.symm = id from funext φ.apply_symm_apply, Measure.map_id]
  rw [e, ← Measure.map_map hm (hmn.comp hm'), ← Measure.map_map hmn hm']
  refine (congrArg (Measure.map φ) key).trans ?_
  rw [Measure.map_smul, e2, habs]

end GlobalTheory.ThK.LemF.QuotInv

end
