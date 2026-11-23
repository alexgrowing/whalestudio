import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

open scoped Pointwise ENNReal in
open GlobalTheory.LocTateInt in
theorem UpperTheory.local_units_haar_comparison :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F), ∀ [MeasurableSpace (Fv F v ⊗[F] E)] [BorelSpace (Fv F v ⊗[F] E)] (m : Measure (Fv F v ⊗[F] E)) [m.IsAddHaarMeasure],
        ∀ (μ : Measure (idelesAt E (evFin F v))), IsNormE E v μ → ∃ c : ℝ, 0 < c ∧ ∀ f : Fv F v ⊗[F] E → ℂ, (∀ t, f t ≠ 0 → IsUnit t) →
          ∫ l : idelesAt E (evFin F v), f (compFin F E v (l.1 : AE F E)) * ((absE F E l.1 : ℝ) : ℂ) ∂μ = (c : ℂ) * ∫ s, f s ∂m := by
  intro F E _ _ _ _ _ v _ _ lam _ μ hμ
  haveI := finite_FE (F := F) (E := E)
  haveI := isTopologicalRing_Ev (E := E) v
  haveI := t2Space_Fv_tensor (E := E) v
  haveI := locallyCompactSpace_Ev (E := E) v
  haveI := secondCountable_Ev (E := E) v
  haveI := isOpenUnits_Ev (E := E) v
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evFin F v)
  haveI := hμ.1
  set φ := idelesAtEquiv E v with hφ
  let j : idelesAt E (evFin F v) → Fv F v ⊗[F] E := fun l => ((φ l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E)
  have hoe : Topology.IsOpenEmbedding j :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := Fv F v ⊗[F] E)).comp φ.toHomeomorph.isOpenEmbedding
  have hme : MeasurableEmbedding j := hoe.measurableEmbedding
  set ν : Measure (idelesAt E (evFin F v)) := lam.comap j with hν
  have hνa : ∀ s, ν s = lam (j '' s) := fun s => hme.comap_apply lam s
  have hne : ∀ x : (Fv F v ⊗[F] E)ˣ, GlobalTheory.Doubling.absEv F E v x ≠ 0 := fun x h => by
    have e := congrArg (GlobalTheory.Doubling.absEv F E v) (mul_inv_cancel x)
    rw [map_mul, map_one, h, zero_mul] at e
    exact zero_ne_one e
  set f : idelesAt E (evFin F v) → ℝ≥0 := fun l => (GlobalTheory.Doubling.absEv F E v (φ l))⁻¹ with hf
  have hfc : Continuous f :=
    ((GlobalTheory.Doubling.continuous_absEv v).comp φ.continuous).inv₀ fun l => hne _
  have hfm : ∀ x y, f (x * y) = f x * f y := fun x y => by
    simp only [hf, map_mul, mul_inv]
  have hf1 : ∀ a, f a⁻¹ * f a = 1 := fun a => by
    rw [← hfm, inv_mul_cancel]
    simp [hf]
  haveI : IsLocallyFiniteMeasure ν := by
    refine ⟨fun x => ?_⟩
    obtain ⟨s, hs, hs'⟩ := lam.finiteAt_nhds (j x)
    refine ⟨j ⁻¹' s, hoe.continuous.continuousAt.preimage_mem_nhds hs, ?_⟩
    rw [hνa]
    exact (measure_mono (Set.image_preimage_subset _ _)).trans_lt hs'
  haveI : ν.IsOpenPosMeasure := by
    refine ⟨fun U hU hn => ?_⟩
    rw [hνa]
    exact (hoe.isOpenMap U hU).measure_ne_zero lam (hn.image _)
  haveI := IsLocallyFiniteMeasure.withDensity_coe (μ := ν) hfc
  have hpos : (ν.withDensity fun x => (f x : ℝ≥0∞)).IsOpenPosMeasure := by
    refine (withDensity_absolutelyContinuous' (μ := ν)
      (hfc.measurable.coe_nnreal_ennreal.aemeasurable) ?_).isOpenPosMeasure
    exact Eventually.of_forall fun x => ENNReal.coe_ne_zero.2 (inv_ne_zero (hne _))
  have hinv : (ν.withDensity fun x => (f x : ℝ≥0∞)).IsMulLeftInvariant := by
    refine ⟨fun a => ?_⟩
    have hma : MeasurableEmbedding (fun x : idelesAt E (evFin F v) => a * x) :=
      (Homeomorph.mulLeft a).measurableEmbedding
    have hmap : Measure.map (fun x : idelesAt E (evFin F v) => a * x) ν = (f a : ℝ≥0∞) • ν := by
      ext s hs
      rw [hma.map_apply, Measure.smul_apply, hνa, hνa, smul_eq_mul]
      have e : j '' ((fun x => a * x) ⁻¹' s) = (φ a)⁻¹ • (j '' s) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          refine ⟨j (a * x), ⟨a * x, hx, rfl⟩, ?_⟩
          simp [j, Units.smul_def, map_mul]
        · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
          refine ⟨a⁻¹ * x, by simpa using hx, ?_⟩
          simp [j, Units.smul_def, map_mul, map_inv]
      rw [e, ← distribHaarChar_mul lam (φ a)⁻¹ (j '' s), map_inv, distribHaarChar_Ev]
      rfl
    ext s hs
    rw [hma.map_apply, withDensity_apply _ (hma.measurable hs), withDensity_apply _ hs]
    have h1 : ∀ x, (f x : ℝ≥0∞) = (f a⁻¹ : ℝ≥0∞) * (f (a * x) : ℝ≥0∞) := fun x => by
      rw [← ENNReal.coe_mul, hfm, ← mul_assoc, hf1, one_mul]
    have h2 : (f a⁻¹ : ℝ≥0∞) * (f a : ℝ≥0∞) = 1 := by
      rw [← ENNReal.coe_mul, hf1, ENNReal.coe_one]
    calc ∫⁻ x in (fun x => a * x) ⁻¹' s, (f x : ℝ≥0∞) ∂ν
        = ∫⁻ x in (fun x => a * x) ⁻¹' s, (f a⁻¹ : ℝ≥0∞) * (f (a * x) : ℝ≥0∞) ∂ν := lintegral_congr h1
      _ = (f a⁻¹ : ℝ≥0∞) * ∫⁻ x in (fun x => a * x) ⁻¹' s, (f (a * x) : ℝ≥0∞) ∂ν :=
          lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = (f a⁻¹ : ℝ≥0∞) * ∫⁻ x in s, (f x : ℝ≥0∞) ∂(Measure.map (fun x => a * x) ν) := by
          rw [hma.restrict_map, hma.lintegral_map]
      _ = _ := by
          rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, h2, one_mul]
  set ρ := ν.withDensity fun x => (f x : ℝ≥0∞) with hρ
  haveI : ρ.IsHaarMeasure := ⟨⟩
  obtain ⟨c, hc0, hc⟩ := haar_idelesAt_eq_smul μ ρ
  refine ⟨c, by exact_mod_cast pos_iff_ne_zero.2 hc0, fun g hg => ?_⟩
  rw [hc, integral_smul_nnreal_measure, hρ, integral_withDensity_eq_integral_smul hfc.measurable]
  have h1 : ∀ l : idelesAt E (evFin F v),
      f l • (g (compFin F E v (l.1 : AE F E)) * ((absE F E l.1 : ℝ) : ℂ)) = g (j l) := by
    intro l
    have e : absE F E l.1 = GlobalTheory.Doubling.absEv F E v (φ l) := by
      rw [absE_of_mem l.2]
      rfl
    have e2 : ((GlobalTheory.Doubling.absEv F E v (φ l) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne (φ l)
    rw [e, NNReal.smul_def, Complex.real_smul, show compFin F E v (l.1 : AE F E) = j l from rfl]
    simp only [hf, NNReal.coe_inv, Complex.ofReal_inv]
    field_simp
  simp_rw [h1]
  have h2 : ∫ l, g (j l) ∂ν = ∫ s, g s ∂lam := by
    rw [← hme.integral_map, hν, hme.map_comap]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
    by_contra h
    obtain ⟨u, rfl⟩ := hg t h
    exact ht ⟨φ.symm u, by simp [j]⟩
  rw [h2, NNReal.smul_def, Complex.real_smul]
