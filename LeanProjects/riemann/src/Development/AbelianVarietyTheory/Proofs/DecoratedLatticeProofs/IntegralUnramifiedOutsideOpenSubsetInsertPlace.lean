import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.HaarStep

set_option maxHeartbeats 1000000 in

theorem integral_openOff_insert : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (Sf : Finset (FinPl D)) (v : FinPl D), v ∉ Sf → ∀ μ : Measure (Gv A v), μ.IsHaarMeasure → μ (stabLoc D.sp.cm.sig A.gram L v) = 1 → ∀ (S' : Finset (FinPl D)), (∀ u, u ∈ S' ↔ u = v ∨ u ∈ Sf) → ∀ F : GA D A → ℂ, IntegrableOn F (openOff A L S') m → ∫ g in openOff A L S', F g ∂m = ∫ x in openOff A L Sf, (∫ y, F (x * (emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x))⁻¹ * emb D.sp.cm.sig A.gram v y) ∂μ) ∂m := by
  intro D A L hL m hm Sf v hv μ hμ hK S' hS' F hF
  haveI : Submodule.IsLattice D.host.E L := hL.1
  have hne : ∀ u, u ∉ S' → u ≠ v := fun u hu h => hu ((hS' u).2 (Or.inl h))
  have memU : ∀ x, x ∈ openOff A L Sf ↔ x ∈ openOff A L S' ∧
      proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v := by
    intro x
    constructor
    · intro h
      exact ⟨fun u hu => h u (fun hu' => hu ((hS' u).2 (Or.inr hu'))), h v hv⟩
    · rintro ⟨h1, h2⟩ u hu
      by_cases e : u = v
      · subst e; exact h2
      · exact h1 u (fun h => by rcases (hS' u).1 h with h | h; exact e h; exact hu h)
  have memV : ∀ (y : Gv A v) (x : GA D A), emb D.sp.cm.sig A.gram v y * x ∈ openOff A L S' ↔ x ∈ openOff A L S' := by
    intro y x
    refine forall_congr' fun u => imp_congr_right fun hu => ?_
    rw [map_mul, proj_emb_ne _ _ (hne u hu), one_mul]
  have isOpen_off : ∀ S : Finset (FinPl D), IsOpen (openOff A L S) := by
    intro S
    let H : Subgroup (GA D A) :=
      ⨅ u, ⨅ (_ : u ∉ S), (stabLoc D.sp.cm.sig A.gram L u).comap (proj D.sp.cm.sig A.gram u)
    have eH : (H : Set (GA D A)) = openOff A L S := by
      ext g; simp [H, openOff, Subgroup.mem_iInf]
    rw [← eH]
    refine Subgroup.isOpen_mono (H₁ := levelOpen D.sp.cm.sig A.gram L) ?_ (isOpen_levelOpen _ _ L)
    intro g hg
    simp only [H, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro u _
    exact (mem_levelOpen.1 hg) u
  have hUm : MeasurableSet (openOff A L Sf) := (isOpen_off Sf).measurableSet
  have hVm : MeasurableSet (openOff A L S') := (isOpen_off S').measurableSet
  have hKo : IsOpen (stabLoc D.sp.cm.sig A.gram L v : Set (Gv A v)) := isOpen_stabLoc _ _ L v
  have hright : ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, μ.map (fun y => y * k) = μ := by
    intro k hk
    rw [GlobalTheory.AdelicUnimod.map_mul_right_eq,
      GlobalTheory.AdelicUnimod.modular_compact _ hKo (isCompact_stabLoc _ _ L v) hk, one_smul]
  have step1 : ∀ x ∈ openOff A L Sf,
      ∫ y, F (x * (emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x))⁻¹ * emb D.sp.cm.sig A.gram v y) ∂μ =
        ∫ y, F (emb D.sp.cm.sig A.gram v y * x) ∂μ := by
    intro x hx
    have hkK : proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v := hx v hv
    set k := proj D.sp.cm.sig A.gram v x with hk
    set x' := x * (emb D.sp.cm.sig A.gram v k)⁻¹ with hx'
    have hx'1 : proj D.sp.cm.sig A.gram v x' = 1 := by
      rw [hx', map_mul, map_inv, proj_emb_self, mul_inv_cancel]
    have hxx : x = x' * emb D.sp.cm.sig A.gram v k := by rw [hx', inv_mul_cancel_right]
    have e : ∀ y, emb D.sp.cm.sig A.gram v y * x = x' * emb D.sp.cm.sig A.gram v (y * k) := by
      intro y
      have hc := (commute_emb D.sp.cm.sig A.gram y hx'1).eq
      calc emb D.sp.cm.sig A.gram v y * x = emb D.sp.cm.sig A.gram v y * x' * emb D.sp.cm.sig A.gram v k := by
            rw [mul_assoc, ← hxx]
        _ = x' * emb D.sp.cm.sig A.gram v y * emb D.sp.cm.sig A.gram v k := by rw [hc]
        _ = x' * emb D.sp.cm.sig A.gram v (y * k) := by rw [map_mul, mul_assoc]
    simp_rw [e]
    have h := integral_map_equiv (μ := μ) (MeasurableEquiv.mulRight k)
      (fun y => F (x' * emb D.sp.cm.sig A.gram v y))
    have hm' : Measure.map (MeasurableEquiv.mulRight k) μ = μ := hright k hkK
    rw [hm'] at h
    exact h
  rw [setIntegral_congr_fun hUm step1]

  have hec : Continuous (emb D.sp.cm.sig A.gram v) := continuous_emb _ _ v
  have hpc : Continuous (proj D.sp.cm.sig A.gram v) := continuous_proj _ _ v
  let Q : Set (GA D A × Gv A v) :=
    {q | (proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ stabLoc D.sp.cm.sig A.gram L v}
  have hQo : IsOpen Q := hKo.preimage (((hpc.comp continuous_fst).inv).mul continuous_snd)
  let f₂ : GA D A × Gv A v → ℂ := Q.indicator (fun q => (openOff A L S').indicator F q.1)
  let T : GA D A × Gv A v → GA D A × Gv A v := fun p => (emb D.sp.cm.sig A.gram v p.2 * p.1, p.2)
  have hT : MeasurePreserving T (m.prod μ) (m.prod μ) := by
    have h1 : MeasurePreserving (fun p : Gv A v × GA D A => (p.1, emb D.sp.cm.sig A.gram v p.1 * p.2))
        (μ.prod m) (μ.prod m) :=
      MeasurePreserving.skew_product (MeasurePreserving.id μ)
        ((hec.comp continuous_fst).mul continuous_snd).measurable
        (Filter.Eventually.of_forall fun y => map_mul_left_eq_self m (emb D.sp.cm.sig A.gram v y))
    have h2 : MeasurePreserving (Prod.swap : GA D A × Gv A v → Gv A v × GA D A) (m.prod μ) (μ.prod m) :=
      Measure.measurePreserving_swap
    have h3 : MeasurePreserving (Prod.swap : Gv A v × GA D A → GA D A × Gv A v) (μ.prod m) (m.prod μ) :=
      Measure.measurePreserving_swap
    have h4 := (h3.comp h1).comp h2
    have e : T = (Prod.swap ∘ (fun p : Gv A v × GA D A => (p.1, emb D.sp.cm.sig A.gram v p.1 * p.2))) ∘ Prod.swap := by
      funext p; rfl
    rw [e]; exact h4
  have hCm : ∀ a : Gv A v, MeasurableSet {y : Gv A v | a⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v} :=
    fun a => (hKo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμC : ∀ a : Gv A v, μ {y : Gv A v | a⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v} = 1 := by
    intro a
    rw [← hK]
    exact measure_preimage_mul μ a⁻¹ _
  have slice : ∀ w, (fun y => f₂ (w, y)) =
      {y : Gv A v | (proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v}.indicator
        (fun _ => (openOff A L S').indicator F w) := by
    intro w; funext y
    rfl
  have hFV : Integrable ((openOff A L S').indicator F) m := (integrable_indicator_iff hVm).2 hF
  have hf₂m : AEStronglyMeasurable f₂ (m.prod μ) :=
    (hFV.aestronglyMeasurable.comp_fst).indicator hQo.measurableSet
  have inner : ∀ w, ∫ y, f₂ (w, y) ∂μ = (openOff A L S').indicator F w := by
    intro w
    rw [slice w, integral_indicator_const _ (hCm _), Measure.real, hμC, ENNReal.toReal_one, one_smul]
  have innerN : ∀ w, ∫ y, ‖f₂ (w, y)‖ ∂μ = ‖(openOff A L S').indicator F w‖ := by
    intro w
    have : (fun y => ‖f₂ (w, y)‖) =
        {y : Gv A v | (proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v}.indicator
          (fun _ => ‖(openOff A L S').indicator F w‖) := by
      rw [show (fun y => ‖f₂ (w, y)‖) = fun y => ‖(fun y => f₂ (w, y)) y‖ from rfl, slice w]
      funext y
      exact norm_indicator_eq_indicator_norm _ y
    rw [this, integral_indicator_const _ (hCm _), Measure.real, hμC, ENNReal.toReal_one, one_smul]
  have hf₂ : Integrable f₂ (m.prod μ) := by
    refine (integrable_prod_iff hf₂m).2 ⟨Filter.Eventually.of_forall fun w => ?_, ?_⟩
    · rw [slice w]
      refine (integrable_indicator_iff (hCm _)).2 ?_
      haveI : IsFiniteMeasure (μ.restrict
          {y : Gv A v | (proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v}) :=
        isFiniteMeasure_restrict.2 (by rw [hμC]; exact ENNReal.one_ne_top)
      exact integrable_const _
    · simp_rw [innerN]
      exact hFV.norm
  have hf₁ : Integrable (f₂ ∘ T) (m.prod μ) := (hT.integrable_comp hf₂m).2 hf₂
  have hI : ∫ p, f₂ (T p) ∂(m.prod μ) = ∫ p, f₂ p ∂(m.prod μ) := by
    rw [← integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hf₂m), hT.map_eq]
  have hT1 : ∀ x y, f₂ (T (x, y)) = (openOff A L Sf).indicator (fun x => F (emb D.sp.cm.sig A.gram v y * x)) x := by
    intro x y
    have hp : (proj D.sp.cm.sig A.gram v (emb D.sp.cm.sig A.gram v y * x))⁻¹ * y =
        (proj D.sp.cm.sig A.gram v x)⁻¹ := by
      rw [map_mul, proj_emb_self, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    have hmem : T (x, y) ∈ Q ↔ proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v := by
      show (proj D.sp.cm.sig A.gram v (emb D.sp.cm.sig A.gram v y * x))⁻¹ * y ∈ stabLoc D.sp.cm.sig A.gram L v ↔ _
      rw [hp, inv_mem_iff]
    by_cases h2 : proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram L v
    · rw [show f₂ (T (x, y)) = (openOff A L S').indicator F (emb D.sp.cm.sig A.gram v y * x) from
        Set.indicator_of_mem (hmem.2 h2) _]
      by_cases h1 : x ∈ openOff A L S'
      · rw [Set.indicator_of_mem ((memV y x).2 h1), Set.indicator_of_mem ((memU x).2 ⟨h1, h2⟩)]
      · rw [Set.indicator_of_notMem (mt (memV y x).1 h1), Set.indicator_of_notMem (fun h => h1 ((memU x).1 h).1)]
    · rw [show f₂ (T (x, y)) = 0 from Set.indicator_of_notMem (mt hmem.1 h2) _,
        Set.indicator_of_notMem (fun h => h2 ((memU x).1 h).2)]
  calc ∫ g in openOff A L S', F g ∂m = ∫ w, (openOff A L S').indicator F w ∂m := (integral_indicator hVm).symm
    _ = ∫ p, f₂ p ∂(m.prod μ) := by rw [integral_prod f₂ hf₂]; simp_rw [inner]
    _ = ∫ p, f₂ (T p) ∂(m.prod μ) := hI.symm
    _ = ∫ x, ∫ y, f₂ (T (x, y)) ∂μ ∂m := integral_prod (f₂ ∘ T) hf₁
    _ = ∫ x, (openOff A L Sf).indicator (fun x => ∫ y, F (emb D.sp.cm.sig A.gram v y * x) ∂μ) x ∂m := by
      congr 1; funext x
      simp_rw [hT1]
      by_cases h : x ∈ openOff A L Sf <;> simp [h]
    _ = ∫ x in openOff A L Sf, ∫ y, F (emb D.sp.cm.sig A.gram v y * x) ∂μ ∂m := integral_indicator hUm

end GlobalTheory.Core.Rk.HaarStep
