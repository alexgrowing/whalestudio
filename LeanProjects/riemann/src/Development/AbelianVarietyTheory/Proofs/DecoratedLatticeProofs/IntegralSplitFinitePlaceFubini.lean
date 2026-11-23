import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.Core.Rk.FubiniPlace

set_option maxHeartbeats 1000000 in

theorem integral_split_place : ∀ (D : D7) (A : HSp D) (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (μ : Measure (GlobalTheory.FinZeta.Gv A v)), μ.IsHaarMeasure → ∀ J : Subgroup (GlobalTheory.FinZeta.Gv A v), IsOpen (J : Set (GlobalTheory.FinZeta.Gv A v)) → μ J = 1 → ∀ E : Set (GA D A), MeasurableSet E → (∀ x y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y ∈ E ↔ x ∈ E) → ∀ (F : GA D A → ℂ) (ζ : GlobalTheory.FinZeta.Gv A v → ℂ), Integrable ζ μ → (∀ y ∈ J, ζ y = 1) → (∀ x ∈ E, GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x = 1 → ∀ y, F (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y) = ζ y * F x) → IntegrableOn F (E ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) m → IntegrableOn F E m ∧ ∫ g in E, F g ∂m = (∫ y, ζ y ∂μ) * ∫ g in E ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}, F g ∂m := by
  intro D A m hm v μ hμ J hJo hJ1 E hE hEr F ζ hζ hζJ hF hFi
  have hec : Continuous (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v) := GlobalTheory.AdelicU.continuous_emb _ _ v
  have hpc : Continuous (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v) := GlobalTheory.AdelicU.continuous_proj _ _ v
  have hPm : MeasurableSet {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J} := (hJo.preimage hpc).measurableSet
  have hUm : MeasurableSet (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) := hE.inter hPm
  have hJm : MeasurableSet (J : Set (GlobalTheory.FinZeta.Gv A v)) := hJo.measurableSet

  have hright : ∀ k ∈ J, μ.map (fun y => y * k) = μ := by
    intro k hk
    have h := Measure.map_right_mul_eq_modularCharacterFun_smul μ k
    have h2 := congrArg (fun m' : Measure (GlobalTheory.FinZeta.Gv A v) => m' (J : Set (GlobalTheory.FinZeta.Gv A v))) h
    simp only [Measure.coe_nnreal_smul_apply] at h2
    rw [Measure.map_apply (measurable_mul_const _) hJm,
      show (fun x => x * k) ⁻¹' (J : Set (GlobalTheory.FinZeta.Gv A v)) = J from Set.ext fun x => J.mul_mem_cancel_right hk,
      hJ1, mul_one] at h2
    have h3 : Measure.modularCharacterFun k = 1 := by exact_mod_cast h2.symm
    rw [h, h3, one_smul]

  have dec : ∀ x : GA D A, GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) = 1 := by
    intro x; rw [map_mul, GlobalTheory.AdelicU.proj_emb_self, mul_inv_cancel]
  have dec2 : ∀ x : GA D A, x = (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x; rw [map_inv, inv_mul_cancel_right]
  have shift : ∀ (x : GA D A) (y : GlobalTheory.FinZeta.Gv A v),
      GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x = (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (y * GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x y
    have hc := (GlobalTheory.AdelicU.commute_emb D.sp.cm.sig A.gram y (dec x)).eq
    calc GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x = GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
          rw [mul_assoc, ← dec2]
      _ = _ := by rw [hc, mul_assoc, ← map_mul]
  have hEl : ∀ (y : GlobalTheory.FinZeta.Gv A v) (x : GA D A), GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x ∈ E ↔ x ∈ E := by
    intro y x
    have h1 := hEr (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h1
    rw [shift, hEr, h1]
  have key : ∀ x ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}), ∀ y, F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x) = F x * ζ (y * GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x) := by
    intro x hx y
    have h1 := hEr (x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h1
    have hx' : x * GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹ ∈ E := h1.1 hx.1
    have h2 := hF _ hx' (dec x) (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)
    rw [← dec2 x] at h2
    rw [shift, hF _ hx' (dec x), h2, hζJ _ hx.2, one_mul, mul_comm]
  classical

  let c : GA D A → GlobalTheory.FinZeta.Gv A v := fun x => if GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J then GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x else 1
  have hcm : Measurable c := Measurable.ite hPm hpc.measurable measurable_const
  have hR : MeasurePreserving (fun q : GA D A × GlobalTheory.FinZeta.Gv A v => (q.1, q.2 * c q.1)) (m.prod μ) (m.prod μ) := by
    refine MeasurePreserving.skew_product (g := fun x y => y * c x) (MeasurePreserving.id m)
      (measurable_snd.mul (hcm.comp measurable_fst) : Measurable fun p : GA D A × GlobalTheory.FinZeta.Gv A v => p.2 * c p.1)
      (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J
    · simp only [c, if_pos hx]; exact hright _ hx
    · simp only [c, if_neg hx, mul_one, Measure.map_id']
  let g0 : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ := fun q => (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator F q.1 * ζ q.2
  have hg0 : Integrable g0 (m.prod μ) := Integrable.mul_prod ((integrable_indicator_iff hUm).2 hFi) hζ
  let f : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ := fun q => (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator (fun x => F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2 * x)) q.1
  have hfg : f = g0 ∘ (fun q : GA D A × GlobalTheory.FinZeta.Gv A v => (q.1, q.2 * c q.1)) := by
    funext q
    by_cases hx : q.1 ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J})
    · have hx2 : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1 ∈ J := hx.2
      simp only [f, g0, Function.comp_apply, c, if_pos hx2]
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, key q.1 hx]
    · simp only [f, g0, Function.comp_apply, Set.indicator_of_notMem hx, zero_mul]
  have hf : Integrable f (m.prod μ) := by
    rw [hfg]; exact (hR.integrable_comp hg0.aestronglyMeasurable).2 hg0
  have hfint : ∫ q, f q ∂(m.prod μ) = ∫ q, g0 q ∂(m.prod μ) := by
    have h := integral_map (μ := m.prod μ) hR.measurable.aemeasurable (f := g0)
      (by rw [hR.map_eq]; exact hg0.aestronglyMeasurable)
    rw [hR.map_eq] at h
    rw [hfg]; exact h.symm

  let T : GA D A × GlobalTheory.FinZeta.Gv A v → GA D A × GlobalTheory.FinZeta.Gv A v := fun q => (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2 * q.1, q.2)
  have hTp : MeasurePreserving T (m.prod μ) (m.prod μ) := by
    have h1 : MeasurePreserving (fun p : GlobalTheory.FinZeta.Gv A v × GA D A => (p.1, GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v p.1 * p.2)) (μ.prod m) (μ.prod m) :=
      MeasurePreserving.skew_product (MeasurePreserving.id μ)
        ((hec.comp continuous_fst).mul continuous_snd).measurable
        (Filter.Eventually.of_forall fun y => map_mul_left_eq_self m (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y))
    have h2 : MeasurePreserving (Prod.swap : GA D A × GlobalTheory.FinZeta.Gv A v → GlobalTheory.FinZeta.Gv A v × GA D A) (m.prod μ) (μ.prod m) :=
      Measure.measurePreserving_swap
    have h3 : MeasurePreserving (Prod.swap : GlobalTheory.FinZeta.Gv A v × GA D A → GA D A × GlobalTheory.FinZeta.Gv A v) (μ.prod m) (m.prod μ) :=
      Measure.measurePreserving_swap
    have h4 := (h3.comp h1).comp h2
    have e : T = (Prod.swap ∘ (fun p : GlobalTheory.FinZeta.Gv A v × GA D A => (p.1, GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v p.1 * p.2))) ∘ Prod.swap := by
      funext p; rfl
    rw [e]; exact h4
  let Te : (GA D A × GlobalTheory.FinZeta.Gv A v) ≃ᵐ (GA D A × GlobalTheory.FinZeta.Gv A v) :=
    { toFun := T
      invFun := fun q => ((GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v q.2)⁻¹ * q.1, q.2)
      left_inv := fun q => by simp [T]
      right_inv := fun q => by simp [T]
      measurable_toFun := (((hec.comp continuous_snd).mul continuous_fst).prodMk continuous_snd).measurable
      measurable_invFun := ((((hec.comp continuous_snd).inv).mul continuous_fst).prodMk continuous_snd).measurable }
  have hT : MeasurePreserving Te (m.prod μ) (m.prod μ) := hTp
  let f₂ : GA D A × GlobalTheory.FinZeta.Gv A v → ℂ :=
    fun q => {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J}.indicator (fun q => E.indicator F q.1) q
  have hf₂T : ∀ q, f₂ (Te q) = f q := by
    rintro ⟨x, y⟩
    have hp : (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y = (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x)⁻¹ := by
      rw [map_mul, GlobalTheory.AdelicU.proj_emb_self, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    show {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J}.indicator (fun q => E.indicator F q.1) (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) =
      (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator (fun x => F (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x)) x
    by_cases h2 : GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v x ∈ J
    · have hq : (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) ∈ {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J} := by
        show (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y ∈ J
        rw [hp]; exact J.inv_mem h2
      rw [Set.indicator_of_mem hq]
      by_cases h1 : x ∈ E
      · rw [Set.indicator_of_mem ((hEl y x).2 h1), Set.indicator_of_mem (show x ∈ (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}) from ⟨h1, h2⟩)]
      · rw [Set.indicator_of_notMem (mt (hEl y x).1 h1), Set.indicator_of_notMem (fun h => h1 h.1)]
    · have hq : (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x, y) ∉ {q : GA D A × GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v q.1)⁻¹ * q.2 ∈ J} := by
        show ¬ (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v (GlobalTheory.AdelicU.emb D.sp.cm.sig A.gram v y * x))⁻¹ * y ∈ J
        rw [hp, inv_mem_iff]; exact h2
      rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem (fun h => h2 h.2)]
  have hf₂ : Integrable f₂ (m.prod μ) := by
    refine (hT.integrable_comp_emb Te.measurableEmbedding).1 ?_
    have : f₂ ∘ Te = f := funext hf₂T
    rw [this]; exact hf
  have hCm : ∀ a : GlobalTheory.FinZeta.Gv A v, MeasurableSet {y : GlobalTheory.FinZeta.Gv A v | a⁻¹ * y ∈ J} :=
    fun a => (hJo.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμC : ∀ a : GlobalTheory.FinZeta.Gv A v, μ {y : GlobalTheory.FinZeta.Gv A v | a⁻¹ * y ∈ J} = 1 := by
    intro a
    rw [← hJ1]
    exact measure_preimage_mul μ a⁻¹ _
  have inner : ∀ w, ∫ y, f₂ (w, y) ∂μ = E.indicator F w := by
    intro w
    have : (fun y => f₂ (w, y)) = {y : GlobalTheory.FinZeta.Gv A v | (GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v w)⁻¹ * y ∈ J}.indicator (fun _ => E.indicator F w) := by
      funext y; rfl
    rw [this, integral_indicator_const _ (hCm _), Measure.real, hμC, ENNReal.toReal_one, one_smul]
  have hFE : Integrable (E.indicator F) m := by
    have h := hf₂.integral_prod_left
    simp_rw [inner] at h
    exact h
  refine ⟨(integrable_indicator_iff hE).1 hFE, ?_⟩
  calc ∫ g in E, F g ∂m = ∫ w, E.indicator F w ∂m := (integral_indicator hE).symm
    _ = ∫ q, f₂ q ∂(m.prod μ) := by rw [integral_prod f₂ hf₂]; simp_rw [inner]
    _ = ∫ q, f₂ (Te q) ∂(m.prod μ) := (hT.integral_comp' f₂).symm
    _ = ∫ q, f q ∂(m.prod μ) := by simp_rw [hf₂T]
    _ = ∫ q, g0 q ∂(m.prod μ) := hfint
    _ = (∫ x, (E ∩ {g : GA D A | GlobalTheory.AdelicU.proj D.sp.cm.sig A.gram v g ∈ J}).indicator F x ∂m) * ∫ y, ζ y ∂μ := integral_prod_mul _ _
    _ = _ := by rw [integral_indicator hUm, mul_comm]

end GlobalTheory.Core.Rk.FubiniPlace
