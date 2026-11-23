import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.BasePsi.Integrals

variable {F : Type} [Field F] [NumberField F]

theorem integral_pi_unit {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (h : X → ℝ) :
    ∫ y : Unit → X, h (y ()) ∂(Measure.pi fun _ : Unit => μ) = ∫ x, h x ∂μ :=
  (measurePreserving_piUnique (fun _ : Unit => μ)).integral_comp' (f := MeasurableEquiv.piUnique _) h

theorem integral_comp_unit_mul {R : Type} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [MeasurableSpace R] [BorelSpace R] (b : Rˣ) (μ : Measure R) (f : R → ℝ) :
    ∫ y, f ((b : R) * y) ∂μ = ∫ y, f y ∂(μ.map fun y => (b : R) * y) := by
  let e : R ≃ₜ R :=
    { toEquiv := Units.mulLeft b
      continuous_toFun := show Continuous fun x => (b : R) * x from continuous_const.mul continuous_id
      continuous_invFun :=
        show Continuous fun x => ((b⁻¹ : Rˣ) : R) * x from continuous_const.mul continuous_id }
  exact (e.measurableEmbedding.integral_map (μ := μ) f).symm

def unitInf (a : (AF F)ˣ) : (Ainf F)ˣ where
  val := (a : AF F).1
  inv := ((a⁻¹ : (AF F)ˣ) : AF F).1
  val_inv := by
    have h : ((a : AF F) * ((a⁻¹ : (AF F)ˣ) : AF F)).1 = 1 := by simp; rfl
    exact h
  inv_val := by
    have h : (((a⁻¹ : (AF F)ˣ) : AF F) * (a : AF F)).1 = 1 := by simp; rfl
    exact h

theorem sigmaFinite_inf (li : Measure (Ainf F)) (h : li.IsAddHaarMeasure) : SigmaFinite li := by
  infer_instance

theorem sigmaFinite_fin (v : HeightOneSpectrum (𝓞 F)) (l : Measure (Fv F v)) (h : l.IsAddHaarMeasure) :
    SigmaFinite l := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  infer_instance

theorem integral_mul_inf (li : Measure (Ainf F)) (h : li.IsAddHaarMeasure) (b : (Ainf F)ˣ)
    (G : Ainf F → ℝ) :
    ∫ y, G ((b : Ainf F) * y) ∂li = ‖((b⁻¹ : (Ainf F)ˣ) : Ainf F)‖ * ∫ y, G y ∂li := by
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hn : 0 ≤ ‖((b⁻¹ : (Ainf F)ˣ) : Ainf F)‖ := by
    rw [InfiniteAdeleRing.norm_def]
    exact Finset.prod_nonneg fun w _ => pow_nonneg (norm_nonneg _) _
  rw [integral_comp_unit_mul b li G, GlobalTheory.CompanionTheory.SW.ProdFormula.map_mul_left_infinite ⟨rfl⟩ b li h,
    integral_smul_measure, ENNReal.toReal_ofReal hn, smul_eq_mul]

theorem integral_mul_fin (v : HeightOneSpectrum (𝓞 F)) (l : Measure (Fv F v))
    (h : l.IsAddHaarMeasure) (c : Fv F v) (hc : c ≠ 0) (f : Fv F v → ℝ) :
    ∫ y, f (c * y) ∂l = ‖c‖⁻¹ * ∫ y, f y ∂l := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have h1 := integral_comp_unit_mul (Units.mk0 c hc) l f
  simp only [Units.val_mk0] at h1
  rw [h1, GlobalTheory.CompanionTheory.SW.ProdFormula.map_mul_left_finite v c hc l h, integral_smul_nnreal_measure,
    NNReal.smul_def, smul_eq_mul]
  simp

theorem integral_ind (v : HeightOneSpectrum (𝓞 F)) (l : Measure (Fv F v)) (h : IsStdV v l)
    (c : Fv F v) (hc : c ≠ 0) :
    ∫ y, (if c * y ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0) ∂l = ‖c‖⁻¹ := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hO : MeasurableSet (v.adicCompletionIntegers F : Set (Fv F v)) :=
    (Valued.isOpen_valuationSubring _).measurableSet
  have h0 := integral_mul_fin v l h.1 c hc
    (fun s => if s ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0)
  have h1 : (fun s : Fv F v => if s ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0) =
      (v.adicCompletionIntegers F : Set (Fv F v)).indicator 1 := by
    ext s
    simp [Set.indicator]
  have h2 : ∫ s, (if s ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0) ∂l = 1 := by
    rw [h1, integral_indicator_one hO, Measure.real, h.2]
    simp
  rw [h0, h2, mul_one]

theorem norm_unitInf_inv (a : (AF F)ˣ) :
    ‖(((unitInf a)⁻¹ : (Ainf F)ˣ) : Ainf F)‖ =
      (∏ w : InfinitePlace F, ‖(a : AF F).1 w‖ ^ w.mult)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [InfiniteAdeleRing.norm_def, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun w _ => ?_
  rw [← mul_pow, ← norm_mul]
  have h := IdeleGroup.infinite_mul_inv a w
  have h' : ((a⁻¹ : (AF F)ˣ) : AF F).1 w * (a : AF F).1 w = 1 := by rw [mul_comm]; exact h
  have : (((unitInf a)⁻¹ : (Ainf F)ˣ) : Ainf F) w = ((a⁻¹ : (AF F)ˣ) : AF F).1 w := rfl
  rw [this, h', norm_one, one_pow]

theorem md_eq_of_off (a : (AF F)ˣ) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hoff : ∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧
      ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) :
    md a = (∏ w : InfinitePlace F, ‖(a : AF F).1 w‖ ^ w.mult) * ∏ v ∈ T, ‖(a : AF F).2 v‖ := by
  rw [md, IdeleGroup.ideleModule_eq]
  congr 1
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  by_contra hT
  exact hv (IdeleGroup.norm_eq_one_of_mul_eq_one (IdeleGroup.finite_mul_inv a v)
    (hoff v hT).1 (hoff v hT).2)

theorem integrals_translates : ∀ (F : Type) [Field F] [NumberField F] (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)),
    IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    (∫ y, phiA G a y ∂(Measure.pi fun _ : Unit => li)) * ∏ v ∈ T, ∫ y, psiA S g a v y ∂(Measure.pi fun _ : Unit => lam v) =
      (md a)⁻¹ * ((∫ y, G y ∂li) * ∏ v ∈ S, ∫ s, g v s ∂(lam v)) := by
  intro F _ _ li lam hli hlam S T G g a hST hoff
  haveI := sigmaFinite_inf li hli.1
  have hI : ∫ y, phiA G a y ∂(Measure.pi fun _ : Unit => li) =
      ‖(((unitInf a)⁻¹ : (Ainf F)ˣ) : Ainf F)‖ * ∫ y, G y ∂li :=
    (integral_pi_unit li (fun x => G ((a : AF F).1 * x))).trans
      (integral_mul_inf li hli.1 (unitInf a) G)
  have hv : ∀ v, (a : AF F).2 v ≠ 0 := IdeleGroup.finite_ne_zero a
  have hP : ∀ v ∈ T, ∫ y, psiA S g a v y ∂(Measure.pi fun _ : Unit => lam v) =
      ‖(a : AF F).2 v‖⁻¹ * (if v ∈ S then ∫ s, g v s ∂(lam v) else 1) := by
    intro v _
    haveI := sigmaFinite_fin v (lam v) (hlam v).1
    by_cases hS : v ∈ S
    · have h1 := integral_pi_unit (lam v) (fun x => g v ((a : AF F).2 v * x))
      have h2 := integral_mul_fin v (lam v) (hlam v).1 _ (hv v) (g v)
      simp only [psiA, hS, if_true]
      rw [h1, h2]
    · have h1 := integral_pi_unit (lam v) (fun x =>
        if (a : AF F).2 v * x ∈ v.adicCompletionIntegers F then (1 : ℝ) else 0)
      have h2 := integral_ind v (lam v) (hlam v) _ (hv v)
      simp only [psiA, hS, if_false]
      rw [h1, h2, mul_one]
  have hS' : ∏ v ∈ T, (if v ∈ S then ∫ s, g v s ∂(lam v) else 1) = ∏ v ∈ S, ∫ s, g v s ∂(lam v) := by
    symm
    calc ∏ v ∈ S, ∫ s, g v s ∂(lam v)
        = ∏ v ∈ S, (if v ∈ S then ∫ s, g v s ∂(lam v) else 1) :=
          Finset.prod_congr rfl fun v h => by simp [h]
      _ = _ := Finset.prod_subset hST fun v _ h => by simp [h]
  rw [hI, Finset.prod_congr rfl hP, Finset.prod_mul_distrib, hS', md_eq_of_off a T hoff,
    norm_unitInf_inv, mul_inv, Finset.prod_inv_distrib]
  ring

end GlobalTheory.CompanionTheory.BasePsi.Integrals
end
