import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DiagLocal

open MeasureTheory GlobalTheory.DiagForm
open scoped Classical

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

local instance measLoc (v : Pl F) : MeasurableSpace (ι → Fv F v) := borel _
local instance borelLoc (v : Pl F) : BorelSpace (ι → Fv F v) := ⟨rfl⟩

def prj (v : Pl F) (y : ι → Af F) : ι → Fv F v := fun i => evalV F v (y i)

def sgl (v : Pl F) (t : ι → Fv F v) : ι → Af F := fun i => singleFin v (t i)

def intPts (F : Type) [Field F] [NumberField F] (ι : Type) : Set (ι → Af F) :=
  Set.univ.pi fun _ => {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}

def away (v : Pl F) (ι : Type) : Set (ι → Af F) := (fun y => y - sgl v (prj v y)) ⁻¹' intPts F ι

omit [Fintype ι] in
theorem continuous_prj (v : Pl F) : Continuous (prj (ι := ι) v) :=
  continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)

omit [Fintype ι] in
theorem continuous_sgl (v : Pl F) : Continuous (sgl (ι := ι) v) :=
  continuous_pi fun i => (continuous_singleFin v).comp (continuous_apply i)

omit [Fintype ι] in
theorem prj_sgl_add (v : Pl F) (t : ι → Fv F v) (y : ι → Af F) : prj v (sgl v t + y) = t + prj v y := by
  funext i
  simp only [prj, sgl, Pi.add_apply, map_add, evalV_singleFin_self]

omit [Fintype ι] in
theorem sgl_add_mem_away (v : Pl F) (t : ι → Fv F v) (y : ι → Af F) : sgl v t + y ∈ away v ι ↔ y ∈ away v ι := by
  have e : sgl v t + y - sgl v (prj v (sgl v t + y)) = y - sgl v (prj v y) := by
    rw [prj_sgl_add]
    funext i
    simp only [sgl, Pi.add_apply, Pi.sub_apply, map_add]
    abel
  simp only [away, Set.mem_preimage, e]

omit [Fintype ι] in
theorem zero_mem_away (v : Pl F) : (0 : ι → Af F) ∈ away v ι := by
  intro i _ w
  have e : ((0 : ι → Af F) - sgl v (prj v 0) : ι → Af F) i = 0 := by
    show (0 : Af F) - singleFin v (evalV F v 0) = 0
    rw [map_zero, map_zero, sub_zero]
  show ((0 : ι → Af F) - sgl v (prj v 0) : ι → Af F) i w ∈ _
  rw [e]
  exact (w.adicCompletionIntegers F).zero_mem

omit [Fintype ι] in
theorem isCompact_intPts : IsCompact (intPts F ι) := isCompact_univ_pi fun _ => (PI.IntAdCpctOpenWork.main F).2

theorem isClopen_away (v : Pl F) : IsClopen (away v ι) :=
  IsClopen.preimage ⟨isCompact_intPts.isClosed,
    isOpen_set_pi Set.finite_univ fun _ _ => (PI.IntAdCpctOpenWork.main F).1⟩
    (continuous_id.sub ((continuous_sgl v).comp (continuous_prj v)))

omit [Fintype ι] in

theorem exists_compact (v : Pl F) {K : Set (ι → Fv F v)} (hK : IsCompact K) :
    ∃ C : Set (ι → Af F), IsCompact C ∧ prj v ⁻¹' K ∩ away v ι ⊆ C := by
  refine ⟨(fun p : (ι → Fv F v) × (ι → Af F) => sgl v p.1 + p.2) '' (K ×ˢ intPts F ι),
    (hK.prod isCompact_intPts).image (((continuous_sgl v).comp continuous_fst).add continuous_snd), ?_⟩
  rintro y ⟨h1, h2⟩
  exact ⟨(prj v y, y - sgl v (prj v y)), ⟨h1, h2⟩, add_sub_cancel _ _⟩

def ind (v : Pl F) (ι : Type) : (ι → Af F) → ℂ := (away v ι).indicator 1

theorem mul_ind_mem_SB (v : Pl F) {φ : (ι → Fv F v) → ℂ} (hφ : φ ∈ SB (ι → Fv F v)) :
    (fun y => φ (prj v y) * ind v ι y) ∈ SB (ι → Af F) := by
  refine ⟨(hφ.1.comp_continuous (continuous_prj v)).mul
    (LocallyConstant.indicator (1 : LocallyConstant _ ℂ) (isClopen_away v)).isLocallyConstant, ?_⟩
  obtain ⟨C, hC, h⟩ := exists_compact v hφ.2.isCompact
  refine HasCompactSupport.intro hC fun y hy => ?_
  by_contra h0
  refine hy (h ⟨subset_tsupport _ (left_ne_zero_of_mul h0), ?_⟩)
  by_contra h1
  exact right_ne_zero_of_mul h0 (Set.indicator_of_notMem h1 _)

def muLoc (v : Pl F) (ι : Type) [Fintype ι] : Measure (ι → Fv F v) :=
  ((Measure.addHaar : Measure (Vf F ι)).restrict (away v ι)).map (prj v)

theorem muLoc_apply (v : Pl F) {s : Set (ι → Fv F v)} (hs : MeasurableSet s) :
    muLoc v ι s = (Measure.addHaar : Measure (Vf F ι)) (prj v ⁻¹' s ∩ away v ι) := by
  rw [muLoc, Measure.map_apply (continuous_prj v).measurable hs,
    Measure.restrict_apply ((continuous_prj v).measurable hs)]

theorem isAddHaarMeasure_muLoc (v : Pl F) : (muLoc v ι).IsAddHaarMeasure where
  lt_top_of_isCompact K hK := by
    obtain ⟨C, hC, h⟩ := exists_compact v hK
    rw [muLoc_apply v hK.isClosed.measurableSet]
    exact (measure_mono h).trans_lt hC.measure_lt_top
  map_add_left_eq_self t := by
    refine Measure.ext fun s hs => ?_
    have hm : Measurable fun x : ι → Fv F v => t + x := (continuous_const.add continuous_id).measurable
    rw [Measure.map_apply hm hs, muLoc_apply v hs, muLoc_apply v (hm hs),
      ← measure_preimage_add _ (sgl v t) (prj v ⁻¹' s ∩ away v ι)]
    congr 1
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, prj_sgl_add, sgl_add_mem_away]
  open_pos U hU hne := by
    obtain ⟨t, ht⟩ := hne
    rw [muLoc_apply v hU.measurableSet]
    refine ((hU.preimage (continuous_prj v)).inter (isClopen_away v).isOpen).measure_ne_zero _
      ⟨sgl v t + 0, ?_, (sgl_add_mem_away v t 0).2 (zero_mem_away v)⟩
    have e : prj v (0 : ι → Af F) = 0 := funext fun i => map_zero _
    rw [Set.mem_preimage, prj_sgl_add, e, add_zero]
    exact ht

theorem integral_muLoc (v : Pl F) {φ : (ι → Fv F v) → ℂ} (hφ : Continuous φ) :
    ∫ x, φ x ∂(muLoc v ι) = ∫ y : Vf F ι, φ (prj v y) * ind v ι y ∂Measure.addHaar := by
  rw [muLoc, integral_map (continuous_prj v).measurable.aemeasurable hφ.aestronglyMeasurable,
    ← integral_indicator (isClopen_away v).isOpen.measurableSet]
  congr 1
  funext y
  by_cases hy : y ∈ away v ι <;> simp [ind, hy]

theorem ind_diag (v : Pl F) (y : ι → Af F) : ind v (ι ⊕ ι) (Sum.elim y y) = ind v ι y := by
  have e : Sum.elim y y ∈ away v (ι ⊕ ι) ↔ y ∈ away v ι :=
    ⟨fun h i _ => h (Sum.inl i) trivial, fun h i _ => by cases i <;> exact h _ trivial⟩
  simp only [ind, Set.indicator_apply, e, Pi.one_apply]

omit [Fintype ι] in
theorem tens_pureA (v : Pl F) (φ : (ι → Fv F v) → ℂ) (f : (ι → mixedEmbedding.mixedSpace F) → ℂ) (g : (ι → Af F) → ℂ) :
    tens (evFin F v) φ (pureA F f g) = pureA F f fun y => φ (prj v y) * g y := by
  funext x
  exact mul_left_comm _ _ _

omit [Fintype ι] in
theorem pureA_ind_add (v : Pl F) (f : (ι → mixedEmbedding.mixedSpace F) → ℂ) (x z : ι → AF F)
    (hz : At (evFin F v) z) : pureA F f (ind v ι) (x + z) = pureA F f (ind v ι) x := by
  have h := hz (1 - pairA F 0 (singleFin v 1)) (by
    rw [map_sub, map_one]
    exact sub_eq_zero.2 (evalV_singleFin_self v 1).symm)
  have h1 : ∀ i, z i = pairA F 0 (singleFin v 1) * z i := fun i => by
    have := congrFun h i
    rwa [Pi.smul_apply, smul_eq_mul, sub_mul, one_mul, Pi.zero_apply, sub_eq_zero] at this
  have h2 : ∀ i, (z i).1 = 0 := fun i => (congrArg Prod.fst (h1 i)).trans (zero_mul _)
  have h3 : ∀ i, (z i).2 = singleFin v (evalV F v (z i).2) := fun i => by
    refine (congrArg Prod.snd (h1 i)).trans (af_ext fun u => ?_)
    show evalV F u (singleFin v 1 * (z i).2) = _
    rw [map_mul]
    by_cases hu : u = v
    · subst hu
      rw [evalV_singleFin_self, evalV_singleFin_self, one_mul]
    · rw [evalV_singleFin_ne hu, evalV_singleFin_ne hu, zero_mul]
  have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + z) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (z i).1) = _
    rw [h2, add_zero]
  have e2 : (fun i => ((x + z) i).2) = sgl v (fun i => evalV F v (z i).2) + fun i => (x i).2 := by
    funext i
    show (x i).2 + (z i).2 = singleFin v (evalV F v (z i).2) + (x i).2
    rw [← h3, add_comm]
  simp only [pureA]
  rw [e1, e2]
  simp only [ind, Set.indicator_apply, sgl_add_mem_away, Pi.one_apply]

theorem exists_arch : ∃ f : SchwartzMap (ι ⊕ ι → mixedEmbedding.mixedSpace F) ℂ,
    SchwartzMap.integralCLM ℂ (volume : Measure (Vi F ι)) (compD F ι f) ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨φ, hφ, h0⟩ := exists_lDiag_ne (F := F) (κ := ι)
  refine h0 ((Submodule.span_le (p := LinearMap.ker (lDiag F ι))).2 ?_ hφ)
  rintro _ ⟨f, g, hg, rfl⟩
  show lDiag F ι _ = 0
  rw [lDiag_pureA f hg, h, mul_zero]

theorem exists_local (v : Pl F) : ∃ r₀ : (ι ⊕ ι → AF F) → ℂ, (∀ φ ∈ SB (ι ⊕ ι → Fv F v), Rest (evFin F v) φ r₀) ∧
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∃ μ : Measure (ι → Fv F v), μ.IsAddHaarMeasure ∧
      (∀ φ ∈ SB (ι ⊕ ι → Fv F v), lDiag F ι (tens (evFin F v) φ r₀) = c₀ * ∫ x, φ (Sum.elim x x) ∂μ) ∧
      ∃ φ₀ ∈ SB (ι → Fv F v), ∫ x, φ₀ x * φ₀ x ∂μ ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_arch (F := F) (ι := ι)
  haveI := isAddHaarMeasure_muLoc (ι := ι) v
  refine ⟨pureA F f (ind v _), fun φ hφ => ⟨pureA_ind_add v f, ?_⟩, _, hf, muLoc v ι, this, fun φ hφ => ?_, ?_⟩
  · rw [tens_pureA]
    exact Submodule.subset_span ⟨f, _, mul_ind_mem_SB v hφ, rfl⟩
  · have hd : Continuous fun x : ι → Fv F v => (Sum.elim x x : ι ⊕ ι → Fv F v) :=
      continuous_pi fun i => by cases i <;> exact continuous_apply _
    rw [tens_pureA, lDiag_pureA f (mul_ind_mem_SB v hφ), mul_comm,
      integral_muLoc v (φ := fun x => φ (Sum.elim x x)) (hφ.1.continuous.comp hd)]
    congr 2
    funext y
    rw [ind_diag]
    congr 2
    funext i
    cases i <;> rfl
  · have h := GlobalTheory.StdVacuum.indicator_mem_SB (κ := ι) v
    set B := {x : ι → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F}
    refine ⟨_, h, ?_⟩
    have hB : B = B.indicator (1 : (ι → Fv F v) → ℂ) ⁻¹' {1} := by
      ext y
      by_cases hy : y ∈ B <;> simp [hy]
    have ho : IsOpen B := by rw [hB]; exact h.1.isOpen_fiber 1
    have hc : IsCompact (closure B) := by
      have h2 := h.2
      unfold HasCompactSupport tsupport at h2
      rwa [Set.support_indicator, Function.support_one, Set.inter_univ] at h2
    have e : (fun x => B.indicator (1 : (ι → Fv F v) → ℂ) x * B.indicator 1 x) = B.indicator fun _ => (1 : ℂ) := by
      funext y
      by_cases hy : y ∈ B <;> simp [hy]
    rw [e, integral_indicator_const _ ho.measurableSet]
    have hpos : 0 < muLoc v ι B := ho.measure_pos _ ⟨0, fun _ => zero_mem _⟩
    have hfin : muLoc v ι B < ⊤ := (measure_mono subset_closure).trans_lt hc.measure_lt_top
    have : 0 < (muLoc v ι).real B := ENNReal.toReal_pos hpos.ne' hfin.ne
    simpa using this.ne'

end GlobalTheory.DiagLocal

theorem GlobalTheory.DiagLocal.exists_diag_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (a a' : ℕ) (G : Geo σ a a') (ψ : AddChar (AF F) ℂ)
    (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a')))
    (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd → ∀ v : Pl F,
    ∃ l ∈ (adeleClass F).adm ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))),
      (∀ z : Matrix (Fin (a + a')) (Fin a') (AE F E), ∀ φ ∈ (adeleClass F).sp ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))),
        l (dd.rho ψ (z * (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (AE F E))ᵀ) φ) = l φ) ∧
      ∃ r₀ : ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ, (∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), Rest (evFin F v) φ r₀) ∧
      ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∃ μ : @MeasureTheory.Measure ((Fin a' × Fin (a + a')) → Fv F v) (borel _),
        @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
        (∀ φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v), l (tens (evFin F v) φ r₀) = c₀ * ∫ x, φ (Sum.elim x x) ∂μ) ∧
        ∃ φ₀ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∫ x, φ₀ x * φ₀ x ∂μ ≠ 0 := by
  intro F E _ _ _ _ _ σ a a' G ψ d' dd hdd v
  refine ⟨GlobalTheory.DiagForm.lDiag F _, GlobalTheory.DiagForm.lDiag_adm, fun z φ hφ => ?_, GlobalTheory.DiagLocal.exists_local v⟩
  have e : z * (diagCols (Fin a') : Matrix (Fin a' ⊕ Fin a') (Fin a') (AE F E))ᵀ = Matrix.fromCols z z := by
    rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
  rw [e, Darboux.rho, hdd z z]
  exact GlobalTheory.DiagForm.lDiag_schr ψ _ _ hφ

end
