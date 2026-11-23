import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableEmbeddingAdelicTupleLocalComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictedProductIntegralPureTensorEqProdStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicTupleMeasureExtOfPureTensorIntegralsStatement

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdBasic

theorem repr_map {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E)
    (z : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul]
  | add x y hx hy => simp [hx, hy]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}

def box (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (Fin n → Fin M → AF F ⊗[F] E) :=
  {X | ∀ v ∉ S, projV v (projFin X) ∈ latV b v}

theorem isOpen_box (S : Finset (HeightOneSpectrum (𝓞 F))) : IsOpen (box (n := n) (M := M) b S) := by
  have h : box (n := n) (M := M) b S = ⋂ a, ⋂ i, ⋂ k,
      (fun X : Fin n → Fin M → AF F ⊗[F] E =>
        ((Algebra.TensorProduct.basis (AF F) b).coord k (X a i)).2) ⁻¹'
        {x : Af F | ∀ v, v ∉ S → x.1 v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))} := by
    ext X
    simp only [box, latV, projV, projFin, repr_map, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_preimage]
    exact ⟨fun h a i k v hv => h v hv a i k, fun h v hv a i k => h a i k v hv⟩
  rw [h]
  refine isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun i =>
    isOpen_iInter_of_finite fun k => IsOpen.preimage ?_ ?_
  · have h1 : Continuous ((Algebra.TensorProduct.basis (AF F) b).coord k) :=
      IsModuleTopology.continuous_of_linearMap _
    exact continuous_snd.comp (h1.comp ((continuous_apply i).comp (continuous_apply a)))
  · exact RestrictedProduct.isOpen_forall_imp_mem
      (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun _ => Valued.isOpen_valuationSubring _)

theorem box_mono {S T : Finset (HeightOneSpectrum (𝓞 F))} (h : S ⊆ T) :
    box (n := n) (M := M) b S ⊆ box b T := fun _ hX v hv => hX v fun hs => hv (h hs)

theorem exists_mem_box (X : Fin n → Fin M → AF F ⊗[F] E) : ∃ S, X ∈ box b S := by
  have h := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).2.1
  have hX : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, projV v (projFin X) ∈ latV b v := by
    have h1 := Set.mem_range_self (f := fun X : Fin n → Fin M → AF F ⊗[F] E =>
      (projInf X, fun v : HeightOneSpectrum (𝓞 F) => projV v (projFin X))) X
    rw [h, Set.mem_setOf_eq] at h1
    exact h1
  have hf := Filter.eventually_cofinite.1 hX
  refine ⟨hf.toFinset, fun v hv => ?_⟩
  by_contra h'
  exact hv (by simpa using h')

variable {b} {ν : Measure (Fin n → Fin M → AF F ⊗[F] E)}
  {mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)}
  {mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)}

theorem measure_rect (h : IsProd b ν mi mv) (S : Finset (HeightOneSpectrum (𝓞 F)))
    {Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E)}
    {Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)}
    (hi : MeasurableSet Ai) (hv : ∀ v, MeasurableSet (Av v)) :
    ν ({X | projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v} ∩ box b S) =
      mi Ai * (∏ v ∈ S, mv v (Av v)) * tailProd b mv S := by
  have hm := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).1.measurable
  have hmi : Measurable (projInf (F := F) (E := E) (M := M) (n := n)) := measurable_fst.comp hm
  have hmv : ∀ v : HeightOneSpectrum (𝓞 F),
      Measurable fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X) := fun v =>
    (measurable_pi_apply v).comp (measurable_snd.comp hm)
  have hR : MeasurableSet {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v} := by
    have : {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v} =
        projInf ⁻¹' Ai ∩ ⋂ v ∈ S, (fun X => projV v (projFin X)) ⁻¹' Av v := by
      ext X; simp
    rw [this]
    exact (hmi hi).inter (S.measurableSet_biInter fun v _ => hmv v (hv v))
  have key := h.2 S (Ai.indicator 1) (fun v => (Av v).indicator 1)
    (measurable_const.indicator hi) (fun v => measurable_const.indicator (hv v))
  simp only [lintegral_indicator_one hi, lintegral_indicator_one (hv _)] at key
  rw [← key, ← Measure.restrict_apply hR, ← lintegral_indicator_one hR]
  refine lintegral_congr fun X => ?_
  by_cases hX : projInf X ∈ Ai ∧ ∀ v ∈ S, projV v (projFin X) ∈ Av v
  · rw [Set.indicator_of_mem (by exact hX), Set.indicator_of_mem hX.1,
      Finset.prod_eq_one fun v hv => Set.indicator_of_mem (hX.2 v hv) _]
    simp
  · rw [Set.indicator_of_notMem (by exact hX)]
    rcases not_and_or.1 hX with h1 | h1
    · rw [Set.indicator_of_notMem h1, zero_mul]
    · push Not at h1
      obtain ⟨v, hv, h1⟩ := h1
      rw [Finset.prod_eq_zero hv (Set.indicator_of_notMem h1 _), mul_zero]

theorem exists_tailProd_ne_zero (h : Conv b mi mv) : ∃ S, tailProd b mv S ≠ 0 := by
  have hs := h.2.2
  have ht := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 from one_pos))
  have hf := Filter.eventually_cofinite.1 ht
  refine ⟨hf.toFinset, ?_⟩
  have hpos : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ hf.toFinset},
      0 < (mv v.1 (latV b v.1)).toReal := fun v => by
    have h1 : |(mv v.1 (latV b v.1)).toReal - 1| < 1 := by
      by_contra h'
      exact v.2 (by simpa using h')
    linarith [(abs_lt.1 h1).1]
  have hs' : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ hf.toFinset} =>
      (mv v.1 (latV b v.1)).toReal - 1 := (hs.of_abs).subtype _
  have hl := Real.summable_log_one_add_of_summable hs'
  simp only [add_sub_cancel] at hl
  rw [tailProd, ← Real.rexp_tsum_eq_tprod hpos hl]
  exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

theorem finiteOnCompacts (h : IsProd b ν mi mv) : IsFiniteMeasureOnCompacts ν := by
  classical
  refine ⟨fun K hK => ?_⟩
  obtain ⟨S, hS⟩ := hK.elim_directed_cover (box b) (isOpen_box b)
    (fun X _ => Set.mem_iUnion.2 (exists_mem_box b X))
    (fun S T => ⟨S ∪ T, box_mono b Finset.subset_union_left, box_mono b Finset.subset_union_right⟩)
  have hc := (GlobalTheory.GaugeGlue.adelicTuple_measurableEmbedding F E d b n M).2.2
  have hi := hK.image hc.1
  have hv := fun v => hK.image (hc.2 v)
  have key := measure_rect h S hi.measurableSet (fun v => (hv v).measurableSet)
  haveI := h.1.1
  haveI := h.1.2.1
  refine lt_of_le_of_lt (measure_mono fun X hX => ?_) (key.trans_lt ?_)
  · exact ⟨⟨⟨X, hX, rfl⟩, fun v _ => ⟨X, hX, rfl⟩⟩, hS hX⟩
  · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hi.measure_lt_top
      (ENNReal.prod_lt_top fun v _ => (hv v).measure_lt_top)) ENNReal.ofReal_lt_top

theorem ne_zero (h : IsProd b ν mi mv) (hi : mi ≠ 0) (hv : ∀ v, mv v ≠ 0) : ν ≠ 0 := by
  obtain ⟨S, hS⟩ := exists_tailProd_ne_zero h.1
  have := measure_rect h S (Av := fun _ => Set.univ) MeasurableSet.univ fun _ => MeasurableSet.univ
  rintro rfl
  exact mul_ne_zero (mul_ne_zero (Measure.measure_univ_ne_zero.2 hi)
    (Finset.prod_ne_zero_iff.2 fun v _ => Measure.measure_univ_ne_zero.2 (hv v))) hS this.symm

theorem null (h : IsProd b ν mi mv) (Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E))
    (Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hi : MeasurableSet Ai) (hv : ∀ v, MeasurableSet (Av v)) (zi : mi Aiᶜ = 0)
    (zv : ∀ v, mv v (Av v)ᶜ = 0) :
    ν {X | ¬ (projInf X ∈ Ai ∧ ∀ v, projV v (projFin X) ∈ Av v)} = 0 := by
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have h1 : ∀ S, ν ({X | projInf X ∈ Aiᶜ ∧ ∀ v ∈ S, projV v (projFin X) ∈ Set.univ} ∩ box b S) = 0 :=
    fun S => by
      rw [measure_rect h S (Av := fun _ => Set.univ) hi.compl fun _ => MeasurableSet.univ, zi,
        zero_mul, zero_mul]
  have h2 : ∀ (w : HeightOneSpectrum (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))),
      ν ({X | projInf X ∈ Set.univ ∧ ∀ v ∈ insert w S,
        projV v (projFin X) ∈ (if v = w then (Av v)ᶜ else Set.univ)} ∩ box b (insert w S)) = 0 :=
    fun w S => by
      rw [measure_rect h (insert w S) (Av := fun v => if v = w then (Av v)ᶜ else Set.univ)
        MeasurableSet.univ fun v => by
          split_ifs
          exacts [(hv v).compl, MeasurableSet.univ],
        Finset.prod_eq_zero (Finset.mem_insert_self w S) (by simpa using zv w), mul_zero, zero_mul]
  refine measure_mono_null (fun X hX => ?_) (measure_union_null (measure_iUnion_null h1)
    (measure_iUnion_null fun w => measure_iUnion_null (h2 w)))
  obtain ⟨S, hS⟩ := exists_mem_box b X
  rcases not_and_or.1 hX with h3 | h3
  · exact Or.inl (Set.mem_iUnion.2 ⟨S, ⟨h3, fun _ _ => trivial⟩, hS⟩)
  · obtain ⟨w, hw⟩ := not_forall.1 h3
    refine Or.inr (Set.mem_iUnion₂.2 ⟨w, S, ⟨trivial, fun v _ => ?_⟩,
      box_mono b (Finset.subset_insert w S) hS⟩)
    split_ifs with h4
    · subst h4; exact hw
    · trivial

end GlobalTheory.GaugeEx.ProdBasic

theorem GlobalTheory.GaugeEx.isProd_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsProd b ν mi mv → IsFiniteMeasureOnCompacts ν ∧ (mi ≠ 0 → (∀ v, mv v ≠ 0) → ν ≠ 0) ∧ (∀ ν', IsProd b ν' mi mv → ν' = ν) ∧ ∀ (Ai : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (Av : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), MeasurableSet Ai → (∀ v, MeasurableSet (Av v)) → mi Aiᶜ = 0 → (∀ v, mv v (Av v)ᶜ = 0) → ν {X | ¬ (projInf X ∈ Ai ∧ ∀ v, projV v (projFin X) ∈ Av v)} = 0 := by
  intro F E _ _ _ _ _ d b n M ν mi mv h
  refine ⟨ProdBasic.finiteOnCompacts h, ProdBasic.ne_zero h, fun ν' h' => ?_, ProdBasic.null h⟩
  refine GlobalTheory.T.adelicTupleMeasure_ext_of_pureTensor_integrals F E d b n M ν' ν fun Φ Φi Φf Φv h1 h2 h3 h4 => ?_
  have k := GlobalTheory.T.restrictedProduct_integral_pureTensor_eq_prod F E d b n M ν mi mv h d b Φ Φi Φf Φv h1 h2 h3 h4
  have k' := GlobalTheory.T.restrictedProduct_integral_pureTensor_eq_prod F E d b n M ν' mi mv h' d b Φ Φi Φf Φv h1 h2 h3 h4
  exact ⟨k'.1, k.1, k'.2.2.trans k.2.2.symm⟩
