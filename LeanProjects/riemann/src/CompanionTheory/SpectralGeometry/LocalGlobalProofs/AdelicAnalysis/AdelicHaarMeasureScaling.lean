import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Core.Scale

variable {F : Type} [Field F] [NumberField F]

lemma one_mem_Oh : (1 : A F) ∈ Oh F := fun v => by
  show (1 : v.adicCompletion F) ∈ v.adicCompletionIntegers F
  exact one_mem _

lemma add_mem_Oh {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x + y ∈ Oh F := fun v =>
  add_mem (hx v) (hy v)

lemma neg_mem_Oh {x : A F} (hx : x ∈ Oh F) : -x ∈ Oh F := fun v =>
  neg_mem (hx v)

lemma zero_mem_Oh : (0 : A F) ∈ Oh F := fun v =>
  (v.adicCompletionIntegers F).zero_mem

def OhSub (F : Type) [Field F] [NumberField F] : AddSubgroup (A F) where
  carrier := Oh F
  add_mem' := add_mem_Oh
  zero_mem' := zero_mem_Oh
  neg_mem' := neg_mem_Oh

def ι (r : 𝓞 F) : A F := algebraMap F (A F) (r : F)

lemma ι_mem (r : 𝓞 F) : ι r ∈ Oh F :=
  ((GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1 _).2 ⟨r, rfl⟩

lemma ι_sub (r s : 𝓞 F) : ι r - ι s = ι (r - s) := by
  simp [ι]

theorem mass_of_subgroup [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F))
    (hlf : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1) (H : AddSubgroup (A F))
    (hHo : IsOpen (H : Set (A F))) (hHs : ∀ x ∈ H, x ∈ Oh F) (I : Ideal (𝓞 F))
    (hI : ∀ r : 𝓞 F, r ∈ I ↔ ι r ∈ H) (hI0 : I ≠ ⊥) :
    lf (H : Set (A F)) = ((Ideal.absNorm I : ℝ≥0∞))⁻¹ := by
  obtain ⟨-, -, -, -, hOo, hd, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : IsTopologicalRing (A F) := inferInstance
  have : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI0
  haveI := Fintype.ofFinite (𝓞 F ⧸ I)
  let rep : (𝓞 F ⧸ I) → 𝓞 F := fun t => Quotient.out t
  have hrep : ∀ t, Ideal.Quotient.mk I (rep t) = t := fun t => Ideal.Quotient.mk_out t
  let C : (𝓞 F ⧸ I) → Set (A F) := fun t => (fun x => x - ι (rep t)) ⁻¹' (H : Set (A F))
  have hCm : ∀ t, MeasurableSet (C t) := fun t =>
    ((hHo.preimage (continuous_id.sub continuous_const))).measurableSet
  have hCl : ∀ t, lf (C t) = lf (H : Set (A F)) := fun t => by
    simpa [C, sub_eq_add_neg] using measure_preimage_add_right lf (-ι (rep t)) (H : Set (A F))
  have hdisj : Pairwise (Function.onFun Disjoint C) := by
    intro t t' htt
    refine Set.disjoint_left.2 fun x hx hx' => htt ?_
    have h : ι (rep t' - rep t) ∈ H := by
      rw [← ι_sub]
      have := H.sub_mem hx hx'
      simpa using this
    have := (hI _).2 h
    rw [← hrep t, ← hrep t']
    exact ((Ideal.Quotient.eq).2 this).symm
  have hU : Oh F = ⋃ t, C t := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      have hop : IsOpen ((fun y => y - x) ⁻¹' (H : Set (A F))) :=
        hHo.preimage (continuous_id.sub continuous_const)
      obtain ⟨f, hf⟩ := hd.exists_mem_open hop ⟨x, by simpa using H.zero_mem⟩
      have hfO : algebraMap F (A F) f ∈ Oh F := by
        have := add_mem_Oh (hHs _ hf) hx
        simpa using this
      obtain ⟨r, rfl⟩ := (hint f).1 hfO
      refine ⟨Ideal.Quotient.mk I r, ?_⟩
      have h2 : rep (Ideal.Quotient.mk I r) - r ∈ I :=
        Ideal.Quotient.eq.1 (hrep _)
      have h3 := (hI _).1 h2
      rw [← ι_sub] at h3
      have h4 := H.neg_mem (H.add_mem hf h3)
      show x - ι (rep (Ideal.Quotient.mk I r)) ∈ H
      convert h4 using 1
      simp only [ι]
      abel
    · rintro ⟨t, ht⟩
      have := add_mem_Oh (hHs _ ht) (ι_mem (rep t))
      simpa using this
  have hsum : (1 : ℝ≥0∞) = (Ideal.absNorm I : ℝ≥0∞) * lf (H : Set (A F)) := by
    rw [← h1, hU, measure_iUnion hdisj hCm, tsum_fintype]
    simp only [hCl, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 2
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum.symm)

lemma mul_mem_Oh {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x * y ∈ Oh F := fun v =>
  mul_mem (hx v) (hy v)

def uF (c : F) (hc : c ≠ 0) : (A F)ˣ :=
  Units.map (algebraMap F (A F)).toMonoidHom (Units.mk0 c hc)

lemma uF_val (c : F) (hc : c ≠ 0) : ((uF c hc : (A F)ˣ) : A F) = algebraMap F (A F) c := rfl

def mulEquiv (a : (A F)ˣ) : A F ≃+ A F where
  toFun x := (a : A F) * x
  invFun x := ((a⁻¹ : (A F)ˣ) : A F) * x
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := mul_add _ _ _

lemma continuous_mulEquiv (a : (A F)ˣ) : Continuous (mulEquiv a) :=
  continuous_const.mul continuous_id

lemma continuous_mulEquiv_symm (a : (A F)ˣ) : Continuous (mulEquiv a).symm :=
  continuous_const.mul continuous_id

lemma isOpen_image_mul (a : (A F)ˣ) {s : Set (A F)} (hs : IsOpen s) :
    IsOpen ((fun x => (a : A F) * x) '' s) := by
  have h : (fun x => (a : A F) * x) '' s = (mulEquiv a).symm ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mulEquiv] using hy
    · intro hx
      exact ⟨_, hx, (mulEquiv a).apply_symm_apply x⟩
  rw [h]
  exact hs.preimage (continuous_mulEquiv_symm a)

theorem scale_unit [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F))
    (hlf : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1) (a : (A F)ˣ) (s : Set (A F))
    (hs : MeasurableSet s) :
    lf ((fun x => (a : A F) * x) '' s) = lf ((fun x => (a : A F) * x) '' Oh F) * lf s := by
  obtain ⟨hlc, hsc, ht2, -, hOo, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hμ : (lf.map (mulEquiv a).symm).IsAddHaarMeasure :=
    (mulEquiv a).symm.isAddHaarMeasure_map lf (continuous_mulEquiv_symm a) (continuous_mulEquiv a)
  have hm : Measurable (mulEquiv a).symm := (continuous_mulEquiv_symm a).measurable
  have himg : ∀ t : Set (A F), (fun x => (a : A F) * x) '' t = (mulEquiv a).symm ⁻¹' t := by
    intro t
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mulEquiv] using hy
    · intro hx
      exact ⟨_, hx, (mulEquiv a).apply_symm_apply x⟩
  have hval : ∀ t : Set (A F), MeasurableSet t →
      lf ((fun x => (a : A F) * x) '' t) = (lf.map (mulEquiv a).symm) t := by
    intro t ht
    rw [Measure.map_apply hm ht, himg]
  obtain ⟨k, hk⟩ : ∃ k : ℝ≥0, lf.map (mulEquiv a).symm = k • lf :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (lf.map (mulEquiv a).symm) lf⟩
  have hc : ∀ t : Set (A F), MeasurableSet t → lf ((fun x => (a : A F) * x) '' t) =
      (k : ℝ≥0∞) * lf t := by
    intro t ht
    rw [hval t ht, hk, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [hc s hs, hc _ hOo.measurableSet, h1, mul_one]

theorem mass_mul_int [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F))
    (hlf : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1) (r : 𝓞 F) (hr : (r : F) ≠ 0) :
    lf ((fun x => algebraMap F (A F) (r : F) * x) '' Oh F) =
      (((Algebra.norm ℤ r).natAbs : ℝ≥0∞))⁻¹ := by
  obtain ⟨-, -, -, -, hOo, -, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hr0 : r ≠ 0 := fun h => hr (by simp [h])
  let H : AddSubgroup (A F) := (OhSub F).map (AddMonoidHom.mulLeft (ι r))
  have hH : (H : Set (A F)) = (fun x => algebraMap F (A F) (r : F) * x) '' Oh F := rfl
  have hHo : IsOpen (H : Set (A F)) := by
    rw [hH]
    exact isOpen_image_mul (uF (r : F) hr) hOo
  have key := mass_of_subgroup lf hlf h1 H hHo ?_ (Ideal.span {r}) ?_ ?_
  · rw [hH] at key
    rw [key, Ideal.absNorm_span_singleton]
  · rintro x ⟨y, hy, rfl⟩
    exact mul_mem_Oh (ι_mem r) hy
  · intro s
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨ι t, ι_mem t, ?_⟩
      simp [ι, mul_comm]
    · rintro ⟨y, hy, hys⟩
      have hys' : algebraMap F (A F) (r : F) * y = algebraMap F (A F) (s : F) := hys
      have hy' : y = algebraMap F (A F) ((s : F) / r) := by
        have hu : algebraMap F (A F) (r : F) * algebraMap F (A F) ((r : F)⁻¹) = 1 := by
          rw [← map_mul, mul_inv_cancel₀ hr, map_one]
        calc y = (algebraMap F (A F) (r : F) * algebraMap F (A F) ((r : F)⁻¹)) * y := by
              rw [hu, one_mul]
          _ = algebraMap F (A F) ((r : F)⁻¹) * (algebraMap F (A F) (r : F) * y) := by ring
          _ = _ := by rw [hys', ← map_mul, div_eq_mul_inv, mul_comm]
      rw [hy'] at hy
      obtain ⟨t, ht⟩ := (hint _).1 hy
      refine ⟨t, ?_⟩
      apply RingOfIntegers.coe_injective
      show (t : F) * (r : F) = (s : F)
      rw [ht]
      field_simp
  · simpa [Ideal.span_singleton_eq_bot] using hr0

def denSub (b : F) : AddSubgroup (A F) where
  carrier := {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F}
  add_mem' := fun {x y} hx hy => ⟨add_mem_Oh hx.1 hy.1, by
    rw [mul_add]; exact add_mem_Oh hx.2 hy.2⟩
  zero_mem' := ⟨zero_mem_Oh, by rw [mul_zero]; exact zero_mem_Oh⟩
  neg_mem' := fun {x} hx => ⟨neg_mem_Oh hx.1, by
    rw [mul_neg]; exact neg_mem_Oh hx.2⟩

lemma isOpen_denSub (b : F) : IsOpen (denSub b : Set (A F)) := by
  obtain ⟨-, -, -, -, hOo, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hc : Continuous (fun x : A F => algebraMap F (A F) b * x) :=
    continuous_const.mul continuous_id
  have h2 : IsOpen ((fun x : A F => algebraMap F (A F) b * x) ⁻¹' Oh F) := hOo.preimage hc
  have h3 := hOo.inter h2
  have h4 : (denSub b : Set (A F)) = Oh F ∩ ((fun x : A F => algebraMap F (A F) b * x) ⁻¹' Oh F) :=
    Set.ext fun x => Iff.rfl
  rw [h4]
  exact h3

def denI (b : F) : Ideal (𝓞 F) :=
  Submodule.comap (LinearMap.toSpanSingleton (𝓞 F) F b) (1 : Submodule (𝓞 F) F)

lemma mem_denI (b : F) (r : 𝓞 F) : r ∈ denI b ↔ ∃ t : 𝓞 F, (t : F) = (r : F) * b := by
  unfold denI
  rw [Submodule.mem_comap, Submodule.mem_one]
  simp [Algebra.smul_def]

lemma denI_ne_bot (b : F) : denI b ≠ ⊥ := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 F) b
  intro hbot
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyF : (y : F) ≠ 0 := fun h => hy0 (RingOfIntegers.coe_injective (by simpa using h))
  have hmem : y ∈ denI b := by
    rw [mem_denI]
    refine ⟨x, ?_⟩
    rw [← hxy]
    show (x : F) = (y : F) * ((x : F) / (y : F))
    field_simp
  rw [hbot] at hmem
  exact hy0 (by simpa using hmem)

lemma mem_denI_iff_sub (b : F) (r : 𝓞 F) : r ∈ denI b ↔ ι r ∈ denSub b := by
  have hint := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.2.2.1
  rw [mem_denI]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨ι_mem r, ?_⟩
    have h : algebraMap F (A F) b * ι r = ι t := by
      simp only [ι]
      rw [ht, ← map_mul, mul_comm]
    rw [h]
    exact ι_mem t
  · rintro ⟨-, h⟩
    have h' : algebraMap F (A F) ((r : F) * b) ∈ Oh F := by
      rw [mul_comm, map_mul]; exact h
    exact (hint _).1 h'

theorem mass_den [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F))
    (hlf : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1) (b : F) :
    lf {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} = ((den b : ℝ≥0∞))⁻¹ :=
  mass_of_subgroup lf hlf h1 (denSub b) (isOpen_denSub b) (fun _ hx => hx.1) (denI b)
    (mem_denI_iff_sub b) (denI_ne_bot b)

theorem scale_field [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F))
    (hlf : lf.IsAddHaarMeasure) (h1 : lf (Oh F) = 1) (c : F) (hc : c ≠ 0) (s : Set (A F))
    (hs : MeasurableSet s) :
    lf ((fun x => algebraMap F (A F) c * x) '' s) =
      ENNReal.ofReal (|((Algebra.norm ℚ c : ℚ) : ℝ)|⁻¹) * lf s := by
  have hOo := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).2.2.2.2.1
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 F) c
  have hxy' : (x : F) / (y : F) = c := hxy
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyF : (y : F) ≠ 0 := fun h => hy0 (RingOfIntegers.coe_injective (by simpa using h))
  have hxF : (x : F) ≠ 0 := by
    intro h
    rw [h, zero_div] at hxy'
    exact hc hxy'.symm
  have hx0 : x ≠ 0 := fun h => hxF (by simp [h])
  have hnx : (Algebra.norm ℤ x).natAbs ≠ 0 := by
    simpa [Algebra.norm_eq_zero_iff] using hx0
  have hny : (Algebra.norm ℤ y).natAbs ≠ 0 := by
    simpa [Algebra.norm_eq_zero_iff] using hy0
  have hcy : (fun z => algebraMap F (A F) (x : F) * z) '' Oh F =
      (fun z => algebraMap F (A F) c * z) ''
        ((fun z => algebraMap F (A F) (y : F) * z) '' Oh F) := by
    rw [Set.image_image]
    refine Set.image_congr fun z _ => ?_
    rw [← mul_assoc, ← map_mul, ← hxy']
    congr 2
    field_simp
  have hm : MeasurableSet ((fun z => algebraMap F (A F) (y : F) * z) '' Oh F) :=
    (isOpen_image_mul (uF (y : F) hyF) hOo).measurableSet
  have h2 := scale_unit lf hlf h1 (uF c hc) _ hm
  simp only [uF_val] at h2
  rw [← hcy, mass_mul_int lf hlf h1 x hxF, mass_mul_int lf hlf h1 y hyF] at h2
  have hφ : lf ((fun z => algebraMap F (A F) c * z) '' Oh F) =
      ENNReal.ofReal (|((Algebra.norm ℚ c : ℚ) : ℝ)|⁻¹) := by
    have hnorm : |((Algebra.norm ℚ c : ℚ) : ℝ)|⁻¹ =
        ((Algebra.norm ℤ y).natAbs : ℝ) / ((Algebra.norm ℤ x).natAbs : ℝ) := by
      have hmul : Algebra.norm ℚ c * Algebra.norm ℚ (y : F) = Algebra.norm ℚ (x : F) := by
        rw [← map_mul, ← hxy']
        congr 1
        field_simp
      rw [← Algebra.coe_norm_int, ← Algebra.coe_norm_int] at hmul
      have hmulR : ((Algebra.norm ℚ c : ℚ) : ℝ) * ((Algebra.norm ℤ y : ℤ) : ℝ) =
          ((Algebra.norm ℤ x : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) hmul
      have hYp : (0 : ℝ) < ((Algebra.norm ℤ y).natAbs : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hny
      have hXp : (0 : ℝ) < ((Algebra.norm ℤ x).natAbs : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hnx
      have habs : |((Algebra.norm ℚ c : ℚ) : ℝ)| * ((Algebra.norm ℤ y).natAbs : ℝ) =
          ((Algebra.norm ℤ x).natAbs : ℝ) := by
        rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs, ← abs_mul, hmulR]
      rw [← habs]
      have hC : |((Algebra.norm ℚ c : ℚ) : ℝ)| ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at habs
        exact hXp.ne habs
      field_simp
    rw [hnorm, ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hnx),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, div_eq_mul_inv]
    have hyne : (((Algebra.norm ℤ y).natAbs : ℝ≥0∞)) ≠ 0 := by exact_mod_cast hny
    have hyt : (((Algebra.norm ℤ y).natAbs : ℝ≥0∞)) ≠ ∞ := ENNReal.natCast_ne_top _
    rw [h2, mul_left_comm, ENNReal.mul_inv_cancel hyne hyt, mul_one]
  have h3 := scale_unit lf hlf h1 (uF c hc) s hs
  simp only [uF_val] at h3
  rw [h3, hφ]

theorem lf_scale : ∀ (F : Type) [Field F] [NumberField F], ∀ [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → (∀ (c : F), c ≠ 0 → ∀ s : Set (A F), MeasurableSet s → lf ((fun x => algebraMap F (A F) c * x) '' s) = ENNReal.ofReal (|((Algebra.norm ℚ c : ℚ) : ℝ)|⁻¹) * lf s) ∧ (∀ b : F, lf {x | x ∈ Oh F ∧ algebraMap F (A F) b * x ∈ Oh F} = ((den b : ℝ≥0∞))⁻¹) ∧ ∀ (a : (A F)ˣ) (s : Set (A F)), MeasurableSet s → lf ((fun x => (a : A F) * x) '' s) = lf ((fun x => (a : A F) * x) '' Oh F) * lf s := by
  intro F _ _ _ _ lf hlf h1
  exact ⟨fun c hc s hs => scale_field lf hlf h1 c hc s hs, fun b => mass_den lf hlf h1 b,
    fun a s hs => scale_unit lf hlf h1 a s hs⟩

end GlobalTheory.CompanionTheory.SW.Core.Scale
