import Mathlib

open MeasureTheory Filter Set Topology
open scoped ENNReal RestrictedProduct

namespace GroundTheory.Automorphic

noncomputable section

namespace RestrictedHaar

set_option linter.unusedSectionVars false

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i : Fin n ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i : Fin n ↦ f i.succ) (fun i ↦ hf _)]
          exact lintegral_prod_mul (hf 0).aemeasurable
            (Finset.measurable_prod _ fun (i : Fin n) _ ↦ (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

theorem lintegral_fintype_prod_eq_prod {κ : Type*} [Fintype κ] {E : κ → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : κ) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : κ) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : κ) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin κ).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod (fun i ↦ f (e i)) (fun i ↦ hf _)

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] (C : ∀ i, Subgroup (G i))

def box (T : Finset ι) : Subgroup (Πʳ i, [G i, (C i : Set (G i))]) where
  carrier := {x | ∀ i, i ∉ T → x i ∈ C i}
  one_mem' i _ := by
    show (1 : Πʳ i, [G i, (C i : Set (G i))]) i ∈ C i
    rw [RestrictedProduct.one_apply]
    exact (C i).one_mem
  mul_mem' {x y} hx hy i hi := by
    show (x * y) i ∈ C i
    rw [RestrictedProduct.mul_apply]
    exact (C i).mul_mem (hx i hi) (hy i hi)
  inv_mem' {x} hx i hi := by
    show x⁻¹ i ∈ C i
    rw [RestrictedProduct.inv_apply]
    exact (C i).inv_mem (hx i hi)

theorem mem_box {T : Finset ι} {x : Πʳ i, [G i, (C i : Set (G i))]} :
    x ∈ box C T ↔ ∀ i, i ∉ T → x i ∈ C i := Iff.rfl

theorem box_mono {T T' : Finset ι} (h : T ⊆ T') : box C T ≤ box C T' :=
  fun _ hx i hi ↦ hx i fun hiT ↦ hi (h hiT)

theorem exists_mem_box (x : Πʳ i, [G i, (C i : Set (G i))]) : ∃ T : Finset ι, x ∈ box C T := by
  have hx : {i | ¬ x i ∈ C i}.Finite := Filter.eventually_cofinite.1 x.2
  refine ⟨hx.toFinset, fun i hi ↦ ?_⟩
  by_contra h
  exact hi (hx.mem_toFinset.2 h)

def proj (T : Finset ι) : (Πʳ i, [G i, (C i : Set (G i))]) →* ((i : T) → G i) where
  toFun x i := x i
  map_one' := by
    funext i
    show (1 : Πʳ i, [G i, (C i : Set (G i))]) (i : ι) = 1
    rw [RestrictedProduct.one_apply]
  map_mul' x y := by
    funext i
    show (x * y) (i : ι) = x i * y i
    rw [RestrictedProduct.mul_apply]

theorem proj_apply (T : Finset ι) (x : Πʳ i, [G i, (C i : Set (G i))]) (i : T) : proj C T x i = x i := rfl

open Classical in

def secFun (T : Finset ι) (a : (i : T) → G i) (i : ι) : G i := if h : i ∈ T then a ⟨i, h⟩ else 1

theorem secFun_of_mem {T : Finset ι} (a : (i : T) → G i) {i : ι} (h : i ∈ T) :
    secFun T a i = a ⟨i, h⟩ := by
  classical
  unfold secFun
  rw [dif_pos h]

theorem secFun_of_notMem {T : Finset ι} (a : (i : T) → G i) {i : ι} (h : i ∉ T) :
    secFun T a i = 1 := by
  classical
  unfold secFun
  rw [dif_neg h]

def sec (T : Finset ι) : ((i : T) → G i) →* (Πʳ i, [G i, (C i : Set (G i))]) where
  toFun a := ⟨secFun T a, by
    filter_upwards [T.finite_toSet.compl_mem_cofinite] with i hi
    rw [secFun_of_notMem a (show i ∉ T from hi)]
    exact (C i).one_mem⟩
  map_one' := by
    refine RestrictedProduct.ext _ _ fun i ↦ ?_
    show secFun T 1 i = (1 : Πʳ i, [G i, (C i : Set (G i))]) i
    rw [RestrictedProduct.one_apply]
    by_cases h : i ∈ T
    · rw [secFun_of_mem _ h]
      rfl
    · rw [secFun_of_notMem _ h]
  map_mul' a b := by
    refine RestrictedProduct.ext _ _ fun i ↦ ?_
    show secFun T (a * b) i = secFun T a i * secFun T b i
    by_cases h : i ∈ T
    · rw [secFun_of_mem _ h, secFun_of_mem _ h, secFun_of_mem _ h]
      rfl
    · rw [secFun_of_notMem _ h, secFun_of_notMem _ h, secFun_of_notMem _ h, one_mul]

theorem sec_apply (T : Finset ι) (a : (i : T) → G i) (i : ι) : sec C T a i = secFun T a i := rfl

theorem sec_mem_box (T : Finset ι) (a : (i : T) → G i) : sec C T a ∈ box C T := by
  intro i hi
  rw [sec_apply, secFun_of_notMem a hi]
  exact (C i).one_mem

theorem proj_sec (T : Finset ι) (a : (i : T) → G i) : proj C T (sec C T a) = a := by
  funext i
  rw [proj_apply, sec_apply, secFun_of_mem a i.2]

variable [∀ i, TopologicalSpace (G i)]

theorem continuous_proj (T : Finset ι) : Continuous (proj C T) :=
  continuous_pi fun i ↦ RestrictedProduct.continuous_eval (i : ι)

theorem isOpen_box (hCo : ∀ i, IsOpen (C i : Set (G i))) (T : Finset ι) :
    IsOpen (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) :=
  RestrictedProduct.isOpen_forall_imp_mem (R := G) (A := fun i ↦ (C i : Set (G i))) hCo
    (p := fun i ↦ i ∉ T)

theorem isCompact_box_inter_preimage [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)] (hCo : ∀ i, IsOpen (C i : Set (G i)))
    (hCc : ∀ i, IsCompact (C i : Set (G i))) (T : Finset ι) {E : Set ((i : T) → G i)}
    (hE : IsCompact E) :
    IsCompact ((box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C T ⁻¹' E) := by
  classical
  set S : Set ι := (↑T)ᶜ with hSdef
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.2 T.finite_toSet.compl_mem_cofinite
  set W : Set ((i : ι) → G i) := {x | (fun i : T ↦ x i) ∈ E} ∩ {x | ∀ i ∈ S, x i ∈ C i} with hW
  have hWc : IsCompact W := by
    have hbig : IsCompact (Set.univ.pi fun i ↦
        if h : i ∈ T then (fun a : (j : T) → G j ↦ a ⟨i, h⟩) '' E else (C i : Set (G i))) := by
      refine isCompact_univ_pi fun i ↦ ?_
      split_ifs with h
      · exact hE.image (continuous_apply _)
      · exact hCc i
    refine hbig.of_isClosed_subset ?_ ?_
    · refine IsClosed.inter (hE.isClosed.preimage (continuous_pi fun i ↦ continuous_apply _)) ?_
      simp only [Set.ofPred_forall]
      exact isClosed_biInter fun i _ ↦
        (Subgroup.isClosed_of_isOpen (C i) (hCo i)).preimage (continuous_apply i)
    · rintro x ⟨hxE, hxS⟩ i -
      by_cases h : i ∈ T
      · dsimp only
        rw [dif_pos h]
        exact ⟨_, hxE, rfl⟩
      · dsimp only
        rw [dif_neg h]
        exact hxS i h
  set Z : Set (Πʳ i, [G i, (C i : Set (G i))]_[𝓟 S]) := (fun y ↦ (y : (i : ι) → G i)) ⁻¹' W with hZ
  have hZc : IsCompact Z := by
    rw [(RestrictedProduct.isEmbedding_coe_of_principal (R := G) (A := fun i ↦ (C i : Set (G i)))
      (S := S)).isCompact_iff, hZ, image_preimage_eq_inter_range, RestrictedProduct.range_coe_principal]
    rw [inter_eq_left.2 fun x hx ↦ hx.2]
    exact hWc
  have heq : (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C T ⁻¹' E =
      RestrictedProduct.inclusion G (fun i ↦ (C i : Set (G i))) hS '' Z := by
    ext x
    constructor
    · rintro ⟨hxb, hxE⟩
      refine ⟨⟨x.1, Filter.eventually_principal.2 fun i hi ↦ hxb i hi⟩, ⟨hxE, fun i hi ↦ hxb i hi⟩, ?_⟩
      exact RestrictedProduct.ext _ _ fun i ↦ rfl
    · rintro ⟨y, ⟨hyE, hyS⟩, rfl⟩
      exact ⟨fun i hi ↦ hyS i hi, hyE⟩
  rw [heq]
  exact hZc.image (RestrictedProduct.continuous_inclusion hS)

section Measure

variable [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)] [∀ i, SecondCountableTopology (G i)]
  [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  [MeasurableSpace (Πʳ i, [G i, (C i : Set (G i))])] [BorelSpace (Πʳ i, [G i, (C i : Set (G i))])]

def projMeasure (μ : Measure (Πʳ i, [G i, (C i : Set (G i))])) (T : Finset ι) :
    Measure ((i : T) → G i) :=
  (μ.restrict (box C T : Set (Πʳ i, [G i, (C i : Set (G i))]))).map (proj C T)

theorem projMeasure_apply (μ : Measure (Πʳ i, [G i, (C i : Set (G i))]))
    (T : Finset ι) {E : Set ((i : T) → G i)} (hE : MeasurableSet E) :
    projMeasure C μ T E = μ ((box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C T ⁻¹' E) := by
  have hm : Measurable (proj C T) := (continuous_proj C T).measurable
  rw [projMeasure, Measure.map_apply hm hE, Measure.restrict_apply (hm hE), inter_comm]

theorem isHaarMeasure_projMeasure (hCo : ∀ i, IsOpen (C i : Set (G i)))
    (hCc : ∀ i, IsCompact (C i : Set (G i))) (μ : Measure (Πʳ i, [G i, (C i : Set (G i))]))
    [μ.IsHaarMeasure] (T : Finset ι) : (projMeasure C μ T).IsHaarMeasure := by
  refine { lt_top_of_isCompact := fun K hK ↦ ?_, map_mul_left_eq_self := fun a ↦ ?_,
           open_pos := fun U hU hne ↦ ?_ }
  · rw [projMeasure_apply C μ T hK.isClosed.measurableSet]
    exact (isCompact_box_inter_preimage C hCo hCc T hK).measure_lt_top
  · ext E hE
    rw [Measure.map_apply (measurable_const_mul a) hE,
      projMeasure_apply C μ T (measurable_const_mul a hE), projMeasure_apply C μ T hE]
    have hset : (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C T ⁻¹' ((a * ·) ⁻¹' E) =
        (sec C T a * ·) ⁻¹' ((box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C T ⁻¹' E) := by
      ext x
      simp only [mem_inter_iff, mem_preimage, SetLike.mem_coe, map_mul, proj_sec]
      constructor
      · rintro ⟨hx, hxE⟩
        exact ⟨(box C T).mul_mem (sec_mem_box C T a) hx, hxE⟩
      · rintro ⟨hx, hxE⟩
        refine ⟨?_, hxE⟩
        have := (box C T).mul_mem ((box C T).inv_mem (sec_mem_box C T a)) hx
        rwa [inv_mul_cancel_left] at this
    have : Fact (∀ i, IsOpen (C i : Set (G i))) := ⟨hCo⟩
    have : MeasurableMul (Πʳ i, [G i, (C i : Set (G i))]) :=
      ⟨fun c ↦ (continuous_const_mul c).measurable, fun c ↦ (continuous_mul_const c).measurable⟩
    rw [hset, measure_preimage_mul]
  · rw [projMeasure_apply C μ T hU.measurableSet]
    obtain ⟨a, ha⟩ := hne
    refine ((isOpen_box C hCo T).inter (hU.preimage (continuous_proj C T))).measure_ne_zero μ
      ⟨sec C T a, sec_mem_box C T a, ?_⟩
    show proj C T (sec C T a) ∈ U
    rw [proj_sec]
    exact ha

theorem setOf_forall_mem_eq :
    {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} =
      (box C ∅ : Set (Πʳ i, [G i, (C i : Set (G i))])) ∩ proj C ∅ ⁻¹' univ := by
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, SetLike.mem_coe, mem_box, Finset.notMem_empty,
    not_false_eq_true, true_implies, mem_preimage, mem_univ, and_true]

theorem isCompact_setOf_forall_mem (hCo : ∀ i, IsOpen (C i : Set (G i)))
    (hCc : ∀ i, IsCompact (C i : Set (G i))) :
    IsCompact {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} := by
  rw [setOf_forall_mem_eq]
  refine isCompact_box_inter_preimage C hCo hCc ∅ ?_
  exact Set.Subsingleton.isCompact fun a _ b _ ↦ funext fun i ↦ absurd i.2 (Finset.notMem_empty _)

theorem measure_setOf_forall_mem_pos (hCo : ∀ i, IsOpen (C i : Set (G i)))
    (μ : Measure (Πʳ i, [G i, (C i : Set (G i))])) [μ.IsHaarMeasure] :
    0 < μ {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} := by
  have h : {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} =
      (box C ∅ : Set (Πʳ i, [G i, (C i : Set (G i))])) := by
    ext x
    simp [mem_box]
  rw [h]
  exact (isOpen_box C hCo ∅).measure_pos μ ⟨1, (box C ∅).one_mem⟩

theorem measureReal_setOf_forall_mem_pos (hCo : ∀ i, IsOpen (C i : Set (G i)))
    (hCc : ∀ i, IsCompact (C i : Set (G i))) (μ : Measure (Πʳ i, [G i, (C i : Set (G i))]))
    [μ.IsHaarMeasure] :
    0 < μ.real {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} :=
  ENNReal.toReal_pos (measure_setOf_forall_mem_pos C hCo μ).ne'
    (isCompact_setOf_forall_mem C hCo hCc).measure_lt_top.ne

variable [∀ i, LocallyCompactSpace (G i)]

theorem projMeasure_eq (hCo : ∀ i, IsOpen (C i : Set (G i))) (hCc : ∀ i, IsCompact (C i : Set (G i)))
    (μ : Measure (Πʳ i, [G i, (C i : Set (G i))])) [μ.IsHaarMeasure] (ν : ∀ i, Measure (G i))
    [∀ i, (ν i).IsHaarMeasure] (hν : ∀ i, ν i (C i) = 1) (T : Finset ι) :
    projMeasure C μ T =
      μ {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} • Measure.pi (fun i : T ↦ ν i) := by
  have := isHaarMeasure_projMeasure C hCo hCc μ T
  have h := Measure.isMulLeftInvariant_eq_smul (projMeasure C μ T) (Measure.pi fun i : T ↦ ν i)
  set B : Set ((i : T) → G i) := Set.univ.pi fun i ↦ (C i : Set (G i)) with hBdef
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun i ↦ (hCo i).measurableSet
  have hpi : Measure.pi (fun i : T ↦ ν i) B = 1 := by
    rw [hBdef, Measure.pi_pi]
    simp [hν]
  have hproj : projMeasure C μ T B = μ {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} := by
    rw [projMeasure_apply C μ T hB]
    congr 1
    ext x
    simp only [hBdef, mem_inter_iff, mem_preimage, Set.mem_pi, mem_univ, true_implies, SetLike.mem_coe,
      mem_ofPred_eq, mem_box, proj_apply]
    constructor
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i ∈ T
      · exact h2 ⟨i, hi⟩
      · exact h1 i hi
    · intro h
      exact ⟨fun i _ ↦ h i, fun i ↦ h i⟩
  have hc : ((projMeasure C μ T).haarScalarFactor (Measure.pi fun i : T ↦ ν i) : ℝ≥0∞) =
      μ {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} := by
    have := congrArg (fun m : Measure ((i : T) → G i) ↦ m B) h
    simp only [Measure.smul_apply, hpi, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    rw [← hproj, this]
  conv_lhs => rw [h]
  rw [← hc]
  rfl

theorem setIntegral_box (hCo : ∀ i, IsOpen (C i : Set (G i))) (hCc : ∀ i, IsCompact (C i : Set (G i)))
    (μ : Measure (Πʳ i, [G i, (C i : Set (G i))])) [μ.IsHaarMeasure] (ν : ∀ i, Measure (G i))
    [∀ i, (ν i).IsHaarMeasure] (hν : ∀ i, ν i (C i) = 1) (F : ∀ i, G i → ℂ)
    (hF : ∀ i, Measurable (F i)) (T : Finset ι) (Φ : Πʳ i, [G i, (C i : Set (G i))] → ℂ)
    (hΦ : ∀ x ∈ box C T, Φ x = ∏ i ∈ T, F i (x i)) :
    ∫ x in (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])), Φ x ∂μ =
      μ.real {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} * ∏ i ∈ T, ∫ y, F i y ∂ν i := by
  have hb := (isOpen_box C hCo T).measurableSet
  have hmeas : Measurable fun a : (i : T) → G i ↦ ∏ i : T, F i (a i) :=
    Finset.measurable_prod _ fun i _ ↦ (hF i).comp (measurable_pi_apply i)
  calc ∫ x in (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])), Φ x ∂μ =
        ∫ x in (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])),
          (fun a : (i : T) → G i ↦ ∏ i : T, F i (a i)) (proj C T x) ∂μ := by
        refine setIntegral_congr_fun hb fun x hx ↦ ?_
        rw [hΦ x hx, ← Finset.prod_coe_sort T]
        rfl
    _ = ∫ a, ∏ i : T, F i (a i) ∂projMeasure C μ T := by
        rw [projMeasure, integral_map (continuous_proj C T).measurable.aemeasurable
          hmeas.aestronglyMeasurable]
    _ = _ := by
        rw [projMeasure_eq C hCo hCc μ ν hν T, integral_smul_measure, integral_fintype_prod_eq_prod,
          Finset.prod_coe_sort T (fun i ↦ ∫ y, F i y ∂ν i), Complex.real_smul, measureReal_def]

theorem setLIntegral_box (hCo : ∀ i, IsOpen (C i : Set (G i))) (hCc : ∀ i, IsCompact (C i : Set (G i)))
    (μ : Measure (Πʳ i, [G i, (C i : Set (G i))])) [μ.IsHaarMeasure] (ν : ∀ i, Measure (G i))
    [∀ i, (ν i).IsHaarMeasure] (hν : ∀ i, ν i (C i) = 1) (F : ∀ i, G i → ℂ)
    (hF : ∀ i, Measurable (F i)) (T : Finset ι) (Φ : Πʳ i, [G i, (C i : Set (G i))] → ℂ)
    (hΦ : ∀ x ∈ box C T, Φ x = ∏ i ∈ T, F i (x i)) :
    ∫⁻ x in (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])), ‖Φ x‖ₑ ∂μ =
      μ {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} * ∏ i ∈ T, ∫⁻ y, ‖F i y‖ₑ ∂ν i := by
  have hb := (isOpen_box C hCo T).measurableSet
  have hmeas : Measurable fun a : (i : T) → G i ↦ ∏ i : T, ‖F i (a i)‖ₑ :=
    Finset.measurable_prod _ fun i _ ↦ ((hF i).comp (measurable_pi_apply i)).enorm
  calc ∫⁻ x in (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])), ‖Φ x‖ₑ ∂μ =
        ∫⁻ x in (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])),
          (fun a : (i : T) → G i ↦ ∏ i : T, ‖F i (a i)‖ₑ) (proj C T x) ∂μ := by
        refine setLIntegral_congr_fun hb fun x hx ↦ ?_
        rw [hΦ x hx, ← Finset.prod_coe_sort T]
        simp only [enorm_eq_nnnorm, nnnorm_prod, ENNReal.ofNNReal_finsetProd]
        rfl
    _ = ∫⁻ a, ∏ i : T, ‖F i (a i)‖ₑ ∂projMeasure C μ T := by
        rw [projMeasure, lintegral_map hmeas (continuous_proj C T).measurable]
    _ = _ := by
        rw [projMeasure_eq C hCo hCc μ ν hν T, lintegral_smul_measure,
          lintegral_fintype_prod_eq_prod (fun i : T ↦ fun y ↦ ‖F i y‖ₑ) (fun i ↦ (hF i).enorm),
          Finset.prod_coe_sort T (fun i ↦ ∫⁻ y, ‖F i y‖ₑ ∂ν i), smul_eq_mul]

end Measure

section Product

variable [∀ i, IsTopologicalGroup (G i)] [∀ i, T2Space (G i)] [∀ i, SecondCountableTopology (G i)]
  [∀ i, LocallyCompactSpace (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
  [MeasurableSpace (Πʳ i, [G i, (C i : Set (G i))])] [BorelSpace (Πʳ i, [G i, (C i : Set (G i))])]

theorem finprod_eq_prod_of_mem_box {F : ∀ i, G i → ℂ} {T : Finset ι} (hT : ∀ i ∉ T, ∀ c ∈ C i, F i c = 1)
    {x : Πʳ i, [G i, (C i : Set (G i))]} (hx : x ∈ box C T) :
    ∏ᶠ i, F i (x i) = ∏ i ∈ T, F i (x i) := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun i hi ↦ ?_
  by_contra hiT
  exact hi (hT i hiT _ (hx i hiT))

theorem exists_finset_of_eventually {F : ∀ i, G i → ℂ} (hF1 : ∀ᶠ i in cofinite, ∀ c ∈ C i, F i c = 1) :
    ∃ T₀ : Finset ι, ∀ i ∉ T₀, ∀ c ∈ C i, F i c = 1 := by
  have h := Filter.eventually_cofinite.1 hF1
  refine ⟨h.toFinset, fun i hi ↦ ?_⟩
  by_contra hc
  exact hi (h.mem_toFinset.2 hc)

theorem hasProd_integral [Countable ι] (hCo : ∀ i, IsOpen (C i : Set (G i)))
    (hCc : ∀ i, IsCompact (C i : Set (G i))) (μ : Measure (Πʳ i, [G i, (C i : Set (G i))]))
    [μ.IsHaarMeasure] (ν : ∀ i, Measure (G i)) [∀ i, (ν i).IsHaarMeasure] (hν : ∀ i, ν i (C i) = 1)
    (F : ∀ i, G i → ℂ) (hF : ∀ i, Measurable (F i)) (hF1 : ∀ᶠ i in cofinite, ∀ c ∈ C i, F i c = 1)
    (Φ : Πʳ i, [G i, (C i : Set (G i))] → ℂ) (hΦ : ∀ x, Φ x = ∏ᶠ i, F i (x i)) (hint : Integrable Φ μ) :
    HasProd (fun i ↦ ∫ y, F i y ∂ν i)
      ((μ.real {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i})⁻¹ * ∫ x, Φ x ∂μ) := by
  obtain ⟨T₀, hT₀⟩ := exists_finset_of_eventually C hF1
  have hbox : ∀ T : Finset ι, T₀ ⊆ T → ∀ x ∈ box C T, Φ x = ∏ i ∈ T, F i (x i) := by
    intro T hT x hx
    rw [hΦ x]
    exact finprod_eq_prod_of_mem_box C (fun i hi ↦ hT₀ i fun h ↦ hi (hT h)) hx
  have hU : ⋃ T : Finset ι, (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])) = univ :=
    eq_univ_of_forall fun x ↦ mem_iUnion.2 (exists_mem_box C x)
  have hlim : Tendsto (fun T : Finset ι ↦ ∫ x in (box C T : Set (Πʳ i, [G i, (C i : Set (G i))])), Φ x ∂μ)
      atTop (𝓝 (∫ x, Φ x ∂μ)) := by
    have := tendsto_setIntegral_of_monotone (μ := μ) (f := Φ)
      (fun T ↦ (isOpen_box C hCo T).measurableSet) (fun T T' h ↦ box_mono C h)
      (by rw [hU]; exact hint.integrableOn)
    rwa [hU, Measure.restrict_univ] at this
  have ha := (measureReal_setOf_forall_mem_pos C hCo hCc μ).ne'
  show Tendsto _ atTop _
  refine (hlim.const_mul _).congr' ?_
  filter_upwards [eventually_ge_atTop T₀] with T hT
  rw [setIntegral_box C hCo hCc μ ν hν F hF T Φ (hbox T hT), ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ha,
    Complex.ofReal_one, one_mul]

theorem mul_prod_lintegral_le (hCo : ∀ i, IsOpen (C i : Set (G i)))
    (hCc : ∀ i, IsCompact (C i : Set (G i))) (μ : Measure (Πʳ i, [G i, (C i : Set (G i))]))
    [μ.IsHaarMeasure] (ν : ∀ i, Measure (G i)) [∀ i, (ν i).IsHaarMeasure] (hν : ∀ i, ν i (C i) = 1)
    (F : ∀ i, G i → ℂ) (hF : ∀ i, Measurable (F i)) {T : Finset ι}
    (hT : ∀ i ∉ T, ∀ c ∈ C i, F i c = 1)
    (Φ : Πʳ i, [G i, (C i : Set (G i))] → ℂ) (hΦ : ∀ x, Φ x = ∏ᶠ i, F i (x i)) :
    μ {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} * ∏ i ∈ T, ∫⁻ y, ‖F i y‖ₑ ∂ν i ≤
      ∫⁻ x, ‖Φ x‖ₑ ∂μ := by
  rw [← setLIntegral_box C hCo hCc μ ν hν F hF T Φ fun x hx ↦ by
    rw [hΦ x]; exact finprod_eq_prod_of_mem_box C hT hx]
  exact setLIntegral_le_lintegral _ _

theorem one_le_lintegral (ν : ∀ i, Measure (G i)) (hν : ∀ i, ν i (C i) = 1) (hCo : ∀ i, IsOpen (C i : Set (G i)))
    (F : ∀ i, G i → ℂ) {i : ι} (h : ∀ c ∈ C i, F i c = 1) : 1 ≤ ∫⁻ y, ‖F i y‖ₑ ∂ν i := by
  calc (1 : ℝ≥0∞) = ∫⁻ y in (C i : Set (G i)), 1 ∂ν i := by rw [setLIntegral_const, one_mul, hν]
    _ = ∫⁻ y in (C i : Set (G i)), ‖F i y‖ₑ ∂ν i :=
        setLIntegral_congr_fun (hCo i).measurableSet fun y hy ↦ by rw [h y hy, enorm_one]
    _ ≤ _ := setLIntegral_le_lintegral _ _

theorem integrable_factor (hCo : ∀ i, IsOpen (C i : Set (G i)))
    (hCc : ∀ i, IsCompact (C i : Set (G i))) (μ : Measure (Πʳ i, [G i, (C i : Set (G i))]))
    [μ.IsHaarMeasure] (ν : ∀ i, Measure (G i)) [∀ i, (ν i).IsHaarMeasure] (hν : ∀ i, ν i (C i) = 1)
    (F : ∀ i, G i → ℂ) (hF : ∀ i, Measurable (F i)) (hF1 : ∀ᶠ i in cofinite, ∀ c ∈ C i, F i c = 1)
    (Φ : Πʳ i, [G i, (C i : Set (G i))] → ℂ) (hΦ : ∀ x, Φ x = ∏ᶠ i, F i (x i)) (hint : Integrable Φ μ)
    (hne : ∀ i, (¬ ∀ c ∈ C i, F i c = 1) → ∫⁻ y, ‖F i y‖ₑ ∂ν i ≠ 0) (i : ι) :
    Integrable (F i) (ν i) := by
  classical
  obtain ⟨T₀, hT₀⟩ := exists_finset_of_eventually C hF1
  set T := insert i T₀
  have hT : ∀ j ∉ T, ∀ c ∈ C j, F j c = 1 := fun j hj ↦ hT₀ j fun h ↦ hj (Finset.mem_insert_of_mem h)
  have hpos : ∀ j, ∫⁻ y, ‖F j y‖ₑ ∂ν j ≠ 0 := by
    intro j
    by_cases h : ∀ c ∈ C j, F j c = 1
    · exact (lt_of_lt_of_le one_pos (one_le_lintegral C ν hν hCo F h)).ne'
    · exact hne j h
  have hle := mul_prod_lintegral_le C hCo hCc μ ν hν F hF hT Φ hΦ
  have hfin : μ {x : Πʳ i, [G i, (C i : Set (G i))] | ∀ i, x i ∈ C i} *
      ∏ j ∈ T, ∫⁻ y, ‖F j y‖ₑ ∂ν j ≠ ⊤ := (lt_of_le_of_lt hle hint.2).ne
  have hprod : ∏ j ∈ T, ∫⁻ y, ‖F j y‖ₑ ∂ν j ≠ ⊤ :=
    (ENNReal.lt_top_of_mul_ne_top_right hfin (measure_setOf_forall_mem_pos C hCo μ).ne').ne
  rw [← Finset.mul_prod_erase T _ (Finset.mem_insert_self i T₀)] at hprod
  have hi : ∫⁻ y, ‖F i y‖ₑ ∂ν i < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_left hprod (Finset.prod_ne_zero_iff.2 fun j _ ↦ hpos j)
  exact ⟨(hF i).aestronglyMeasurable, hi⟩

end Product

end RestrictedHaar

end

end GroundTheory.Automorphic
