import Mathlib

noncomputable section

namespace GlobalTheory.RestrMeas

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal

section Cyl

variable {X W V : Type} {Ya : W → Type} {Yf : V → Type}

def cyl (pa : ∀ w, X → Ya w) (pf : ∀ v, X → Yf v) (K : ∀ v, Set (Yf v)) (S : Finset V)
    (A : ∀ w, Set (Ya w)) (B : ∀ v, Set (Yf v)) : Set X :=
  {x | (∀ w, pa w x ∈ A w) ∧ (∀ v ∈ S, pf v x ∈ B v) ∧ ∀ v ∉ S, pf v x ∈ K v}

variable {pa : ∀ w, X → Ya w} {pf : ∀ v, X → Yf v} {K K' : ∀ v, Set (Yf v)}

theorem mem_cyl {S : Finset V} {A : ∀ w, Set (Ya w)} {B : ∀ v, Set (Yf v)} {x : X} :
    x ∈ cyl pa pf K S A B ↔ (∀ w, pa w x ∈ A w) ∧ (∀ v ∈ S, pf v x ∈ B v) ∧ ∀ v ∉ S, pf v x ∈ K v := Iff.rfl

theorem cyl_self (S : Finset V) (A : ∀ w, Set (Ya w)) :
    cyl pa pf K S A K = {x | (∀ w, pa w x ∈ A w) ∧ ∀ v, pf v x ∈ K v} :=
  Set.ext fun _ => and_congr_right fun _ =>
    ⟨fun h v => (Classical.em (v ∈ S)).elim (h.1 v) (h.2 v), fun h => ⟨fun v _ => h v, fun v _ => h v⟩⟩

open Classical in

theorem cyl_eq_of_subset {S T : Finset V} (h : S ⊆ T) (hK : ∀ v ∉ T, K v = K' v) (A : ∀ w, Set (Ya w))
    (B : ∀ v, Set (Yf v)) : cyl pa pf K' S A B = cyl pa pf K T A fun v => if v ∈ S then B v else K' v := by
  refine Set.ext fun x => and_congr_right fun _ => ⟨fun ⟨h1, h2⟩ => ⟨fun v _ => ?_, fun v hv => ?_⟩,
    fun ⟨h1, h2⟩ => ⟨fun v hv => ?_, fun v hv => ?_⟩⟩
  · by_cases hv : v ∈ S
    · simpa [hv] using h1 v hv
    · simpa [hv] using h2 v hv
  · rw [hK v hv]; exact h2 v fun h' => hv (h h')
  · simpa [hv] using h1 v (h hv)
  · by_cases hT : v ∈ T
    · simpa [hv] using h1 v hT
    · rw [← hK v hT]; exact h2 v hT

variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]

def IsCylProd (pa : ∀ w, X → Ya w) (pf : ∀ v, X → Yf v) (K : ∀ v, Set (Yf v)) (μa : ∀ w, Measure (Ya w))
    (μf : ∀ v, Measure (Yf v)) (μ : Measure X) : Prop :=
  (∀ᶠ v in cofinite, μf v (K v) = 1) ∧
  ∀ S : Finset V, (∀ v ∉ S, μf v (K v) = 1) → ∀ (A : ∀ w, Set (Ya w)) (B : ∀ v, Set (Yf v)),
    (∀ w, MeasurableSet (A w)) → (∀ v ∈ S, MeasurableSet (B v)) →
    μ (cyl pa pf K S A B) = (∏ w, μa w (A w)) * ∏ v ∈ S, μf v (B v)

variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ : Measure X}

theorem exists_finset_of_eventually {p : V → Prop} (h : ∀ᶠ v in cofinite, p v) : ∃ S : Finset V, ∀ v ∉ S, p v :=
  ⟨(eventually_cofinite.1 h).toFinset, fun v hv => by simpa using hv⟩

theorem eventually_of_finset {p : V → Prop} (S : Finset V) (h : ∀ v ∉ S, p v) : ∀ᶠ v in cofinite, p v :=
  S.eventually_cofinite_notMem.mono h

theorem isCylProd_of_large (hK' : ∀ v, MeasurableSet (K' v)) (S₀ : Finset V) (h1 : ∀ v ∉ S₀, μf v (K' v) = 1)
    (hK : ∀ v ∉ S₀, K v = K' v)
    (h : ∀ S : Finset V, S₀ ⊆ S → ∀ (A : ∀ w, Set (Ya w)) (B : ∀ v, Set (Yf v)),
      (∀ w, MeasurableSet (A w)) → (∀ v ∈ S, MeasurableSet (B v)) →
      μ (cyl pa pf K S A B) = (∏ w, μa w (A w)) * ∏ v ∈ S, μf v (B v)) : IsCylProd pa pf K' μa μf μ := by
  classical
  refine ⟨eventually_of_finset S₀ h1, fun S hS A B hA hB => ?_⟩
  rw [cyl_eq_of_subset (K := K) (T := S ∪ S₀) Finset.subset_union_left
    (fun v hv => hK v fun h' => hv (Finset.mem_union_right _ h')), h _ Finset.subset_union_right _ _ hA fun v _ => ?_]
  · congr 1
    rw [← Finset.prod_subset Finset.subset_union_left fun v _ hv => by simp only [if_neg hv, hS v hv]]
    exact Finset.prod_congr rfl fun v hv => by simp only [if_pos hv]
  · split_ifs with hv
    exacts [hB v hv, hK' v]

theorem IsCylProd.congr (h : IsCylProd pa pf K μa μf μ) (hK' : ∀ v, MeasurableSet (K' v))
    (hK : ∀ᶠ v in cofinite, K v = K' v) : IsCylProd pa pf K' μa μf μ := by
  obtain ⟨S₀, hS⟩ := exists_finset_of_eventually (h.1.and hK)
  exact isCylProd_of_large hK' S₀ (fun v hv => (hS v hv).2 ▸ (hS v hv).1) (fun v hv => (hS v hv).2)
    fun S hs => h.2 S fun v hv => (hS v fun h' => hv (hs h')).1

theorem IsCylProd.measure_level (h : IsCylProd pa pf K μa μf μ) (hK : ∀ v, MeasurableSet (K v))
    {A : ∀ w, Set (Ya w)} (hA : ∀ w, MeasurableSet (A w)) :
    μ {x | (∀ w, pa w x ∈ A w) ∧ ∀ v, pf v x ∈ K v} = (∏ w, μa w (A w)) * ∏ᶠ v, μf v (K v) := by
  obtain ⟨S, hS⟩ := exists_finset_of_eventually h.1
  rw [← cyl_self S, h.2 S hS A K hA fun v _ => hK v, finprod_eq_prod_of_mulSupport_subset _ (s := S)]
  exact fun v hv => by_contra fun h' => hv (hS v h')

theorem IsCylProd.smul (h : IsCylProd pa pf K μa μf μ) (hK : ∀ v, MeasurableSet (K v)) (c : W → ℝ≥0∞)
    (d : V → ℝ≥0∞) (T : Finset V) (hd : ∀ v ∉ T, d v = 1) :
    IsCylProd pa pf K (fun w => c w • μa w) (fun v => d v • μf v) (((∏ w, c w) * ∏ v ∈ T, d v) • μ) := by
  classical
  obtain ⟨S₀, hS⟩ := exists_finset_of_eventually h.1
  refine isCylProd_of_large hK (S₀ ∪ T) (fun v hv => ?_) (fun _ _ => rfl) fun S hs A B hA hB => ?_
  · rw [Finset.notMem_union] at hv
    rw [hd v hv.2, one_smul, hS v hv.1]
  · rw [Finset.prod_subset (Finset.subset_union_right.trans hs) fun v _ hv => hd v hv]
    simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
    rw [h.2 S (fun v hv => hS v fun h' => hv (hs (Finset.mem_union_left _ h'))) A B hA hB, mul_mul_mul_comm]

theorem IsCylProd.map {X' : Type} [MeasurableSpace X'] (h : IsCylProd pa pf K μa μf μ) (e : X ≃ᵐ X')
    {pa' : ∀ w, X' → Ya w} {pf' : ∀ v, X' → Yf v} (ha : ∀ w x, pa' w (e x) = pa w x)
    (hf : ∀ v x, pf' v (e x) = pf v x) : IsCylProd pa' pf' K μa μf (μ.map e) :=
  ⟨h.1, fun S hS A B hA hB => by
    rw [e.map_apply, ← h.2 S hS A B hA hB]
    congr 1
    ext x
    simp only [mem_preimage, mem_cyl, ha, hf]⟩

end Cyl

section Group

variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Group X] [∀ w, Group (Ya w)] [∀ v, Group (Yf v)]
  [TopologicalSpace X] [∀ w, TopologicalSpace (Ya w)] [∀ v, TopologicalSpace (Yf v)]

structure IsRestrGroup (pa : ∀ w, X →* Ya w) (pf : ∀ v, X →* Yf v) (K : ∀ v, Subgroup (Yf v)) : Prop where
  continuous_pa : ∀ w, Continuous (pa w)
  continuous_pf : ∀ v, Continuous (pf v)
  isOpen_K : ∀ v, IsOpen (K v : Set (Yf v))
  isCompact_K : ∀ v, IsCompact (K v : Set (Yf v))
  ext : ∀ x y, (∀ w, pa w x = pa w y) → (∀ v, pf v x = pf v y) → x = y
  eventually_mem : ∀ x, ∀ᶠ v in cofinite, pf v x ∈ K v
  exists_eq : ∀ (a : ∀ w, Ya w) (y : ∀ v, Yf v), (∀ᶠ v in cofinite, y v ∈ K v) →
    ∃ x, (∀ w, pa w x = a w) ∧ ∀ v, pf v x = y v
  isOpen_level : IsOpen {x | ∀ v, pf v x ∈ K v}
  isCompact_level : ∀ C : ∀ w, Set (Ya w), (∀ w, IsCompact (C w)) →
    IsCompact {x | (∀ w, pa w x ∈ C w) ∧ ∀ v, pf v x ∈ K v}

def noArch (X : Type) [Group X] : ∀ _ : Empty, X →* PUnit := fun _ => 1

variable {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K K' : ∀ v, Subgroup (Yf v)}

omit [∀ v, TopologicalSpace (Yf v)] in

theorem exists_extend_one {V' : Type} {j : V' → V} (hj : Function.Injective j) (y : ∀ v', Yf (j v')) :
    ∃ z : ∀ v, Yf v, (∀ v', z (j v') = y v') ∧ ∀ v ∉ range j, z v = 1 := by
  have : ∀ v, ∃ z : Yf v, (∀ v' (e : j v' = v), z = e ▸ y v') ∧ (v ∉ range j → z = 1) := fun v => by
    by_cases hv : v ∈ range j
    · obtain ⟨u, rfl⟩ := hv
      exact ⟨y u, fun v' e => by obtain rfl := hj e; rfl, fun h => absurd ⟨u, rfl⟩ h⟩
    · exact ⟨1, fun v' e => absurd ⟨v', e⟩ hv, fun _ => rfl⟩
  choose z h1 h2 using this
  exact ⟨z, fun v' => h1 _ v' rfl, h2⟩

theorem IsRestrGroup.subgroup [∀ w, T1Space (Ya w)] [∀ v, T1Space (Yf v)] (h : IsRestrGroup pa pf K)
    {W' V' : Type} {i : W' → W} {j : V' → V} (hi : Function.Injective i) (hj : Function.Injective j)
    (H : Subgroup X) (hH : ∀ x, x ∈ H ↔ (∀ w ∉ range i, pa w x = 1) ∧ ∀ v ∉ range j, pf v x = 1) :
    IsRestrGroup (fun w => (pa (i w)).comp H.subtype) (fun v => (pf (j v)).comp H.subtype) fun v => K (j v) := by
  have hl : ∀ x : H, (∀ v, pf (j v) x ∈ K (j v)) ↔ ∀ v, pf v x ∈ K v := fun x => ⟨fun hx v => by
    by_cases hv : v ∈ range j
    · obtain ⟨u, rfl⟩ := hv; exact hx u
    · rw [((hH x).1 x.2).2 v hv]; exact one_mem _, fun hx v => hx _⟩
  refine ⟨fun w => (h.continuous_pa _).comp continuous_subtype_val,
    fun v => (h.continuous_pf _).comp continuous_subtype_val, fun v => h.isOpen_K _, fun v => h.isCompact_K _,
    fun x y ha hf => Subtype.ext (h.ext _ _ (fun w => ?_) fun v => ?_),
    fun x => hj.tendsto_cofinite.eventually (h.eventually_mem x), fun a y hy => ?_, ?_, fun C hC => ?_⟩
  · by_cases hw : w ∈ range i
    · obtain ⟨u, rfl⟩ := hw; exact ha u
    · rw [((hH x).1 x.2).1 w hw, ((hH y).1 y.2).1 w hw]
  · by_cases hv : v ∈ range j
    · obtain ⟨u, rfl⟩ := hv; exact hf u
    · rw [((hH x).1 x.2).2 v hv, ((hH y).1 y.2).2 v hv]
  · obtain ⟨a', ha1, ha2⟩ := exists_extend_one hi a
    obtain ⟨y', hy1, hy2⟩ := exists_extend_one hj y
    obtain ⟨x, hx1, hx2⟩ := h.exists_eq a' y' (((eventually_cofinite.1 hy).image j).subset fun v hv => by
      by_cases hr : v ∈ range j
      · obtain ⟨u, rfl⟩ := hr
        exact ⟨u, fun hu => hv (show y' (j u) ∈ K (j u) by rw [hy1]; exact hu), rfl⟩
      · exact absurd (show y' v ∈ K v by rw [hy2 v hr]; exact one_mem _) hv)
    exact ⟨⟨x, (hH x).2 ⟨fun w hw => (hx1 w).trans (ha2 w hw), fun v hv => (hx2 v).trans (hy2 v hv)⟩⟩,
      fun w => (hx1 _).trans (ha1 w), fun v => (hx2 _).trans (hy1 v)⟩
  · convert h.isOpen_level.preimage (continuous_subtype_val (p := (· ∈ H))) using 1
    exact Set.ext hl
  · have hc : IsClosed (H : Set X) := by
      have : (H : Set X) = (⋂ w ∉ range i, pa w ⁻¹' {1}) ∩ ⋂ v ∉ range j, pf v ⁻¹' {1} :=
        Set.ext fun x => by simpa using hH x
      rw [this]
      exact (isClosed_biInter fun w _ => isClosed_singleton.preimage (h.continuous_pa w)).inter
        (isClosed_biInter fun v _ => isClosed_singleton.preimage (h.continuous_pf v))
    have : ∀ w, ∃ D : Set (Ya w), IsCompact D ∧ (∀ u (e : i u = w), D = e ▸ C u) ∧ (w ∉ range i → D = {1}) :=
      fun w => by
        by_cases hw : w ∈ range i
        · obtain ⟨u, rfl⟩ := hw
          exact ⟨C u, hC u, fun v' e => by obtain rfl := hi e; rfl, fun h => absurd ⟨u, rfl⟩ h⟩
        · exact ⟨{1}, isCompact_singleton, fun v' e => absurd ⟨v', e⟩ hw, fun _ => rfl⟩
    choose D hD h1 h2 using this
    refine (congrArg IsCompact (Set.ext fun x => ?_)).mpr
      (hc.isClosedEmbedding_subtypeVal.isCompact_preimage (h.isCompact_level D hD))
    refine and_congr (Iff.intro (fun hx w => ?_) (fun hx u => ?_) :
      (∀ u, pa (i u) x ∈ C u) ↔ ∀ w, pa w x ∈ D w) (hl x)
    · by_cases hw : w ∈ range i
      · obtain ⟨u, rfl⟩ := hw
        rw [h1 _ u rfl]; exact hx u
      · rw [h2 w hw]; exact ((hH x).1 x.2).1 w hw
    · have := hx (i u)
      rwa [h1 _ u rfl] at this

theorem IsRestrGroup.noArch [IsEmpty W] (h : IsRestrGroup pa pf K) : IsRestrGroup (noArch X) pf K :=
  ⟨fun w => w.elim, h.continuous_pf, h.isOpen_K, h.isCompact_K, fun x y _ hf => h.ext x y isEmptyElim hf,
    h.eventually_mem, fun _ y hy => (h.exists_eq isEmptyElim y hy).imp fun _ hx => ⟨fun w => w.elim, hx.2⟩,
    h.isOpen_level, fun _ _ => by simpa using h.isCompact_level isEmptyElim isEmptyElim⟩

def levelAway (pf : ∀ v, X →* Yf v) (K : ∀ v, Subgroup (Yf v)) (S : Finset V) : Subgroup X :=
  ⨅ v, ⨅ (_ : v ∉ S), (K v).comap (pf v)

omit [TopologicalSpace X] [∀ v, TopologicalSpace (Yf v)] in
theorem mem_levelAway {S : Finset V} {x : X} : x ∈ levelAway pf K S ↔ ∀ v ∉ S, pf v x ∈ K v := by
  simp [levelAway, Subgroup.mem_iInf]

theorem IsRestrGroup.isOpen_levelAway [IsTopologicalGroup X] (h : IsRestrGroup pa pf K) (S : Finset V) :
    IsOpen (levelAway pf K S : Set X) := by
  refine Subgroup.isOpen_mono (H₁ := levelAway pf K ∅) (fun x hx => ?_) ?_
  · exact mem_levelAway.2 fun v _ => mem_levelAway.1 hx v (by simp)
  · convert h.isOpen_level using 1
    ext x
    simp [mem_levelAway]

variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]

def IsHaarProd (pa : ∀ w, X →* Ya w) (pf : ∀ v, X →* Yf v) (K : ∀ v, Subgroup (Yf v)) (μa : ∀ w, Measure (Ya w))
    (μf : ∀ v, Measure (Yf v)) (μ : Measure X) : Prop :=
  (∀ w, (μa w).IsHaarMeasure) ∧ (∀ v, (μf v).IsHaarMeasure) ∧ μ.IsHaarMeasure ∧
    IsCylProd (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) μa μf μ

def IsHaarProdFin (pf : ∀ v, X →* Yf v) (K : ∀ v, Subgroup (Yf v)) (μf : ∀ v, Measure (Yf v)) (μ : Measure X) :
    Prop := IsHaarProd (noArch X) pf K (fun w => w.elim) μf μ

variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ μ' : Measure X}

theorem isHaarProdFin_iff : IsHaarProdFin pf K μf μ ↔ (∀ v, (μf v).IsHaarMeasure) ∧ μ.IsHaarMeasure ∧
    (∀ᶠ v in cofinite, μf v (K v) = 1) ∧
    ∀ S : Finset V, (∀ v ∉ S, μf v (K v) = 1) → ∀ B : ∀ v, Set (Yf v), (∀ v ∈ S, MeasurableSet (B v)) →
      μ {x | (∀ v ∈ S, pf v x ∈ B v) ∧ ∀ v ∉ S, pf v x ∈ K v} = ∏ v ∈ S, μf v (B v) := by
  simp [IsHaarProdFin, IsHaarProd, IsCylProd, cyl]

variable [BorelSpace X] [∀ w, BorelSpace (Ya w)] [∀ v, BorelSpace (Yf v)] [IsTopologicalGroup X]

theorem IsRestrGroup.measurableSet_cyl (h : IsRestrGroup pa pf K) {S : Finset V} {A : ∀ w, Set (Ya w)}
    {B : ∀ v, Set (Yf v)} (hA : ∀ w, MeasurableSet (A w)) (hB : ∀ v ∈ S, MeasurableSet (B v)) :
    MeasurableSet (cyl (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) S A B) := by
  have : cyl (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) S A B =
      (⋂ w, pa w ⁻¹' A w) ∩ ((⋂ v ∈ S, pf v ⁻¹' B v) ∩ levelAway pf K S) := by
    ext x
    simp [mem_cyl, mem_levelAway]
  rw [this]
  exact (MeasurableSet.iInter fun w => (h.continuous_pa w).measurable (hA w)).inter
    ((S.measurableSet_biInter fun v hv => (h.continuous_pf v).measurable (hB v hv)).inter
      (h.isOpen_levelAway S).measurableSet)

omit [BorelSpace X] [∀ w, BorelSpace (Ya w)] [IsTopologicalGroup X] in

theorem IsHaarProd.smul (h : IsHaarProd pa pf K μa μf μ) (hK : ∀ v, IsOpen (K v : Set (Yf v))) (c : W → ℝ≥0)
    (d : V → ℝ≥0) (hc : ∀ w, c w ≠ 0) (hd0 : ∀ v, d v ≠ 0) (T : Finset V) (hd : ∀ v ∉ T, d v = 1) :
    IsHaarProd pa pf K (fun w => c w • μa w) (fun v => d v • μf v) (((∏ w, c w) * ∏ v ∈ T, d v) • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun w => IsHaarMeasure.nnreal_smul _ (hc w), fun v => IsHaarMeasure.nnreal_smul _ (hd0 v),
    IsHaarMeasure.nnreal_smul _ (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => hc w)
      (Finset.prod_ne_zero_iff.2 fun v _ => hd0 v)), ?_⟩
  have := h4.smul (fun v => (hK v).measurableSet) (fun w => c w) (fun v => d v) T fun v hv => by simp [hd v hv]
  simpa only [ENNReal.smul_def, ENNReal.coe_mul, ENNReal.ofNNReal_finsetProd] using this

variable [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, IsTopologicalGroup (Ya w)]
  [∀ w, LocallyCompactSpace (Ya w)] [∀ w, T2Space (Ya w)]

omit [∀ w, IsTopologicalGroup (Ya w)] in

theorem IsHaarProd.unique (hK : ∀ v, IsOpen (K v : Set (Yf v))) (hK' : ∀ v, IsCompact (K v : Set (Yf v)))
    (h : IsHaarProd pa pf K μa μf μ) (h' : IsHaarProd pa pf K μa μf μ') : μ = μ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨-, -, h3', h4'⟩ := h'
  obtain ⟨S, hS⟩ := exists_finset_of_eventually h4.1
  let C : ∀ w, TopologicalSpace.PositiveCompacts (Ya w) := fun w => Classical.arbitrary _
  have e := h4.2 S hS (fun w => C w) _ (fun w => (C w).isCompact.measurableSet) fun v _ => (hK v).measurableSet
  have e' := h4'.2 S hS (fun w => C w) _ (fun w => (C w).isCompact.measurableSet) fun v _ => (hK v).measurableSet
  have h0 : (∏ w, μa w (C w)) * ∏ v ∈ S, μf v (K v) ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => (measure_pos_of_nonempty_interior _ (C w).interior_nonempty).ne')
      (Finset.prod_ne_zero_iff.2 fun v _ => ((hK v).measure_pos _ ⟨1, one_mem _⟩).ne')
  have ht : (∏ w, μa w (C w)) * ∏ v ∈ S, μf v (K v) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.prod_ne_top fun w _ => (C w).isCompact.measure_lt_top.ne)
      (ENNReal.prod_ne_top fun v _ => (hK' v).measure_lt_top.ne)
  have hm := isMulLeftInvariant_eq_smul μ μ'
  rw [hm, Measure.smul_apply, e', ENNReal.smul_def, smul_eq_mul] at e
  have : (haarScalarFactor μ μ' : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj h0 ht).1 (e.trans (one_mul _).symm)
  rw [hm, ENNReal.coe_eq_one.1 this, one_smul]

variable [∀ w, SecondCountableTopology (Ya w)] [∀ v, IsTopologicalGroup (Yf v)] [∀ v, LocallyCompactSpace (Yf v)]
  [∀ v, SecondCountableTopology (Yf v)]

omit [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, T2Space (Ya w)] in

theorem IsRestrGroup.exists_factor (h : IsRestrGroup pa pf K) (μa : ∀ w, Measure (Ya w)) (μf : ∀ v, Measure (Yf v))
    [∀ w, (μa w).IsHaarMeasure] [∀ v, (μf v).IsHaarMeasure] (ν : Measure X) [ν.IsHaarMeasure] (S : Finset V) :
    ∃ c : ℝ≥0∞, ∀ (A : ∀ w, Set (Ya w)) (B : ∀ v, Set (Yf v)), (∀ w, MeasurableSet (A w)) →
      (∀ v ∈ S, MeasurableSet (B v)) →
      ν (cyl (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) S A B) =
        c * ((∏ w, μa w (A w)) * ∏ v ∈ S, μf v (B v)) := by
  classical
  let π : X →* (∀ w, Ya w) × ∀ v : S, Yf v := (MonoidHom.pi pa).prod (MonoidHom.pi fun v : S => pf v)
  have hπ : Measurable π := ((continuous_pi h.continuous_pa).prodMk
    (continuous_pi fun v : S => h.continuous_pf v)).measurable
  let m : Measure ((∀ w, Ya w) × ∀ v : S, Yf v) := (ν.restrict (levelAway pf K S)).map π
  have hm : ∀ s, MeasurableSet s → m s = ν (π ⁻¹' s ∩ levelAway pf K S) := fun s hs => by
    rw [Measure.map_apply hπ hs, Measure.restrict_apply (hπ hs)]
  have hc : ∀ (A : ∀ w, Set (Ya w)) (B : ∀ v, Set (Yf v)), (∀ w, MeasurableSet (A w)) →
      (∀ v ∈ S, MeasurableSet (B v)) → m (univ.pi A ×ˢ univ.pi fun v : S => B v) =
      ν (cyl (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) S A B) := fun A B hA hB => by
    rw [hm _ ((MeasurableSet.univ_pi hA).prod (MeasurableSet.univ_pi fun v => hB v v.2))]
    refine congrArg ν (Set.ext fun t => ?_)
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ_pi, mem_cyl, SetLike.mem_coe, mem_levelAway, and_assoc]
    exact and_congr_right fun _ => and_congr_left fun _ => Subtype.forall
  haveI : m.IsMulLeftInvariant := (forall_measure_preimage_mul_iff m).1 fun y s hs => by
    obtain ⟨z, hz1, hz2⟩ := exists_extend_one (j := fun v : S => v.1) Subtype.val_injective y.2
    have hz3 : ∀ v ∉ S, z v ∈ K v := fun v hv => by rw [hz2 v (by simpa using hv)]; exact one_mem _
    obtain ⟨x, hx1, hx2⟩ := h.exists_eq y.1 z (eventually_of_finset S hz3)
    have hx : π x = y := Prod.ext (funext hx1) (funext fun v => (hx2 v).trans (hz1 v))
    have hxU : x ∈ levelAway pf K S := mem_levelAway.2 fun v hv => hx2 v ▸ hz3 v hv
    rw [hm _ (measurable_const_mul y hs), hm _ hs, ← measure_preimage_mul ν x (π ⁻¹' s ∩ _)]
    refine congrArg ν (Set.ext fun t => ?_)
    simp [hx, Subgroup.mul_mem_cancel_left _ hxU]
  let C : ∀ w, TopologicalSpace.PositiveCompacts (Ya w) := fun w => Classical.arbitrary _
  haveI : IsFiniteMeasureOnCompacts m := ⟨fun s hs => by
    refine measure_lt_top_of_isCompact_of_isMulLeftInvariant
      (univ.pi (fun w => interior (C w)) ×ˢ univ.pi fun v : S => (K v : Set (Yf v)))
      ((isOpen_set_pi finite_univ fun w _ => isOpen_interior).prod (isOpen_set_pi finite_univ fun v _ => h.isOpen_K v))
      ((univ_pi_nonempty_iff.2 fun w => (C w).interior_nonempty).prod
        (univ_pi_nonempty_iff.2 fun v => ⟨1, one_mem _⟩)) ?_ hs
    rw [hc _ (fun v => K v) (fun w => isOpen_interior.measurableSet) fun v _ => (h.isOpen_K v).measurableSet, cyl_self]
    refine ne_top_of_le_ne_top (h.isCompact_level (fun w => C w) fun w => (C w).isCompact).measure_lt_top.ne
      (measure_mono fun x hx => ⟨fun w => interior_subset (hx.1 w), hx.2⟩)⟩
  refine ⟨haarScalarFactor m ((Measure.pi μa).prod (Measure.pi fun v : S => μf v)), fun A B hA hB => ?_⟩
  rw [← hc A B hA hB]
  conv_lhs => rw [isMulLeftInvariant_eq_smul m ((Measure.pi μa).prod (Measure.pi fun v : S => μf v))]
  rw [Measure.smul_apply, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul,
    Finset.prod_coe_sort S fun v => μf v (B v)]

theorem IsRestrGroup.existsUnique_isHaarProd (h : IsRestrGroup pa pf K) (μa : ∀ w, Measure (Ya w))
    (μf : ∀ v, Measure (Yf v)) [ha : ∀ w, (μa w).IsHaarMeasure] [hf : ∀ v, (μf v).IsHaarMeasure]
    (h1 : ∀ᶠ v in cofinite, μf v (K v) = 1) : ∃! μ : Measure X, IsHaarProd pa pf K μa μf μ := by
  refine existsUnique_of_exists_of_unique ?_ fun _ _ => IsHaarProd.unique h.isOpen_K h.isCompact_K
  obtain ⟨S₀, hS⟩ := exists_finset_of_eventually h1
  let ν : Measure X := haar
  let C : ∀ w, TopologicalSpace.PositiveCompacts (Ya w) := fun w => Classical.arbitrary _
  let t := ν {x | (∀ w, pa w x ∈ C w) ∧ ∀ v, pf v x ∈ K v}
  let k := (∏ w, μa w (C w)) * ∏ v ∈ S₀, μf v (K v)
  have k0 : k ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => (measure_pos_of_nonempty_interior _ (C w).interior_nonempty).ne')
      (Finset.prod_ne_zero_iff.2 fun v _ => ((h.isOpen_K v).measure_pos _ ⟨1, one_mem _⟩).ne')
  have kt : k ≠ ∞ := ENNReal.mul_ne_top (ENNReal.prod_ne_top fun w _ => (C w).isCompact.measure_lt_top.ne)
      (ENNReal.prod_ne_top fun v _ => (h.isCompact_K v).measure_lt_top.ne)
  have tt : t ≠ ∞ := (h.isCompact_level (fun w => C w) fun w => (C w).isCompact).measure_lt_top.ne
  have t0 : t ≠ 0 := by
    choose a ha using fun w => (C w).interior_nonempty
    obtain ⟨x, hx1, hx2⟩ := h.exists_eq a 1 (Eventually.of_forall fun v => one_mem _)
    have ho : IsOpen ((⋂ w, pa w ⁻¹' interior (C w)) ∩ {x | ∀ v, pf v x ∈ K v}) :=
      (isOpen_iInter_of_finite fun w => isOpen_interior.preimage (h.continuous_pa w)).inter h.isOpen_level
    refine ne_bot_of_le_ne_bot (ho.measure_pos ν ⟨x, mem_iInter.2 fun w => ?_, fun v => ?_⟩).ne'
      (measure_mono fun y hy => ⟨fun w => interior_subset (mem_iInter.1 hy.1 w), hy.2⟩)
    · rw [mem_preimage, hx1]; exact ha w
    · rw [hx2]; exact one_mem _
  refine ⟨(k / t) • ν, ha, hf, IsHaarMeasure.smul ν (ENNReal.div_ne_zero.2 ⟨k0, tt⟩) (ENNReal.div_ne_top kt t0),
    isCylProd_of_large (fun v => (h.isOpen_K v).measurableSet) S₀ hS (fun _ _ => rfl) fun S hs A B hA hB => ?_⟩
  obtain ⟨c, hc⟩ := h.exists_factor μa μf ν S
  have e := hc (fun w => C w) (fun v => K v) (fun w => (C w).isCompact.measurableSet)
    fun v _ => (h.isOpen_K v).measurableSet
  rw [cyl_self, ← Finset.prod_subset hs fun v _ hv => hS v hv] at e
  have e' : k / t * c = 1 := by
    rw [div_eq_mul_inv, mul_right_comm, mul_comm k, ← show t = c * k from e, ENNReal.mul_inv_cancel t0 tt]
  rw [Measure.smul_apply, hc A B hA hB, smul_eq_mul, ← mul_assoc, e', one_mul]

omit [∀ w, SecondCountableTopology (Ya w)] [∀ v, LocallyCompactSpace (Yf v)] [∀ v, SecondCountableTopology (Yf v)] in

theorem IsHaarProd.isMulRightInvariant (h : IsHaarProd pa pf K μa μf μ) (hX : IsRestrGroup pa pf K)
    [∀ w, (μa w).IsMulRightInvariant] [∀ v, (μf v).IsMulRightInvariant] : μ.IsMulRightInvariant := by
  refine ⟨fun g => IsHaarProd.unique hX.isOpen_K hX.isCompact_K ?_ h⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨S₀, hS⟩ := exists_finset_of_eventually (h4.1.and (hX.eventually_mem g))
  refine ⟨h1, h2, inferInstance, isCylProd_of_large (fun v => (hX.isOpen_K v).measurableSet) S₀
    (fun v hv => (hS v hv).1) (fun _ _ => rfl) fun S hs A B hA hB => ?_⟩
  have e := h4.2 S (fun v hv => (hS v fun h' => hv (hs h')).1) (fun w => (· * pa w g) ⁻¹' A w)
    (fun v => (· * pf v g) ⁻¹' B v) (fun w => measurable_mul_const _ (hA w)) fun v hv => measurable_mul_const _ (hB v hv)
  simp only [measure_preimage_mul_right] at e
  rw [Measure.map_apply (measurable_mul_const g) (hX.measurableSet_cyl hA hB), ← e]
  refine congrArg μ (Set.ext fun x => ?_)
  simp only [mem_preimage, mem_cyl, map_mul]
  exact and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun v hv =>
    (K v).mul_mem_cancel_right (hS v fun h' => hv (hs h')).2

section Split

variable {X' : Type} [Group X'] [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X'] [IsTopologicalGroup X']
  [LocallyCompactSpace X'] [SecondCountableTopology X']

omit [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, IsTopologicalGroup (Ya w)] [∀ w, BorelSpace (Ya w)]
  [∀ w, LocallyCompactSpace (Ya w)] [∀ w, T2Space (Ya w)] [∀ w, SecondCountableTopology (Ya w)] in

theorem IsHaarProd.prod_away {S : Finset V} {pa' : ∀ w, X' →* Ya w} {pf' : ∀ v : {v // v ∉ S}, X' →* Yf v}
    {ν : Measure X'} (h : IsHaarProd pa' pf' (fun v => K v) μa (fun v => μf v) ν) [hf : ∀ v, (μf v).IsHaarMeasure]
    (hK : ∀ v, IsOpen (K v : Set (Yf v))) (e : ((∀ v : S, Yf v) × X') ≃ₜ* X)
    (ea : ∀ w p, pa w (e p) = pa' w p.2) (eS : ∀ (v : S) p, pf v (e p) = p.1 v)
    (ef : ∀ (v : {v // v ∉ S}) p, pf v (e p) = pf' v p.2) :
    IsHaarProd pa pf K μa μf (((Measure.pi fun v : S => μf v).prod ν).map e) := by
  classical
  obtain ⟨h1, -, h3, h4⟩ := h
  obtain ⟨S₀, hS⟩ := exists_finset_of_eventually h4.1
  have hS' : ∀ T : Finset V, S ∪ S₀.map (Function.Embedding.subtype _) ⊆ T →
      ∀ v : {v // v ∉ S}, v.1 ∉ T → μf v (K v) = 1 := fun T hT v hv =>
    hS v fun h' => hv (hT (Finset.mem_union_right _ (Finset.mem_map_of_mem _ h')))
  refine ⟨h1, hf, e.isHaarMeasure_map _, isCylProd_of_large (fun v => (hK v).measurableSet)
    (S ∪ S₀.map (Function.Embedding.subtype _))
    (fun v hv => hS' _ le_rfl ⟨v, fun h' => hv (Finset.mem_union_left _ h')⟩ hv) (fun _ _ => rfl)
    fun T hT A B hA hB => ?_⟩
  have hST : S ⊆ T := Finset.subset_union_left.trans hT
  have e1 := h4.2 (T.subtype _) (fun v hv => hS' T hT v (by simpa using hv)) A (fun v => B v) hA
    fun v hv => hB v (by simpa using hv)
  have e2 : e ⁻¹' cyl (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) T A B =
      (univ.pi fun v : S => B v) ×ˢ cyl (fun w => pa' w) (fun v => pf' v) (fun v => (K v : Set (Yf v)))
        (T.subtype _) A fun v => B v := by
    ext p
    simp only [mem_preimage, mem_cyl, mem_prod, mem_univ_pi, Finset.mem_subtype, ea, ← eS, ← ef]
    refine ⟨fun ⟨a, b, c⟩ => ⟨fun v => b v (hST v.2), a, fun v hv => b v hv, fun v hv => c v hv⟩,
      fun ⟨a, b, c, d⟩ => ⟨b, fun v hv => ?_, fun v hv => d ⟨v, fun h' => hv (hST h')⟩ hv⟩⟩
    by_cases h' : v ∈ S
    exacts [a ⟨v, h'⟩, c ⟨v, h'⟩ hv]
  rw [show ((Measure.pi fun v : S => μf v).prod ν).map e =
      ((Measure.pi fun v : S => μf v).prod ν).map e.toHomeomorph.toMeasurableEquiv from rfl,
    MeasurableEquiv.map_apply]
  erw [e2]
  rw [Measure.prod_prod, e1, Measure.pi_pi, mul_left_comm, Finset.prod_coe_sort S fun v => μf v (B v),
    Finset.prod_subtype_eq_prod_filter fun v => μf v (B v), ← Finset.prod_filter_mul_prod_filter_not T (· ∈ S),
    Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hST]

omit [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, T2Space (Ya w)] [∀ v, IsTopologicalGroup (Yf v)]
  [∀ v, LocallyCompactSpace (Yf v)] [∀ v, SecondCountableTopology (Yf v)] [∀ v, BorelSpace (Yf v)] in

theorem IsHaarProdFin.prod_arch {pf' : ∀ v, X' →* Yf v} {ν : Measure X'} (h : IsHaarProdFin pf' K μf ν)
    [ha : ∀ w, (μa w).IsHaarMeasure] (e : ((∀ w, Ya w) × X') ≃ₜ* X)
    (ea : ∀ w p, pa w (e p) = p.1 w) (ef : ∀ v p, pf v (e p) = pf' v p.2) :
    IsHaarProd pa pf K μa μf (((Measure.pi μa).prod ν).map e) := by
  obtain ⟨h2, h3, h4, h5⟩ := isHaarProdFin_iff.1 h
  refine ⟨ha, h2, e.isHaarMeasure_map _, h4, fun S hS A B hA hB => ?_⟩
  have e2 : e ⁻¹' cyl (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) S A B =
      univ.pi A ×ˢ {x | (∀ v ∈ S, pf' v x ∈ B v) ∧ ∀ v ∉ S, pf' v x ∈ K v} := by
    ext p
    simp [mem_cyl, ea, ef]
  rw [show ((Measure.pi μa).prod ν).map e = ((Measure.pi μa).prod ν).map e.toHomeomorph.toMeasurableEquiv from rfl,
    MeasurableEquiv.map_apply]
  erw [e2]
  rw [Measure.prod_prod, h5 S hS B hB, Measure.pi_pi]

omit [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, IsTopologicalGroup (Ya w)] [∀ w, BorelSpace (Ya w)]
  [∀ w, LocallyCompactSpace (Ya w)] [∀ w, T2Space (Ya w)] [∀ w, SecondCountableTopology (Ya w)]
  [∀ v, IsTopologicalGroup (Yf v)] [∀ v, LocallyCompactSpace (Yf v)] [∀ v, SecondCountableTopology (Yf v)]
  [∀ v, BorelSpace (Yf v)] [LocallyCompactSpace X'] [SecondCountableTopology X'] in

theorem IsHaarProd.map {pa' : ∀ w, X' →* Ya w} {pf' : ∀ v, X' →* Yf v} {ν : Measure X'}
    (h : IsHaarProd pa' pf' K μa μf ν) (e : X' ≃ₜ* X) (ea : ∀ w x, pa w (e x) = pa' w x)
    (ef : ∀ v x, pf v (e x) = pf' v x) : IsHaarProd pa pf K μa μf (ν.map e) :=
  haveI := h.2.2.1
  ⟨h.1, h.2.1, e.isHaarMeasure_map _, h.2.2.2.map e.toHomeomorph.toMeasurableEquiv ea ef⟩

end Split

end Group

def normHaar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) : Measure G :=
  haarMeasure ⟨⟨K, hc⟩, by
    rw [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Compacts.coe_mk, ho.interior_eq]
    exact ⟨1, one_mem _⟩⟩

instance {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) : (normHaar K ho hc).IsHaarMeasure :=
  isHaarMeasure_haarMeasure _

@[simp] theorem normHaar_self {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) :
    normHaar K ho hc K = 1 := haarMeasure_self

example {Y : Type} [MeasurableSpace Y] (ν μ : Measure Y) :
    IsCylProd (W := Unit) (V := Empty) (Ya := fun _ => Y) (Yf := fun _ => Y) (fun _ => id) (fun _ => id)
      (fun _ => univ) (fun _ => ν) (fun _ => ν) μ ↔ μ = ν := by
  refine ⟨fun h => Measure.ext fun s hs => ?_, ?_⟩
  · simpa [cyl] using h.2 ∅ (fun v => v.elim) (fun _ => s) (fun _ => s) (fun _ => hs) fun v => v.elim
  · rintro rfl
    refine ⟨Eventually.of_forall fun v => v.elim, fun S _ A B _ _ => ?_⟩
    simp [cyl, Finset.eq_empty_of_isEmpty S, Unique.forall_iff]

end GlobalTheory.RestrMeas

end
