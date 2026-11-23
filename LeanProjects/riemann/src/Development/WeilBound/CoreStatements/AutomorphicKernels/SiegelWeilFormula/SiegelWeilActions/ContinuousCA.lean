import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisensteinNormSumRationalInvariant
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.IsFirstChernFamily
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.AddFDOfCover
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.InclRSmul

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)

scoped instance afSC : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
scoped instance afBorel : BorelSpace (AF F) := ⟨rfl⟩

variable (F) in

def lamA : Measure (AF F) := Measure.addHaar

instance lamA_haar : (lamA F).IsAddHaarMeasure := by unfold lamA; infer_instance

variable (F) in

def fA : AddSubgroup (AF F) := (algebraMap F (AF F)).range.toAddSubgroup

instance countable_fA : Countable (fA F) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have h : ((fA F : AddSubgroup (AF F)) : Set (AF F)).Countable := by
    refine (Set.countable_range (algebraMap F (AF F))).mono fun x hx => ?_
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y, rfl⟩
  exact h.to_subtype

theorem exists_fd_fA : ∃ 𝓐 : Set (AF F), IsAddFundamentalDomain (fA F) 𝓐 (lamA F) ∧ lamA F 𝓐 ≠ 0 ∧ lamA F 𝓐 ≠ ⊤ := by
  haveI : DiscreteTopology (fA F) := by
    obtain ⟨U, hU, hU0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
    obtain ⟨O, hOU, hO, h0⟩ := mem_nhds_iff.1 hU
    refine discreteTopology_of_isOpen_singleton_zero ?_
    convert hO.preimage continuous_subtype_val using 1
    ext ⟨x, hx⟩
    constructor
    · intro h
      have h1 : x = 0 := congrArg Subtype.val (Set.mem_singleton_iff.1 h)
      subst h1
      exact h0
    · intro h
      obtain ⟨y, rfl⟩ := hx
      have hy : y = 0 := hU0 y (hOU h)
      subst hy
      exact Set.mem_singleton_iff.2 (Subtype.ext (map_zero _))
  obtain ⟨K, hK, hKx⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  obtain ⟨𝓐, h𝓐, hc⟩ := ComplexParameterFamilyContinuity.addFD_of_cover' (fA F) hK (fun x => by
    obtain ⟨y, hy⟩ := hKx x
    exact ⟨-algebraMap F (AF F) y, ⟨-y, map_neg _ _⟩, by rwa [neg_add_eq_sub]⟩) (lamA F)
  refine ⟨𝓐, h𝓐, h𝓐.measure_ne_zero (NeZero.ne _), ?_⟩
  exact ne_top_of_le_ne_top hc.measure_lt_top.ne (measure_mono subset_closure)

variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem pEquiv (h : Hyp L nb uM nb' w₁ cM δ) :
    ∃ P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b),
      (∀ β, P β = ((pb L β, pa L δ β), C4.prj L β)) ∧
      ∀ β, β ∈ nF σ d.Y d.b ↔ (pb L β ∈ L.ratV ∧ pa L δ β ∈ fA F) ∧ C4.prj L β ∈ nF σ L.Y L.b := by
  obtain ⟨P, h1, h2⟩ := Meas.pEquiv0 L h.δ0 ⟨cM (0, 1), by
    obtain ⟨A', hA'⟩ := h.cf (0, 1)
    refine ⟨A', ?_⟩
    rw [hA']
    have hu : uA L (0 : Fin L.n → AE F E) = 1 := by simp [uA]
    rw [hu]⟩
  exact ⟨P, h1, h2⟩

theorem continuous_cA : Continuous (cA σ : AE F E → AE F E) :=
  IsModuleTopology.continuous_of_linearMap (R := AF F) (cA σ).toLinearMap

theorem isClosed_nA' {n : ℕ} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} (hb : IsFrame2 σ Y b) :
    IsClosed (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) := by
  obtain ⟨ε, hε⟩ := hb.1
  have h : (nA σ Y b : Set (Matrix (Fin n) (Fin n) (AE F E))) =
      {β | βᵀ = -((((ε : ℤ) : AE F E)) • β.map (cA σ))} := by
    ext β
    exact kunf.mem_nA_iff hε β
  rw [h]
  have hc : Continuous fun β : Matrix (Fin n) (Fin n) (AE F E) => β.map (cA σ) :=
    continuous_id.matrix_map (continuous_cA (σ := σ))
  exact isClosed_eq continuous_id.matrix_transpose (hc.const_smul (((ε : ℤ) : AE F E))).neg

instance lcNA {n : ℕ} {Y : Spc F E n} {b : GL (Fin n ⊕ Fin n) E} [Fact (IsFrame2 σ Y b)] :
    LocallyCompactSpace (nA σ Y b) :=
  (isClosed_nA' (Fact.out : IsFrame2 σ Y b)).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem lam_map {lam : Measure (nA σ d.Y d.b)} [lam.IsAddHaarMeasure] {ν : Measure (Fin L.n → AE F E)} [ν.IsAddHaarMeasure]
    {lam' : Measure (nA σ L.Y L.b)} [lam'.IsAddHaarMeasure] (P : (nA σ d.Y d.b) ≃ₜ+ (((Fin L.n → AE F E) × AF F) × nA σ L.Y L.b)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ lam.map P = c • ((ν.prod (lamA F)).prod lam') := by
  haveI : Fact (IsFrame2 σ L.Y L.b) := ⟨L.ok.frame⟩
  haveI : (lam.map P).IsAddHaarMeasure := P.isAddHaarMeasure_map lam
  haveI : SFinite ν := inferInstance
  haveI : SFinite lam' := inferInstance
  haveI : SFinite (lamA F) := inferInstance
  haveI : (ν.prod (lamA F)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  haveI : SFinite (ν.prod (lamA F)) := inferInstance
  haveI : ((ν.prod (lamA F)).prod lam').IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  refine ⟨(Measure.addHaarScalarFactor (lam.map P) ((ν.prod (lamA F)).prod lam') : ℝ≥0∞),
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ENNReal.coe_ne_top, ?_⟩
  rw [← ENNReal.smul_def]
  exact Measure.isAddLeftInvariant_eq_smul _ _

theorem kap_eq {ν : Measure (Fin L.n → AE F E)} [ν.IsAddHaarMeasure] {κ : Measure ((Fin L.n → AE F E) × AF F)}
    [κ.IsAddHaarMeasure] : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ κ = c • (ν.prod (lamA F)) := by
  haveI : SFinite ν := inferInstance
  haveI : SFinite (lamA F) := inferInstance
  haveI : (ν.prod (lamA F)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  refine ⟨(Measure.addHaarScalarFactor κ (ν.prod (lamA F)) : ℝ≥0∞),
    ENNReal.coe_ne_zero.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', ENNReal.coe_ne_top, ?_⟩
  rw [← ENNReal.smul_def]
  exact Measure.isAddLeftInvariant_eq_smul _ _

end PositivityTheory.SiegelWeilFormula.Act.C5

namespace PositivityTheory.SiegelWeilFormula.Act.C5

theorem shear_mp' {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] [AddGroup Y] [MeasurableAdd₂ Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] [ν.IsAddRightInvariant] (s : X → Y) (hs : Measurable s) :
    MeasurePreserving (fun p : X × Y => (p.1, p.2 + s p.1)) (μ.prod ν) (μ.prod ν) :=
  (MeasurePreserving.id μ).skew_product (g := fun x y => y + s x) (measurable_snd.add (hs.comp measurable_fst))
    (Filter.Eventually.of_forall fun x => map_add_right_eq_self ν (s x))

open scoped Pointwise in

theorem fd_prod {X Y : Type} [AddCommGroup X] [AddCommGroup Y] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableAdd X] [MeasurableAdd Y] {Γ : AddSubgroup X} {Δ : AddSubgroup Y} [Countable Γ] [Countable Δ]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν] [μ.IsAddRightInvariant] [ν.IsAddRightInvariant] {s : Set X} {t : Set Y}
    (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) := by
  have key : ∀ (g : Γ.prod Δ) (p : X × Y), p ∈ g +ᵥ (s ×ˢ t) ↔ (-(g : X × Y).1 + p.1 ∈ s ∧ -(g : X × Y).2 + p.2 ∈ t) :=
    fun g p => by rw [Set.mem_vadd_set_iff_neg_vadd_mem]; rfl
  refine ⟨hs.nullMeasurableSet.prod ht.nullMeasurableSet, ?_, ?_⟩
  · have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp1 hp2
    obtain ⟨a, ha⟩ := hp1
    obtain ⟨b, hb⟩ := hp2
    exact ⟨⟨((a : X), (b : Y)), AddSubgroup.mem_prod.2 ⟨a.2, b.2⟩⟩, ha, hb⟩
  · intro g g' hne
    have m1 : ∀ g : Γ.prod Δ, (g : X × Y).1 ∈ Γ := fun g => (AddSubgroup.mem_prod.1 g.2).1
    have m2 : ∀ g : Γ.prod Δ, (g : X × Y).2 ∈ Δ := fun g => (AddSubgroup.mem_prod.1 g.2).2
    by_cases h1 : (g : X × Y).1 = (g' : X × Y).1
    · have h2 : (g : X × Y).2 ≠ (g' : X × Y).2 := fun h2 => hne (Subtype.ext (Prod.ext h1 h2))
      have hd : AEDisjoint ν ((⟨_, m2 g⟩ : Δ) +ᵥ t) ((⟨_, m2 g'⟩ : Δ) +ᵥ t) :=
        ht.aedisjoint fun h => h2 (congrArg Subtype.val h)
      refine measure_mono_null (t := Set.univ ×ˢ (((⟨_, m2 g⟩ : Δ) +ᵥ t) ∩ ((⟨_, m2 g'⟩ : Δ) +ᵥ t))) ?_ ?_
      · rintro p ⟨hp, hp'⟩
        rw [key] at hp hp'
        exact ⟨trivial, Set.mem_vadd_set_iff_neg_vadd_mem.2 hp.2, Set.mem_vadd_set_iff_neg_vadd_mem.2 hp'.2⟩
      · rw [Measure.prod_prod, show ν _ = 0 from hd, mul_zero]
    · have hd : AEDisjoint μ ((⟨_, m1 g⟩ : Γ) +ᵥ s) ((⟨_, m1 g'⟩ : Γ) +ᵥ s) :=
        hs.aedisjoint fun h => h1 (congrArg Subtype.val h)
      refine measure_mono_null (t := (((⟨_, m1 g⟩ : Γ) +ᵥ s) ∩ ((⟨_, m1 g'⟩ : Γ) +ᵥ s)) ×ˢ Set.univ) ?_ ?_
      · rintro p ⟨hp, hp'⟩
        rw [key] at hp hp'
        exact ⟨⟨Set.mem_vadd_set_iff_neg_vadd_mem.2 hp.1, Set.mem_vadd_set_iff_neg_vadd_mem.2 hp'.1⟩, trivial⟩
      · rw [Measure.prod_prod, show μ _ = 0 from hd, zero_mul]

end PositivityTheory.SiegelWeilFormula.Act.C5

end
