import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStA

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module MeasureTheory Set
open scoped Classical ComplexOrder

section Crd

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def crd {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) :
    V →ₗ[K] (Fin r → K) :=
  (Basis.span hli).equivFun.toLinearMap ∘ₗ
    (LinearMap.exists_leftInverse_of_injective (Submodule.span K (Set.range v)).subtype
      (Submodule.ker_subtype _)).choose

theorem crd_of_mem {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) {x : V}
    (hx : x ∈ Submodule.span K (Set.range v)) :
    crd hli x = (Basis.span hli).equivFun ⟨x, hx⟩ := by
  unfold crd
  have h := (LinearMap.exists_leftInverse_of_injective (Submodule.span K (Set.range v)).subtype
      (Submodule.ker_subtype _)).choose_spec
  have h2 : (LinearMap.exists_leftInverse_of_injective (Submodule.span K (Set.range v)).subtype
      (Submodule.ker_subtype _)).choose x = ⟨x, hx⟩ := by
    have := congrArg (fun f => f ⟨x, hx⟩) h
    simpa using this
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h2]

theorem sum_crd {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) {x : V}
    (hx : x ∈ Submodule.span K (Set.range v)) : ∑ i, crd hli x i • v i = x := by
  rw [crd_of_mem hli hx]
  have h := (Basis.span hli).sum_equivFun ⟨x, hx⟩
  have h2 := congrArg Subtype.val h
  simp only [Submodule.coe_sum, Submodule.coe_smul, Basis.span_apply] at h2
  exact h2

theorem sum_mem_span {r : ℕ} (v : Fin r → V) (c : Fin r → K) :
    ∑ i, c i • v i ∈ Submodule.span K (Set.range v) := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem crd_sum {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) (c : Fin r → K) :
    crd hli (∑ i, c i • v i) = c := by
  rw [crd_of_mem hli (sum_mem_span v c)]
  have h : (⟨∑ i, c i • v i, sum_mem_span v c⟩ : Submodule.span K (Set.range v)) = ∑ i, c i • (Basis.span hli) i := by
    ext
    simp [Basis.span_apply]
  rw [h, Basis.equivFun_apply, Basis.repr_sum_self]

end Crd

section Lat

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def crdEmb {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) :
    V →+ (Fin r → mixedEmbedding.mixedSpace K) where
  toFun x i := mixedEmbedding K (crd hli x i)
  map_zero' := by ext1 i; simp
  map_add' x y := by ext1 i; simp

theorem crdEmb_apply {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) (x : V) (i : Fin r) :
    crdEmb hli x i = mixedEmbedding K (crd hli x i) := rfl

variable (K) in

noncomputable def latB (r : ℕ) :
    Basis (Σ _ : Fin r, Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (Fin r → mixedEmbedding.mixedSpace K) :=
  Pi.basis fun _ => mixedEmbedding.latticeBasis K

variable (K) in

noncomputable def lat0 (r : ℕ) : Submodule ℤ (Fin r → mixedEmbedding.mixedSpace K) :=
  Submodule.span ℤ (Set.range (latB K r))

theorem heckeAlgebra_mapsTo_localisationLatticeSpan {r : ℕ} {y : Fin r → mixedEmbedding.mixedSpace K} :
    y ∈ lat0 K r ↔ ∀ i, ∃ a : 𝓞 K, mixedEmbedding K (a : K) = y i := by
  rw [lat0, Basis.mem_span_iff_repr_mem ℤ (latB K r)]
  simp only [latB, Pi.basis_repr, Sigma.forall]
  refine forall_congr' fun i => ?_
  rw [← Basis.mem_span_iff_repr_mem ℤ (mixedEmbedding.latticeBasis K),
    mixedEmbedding.mem_span_latticeBasis]
  simp [LinearMap.mem_range]

end Lat

end ReciprocityTheory.GeometryOfNumbersTheory

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module MeasureTheory Set
open scoped Classical ComplexOrder

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

instance instMeasurableAddMixed : MeasurableAdd (mixedEmbedding.mixedSpace K) :=
  MeasurableAdd₂.toMeasurableAdd

instance instHaarPiMixed (r : ℕ) :
    (volume : Measure (Fin r → mixedEmbedding.mixedSpace K)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

instance instBorelPiMixed (r : ℕ) :
    @BorelSpace (Fin r → mixedEmbedding.mixedSpace K) _ MeasureSpace.toMeasurableSpace :=
  Pi.borelSpace

instance (r : ℕ) : DiscreteTopology (lat0 K r) := by unfold lat0; infer_instance

instance (r : ℕ) : IsZLattice ℝ (lat0 K r) := by unfold lat0; infer_instance

theorem sum_ooK_smul {r : ℕ} (v : Fin r → V) (c : Fin r → 𝓞 K) :
    ∑ i, ((c i : K)) • v i = ∑ i, c i • v i := Finset.sum_congr rfl fun i _ => algebraMap_smul K (c i) (v i)

theorem map_span_crdEmb {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.map (crdEmb hli) =
      (lat0 K r).toAddSubgroup := by
  ext y
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, heckeAlgebra_mapsTo_localisationLatticeSpan]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hx
    refine ⟨c i, ?_⟩
    rw [crdEmb_apply, ← sum_ooK_smul, crd_sum]
  · intro h
    choose a ha using h
    refine ⟨∑ i, ((a i : K)) • v i, ?_, ?_⟩
    · rw [sum_ooK_smul]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
    · ext1 i; rw [crdEmb_apply, crd_sum, ha]

noncomputable def latE {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v)
    (E : Submodule (𝓞 K) V) : Submodule ℤ (Fin r → mixedEmbedding.mixedSpace K) :=
  (E.toAddSubgroup.map (crdEmb hli)).toIntSubmodule

theorem crdEmb_injOn {r : ℕ} {v : Fin r → V} (hli : LinearIndependent K v) {x y : V}
    (hx : x ∈ Submodule.span K (Set.range v)) (hy : y ∈ Submodule.span K (Set.range v))
    (h : crdEmb hli x = crdEmb hli y) : x = y := by
  have h1 : crd hli x = crd hli y := by
    funext i
    have h2 := congrFun h i
    simp only [crdEmb_apply] at h2
    exact mixedEmbedding_injective K h2
  rw [← sum_crd hli hx, ← sum_crd hli hy, h1]

theorem span_le_E {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    Submodule.span (𝓞 K) (Set.range v) ≤ E := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv.1 i)

theorem standardLattice_le_frameLattice {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    lat0 K r ≤ latE hv.2.1 E := by
  intro y hy
  have : y ∈ (lat0 K r).toAddSubgroup := hy
  rw [← map_span_crdEmb hv.2.1] at this
  exact AddSubgroup.map_mono (f := crdEmb hv.2.1) (fun x hx => span_le_E hv hx) this

theorem relIndex_lat {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    (lat0 K r).toAddSubgroup.relIndex (latE hv.2.1 E).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup := by
  let P : AddSubgroup V := (Submodule.span K (Set.range v)).toAddSubgroup
  have hEP : E.toAddSubgroup ≤ P := fun x hx => hv.2.2 hx
  have hHP : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup ≤ P :=
    fun x hx => hEP (span_le_E hv hx)
  let f := (crdEmb hv.2.1).comp P.subtype
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (crdEmb_injOn hv.2.1 a.2 b.2 hab)
  have key : ∀ X : AddSubgroup V, X ≤ P → X.map (crdEmb hv.2.1) = (X.addSubgroupOf P).map f := by
    intro X hX
    rw [← AddSubgroup.map_map, AddSubgroup.addSubgroupOf_map_subtype, inf_of_le_left hX]
  rw [← map_span_crdEmb hv.2.1]
  change ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.map (crdEmb hv.2.1)).relIndex
    (E.toAddSubgroup.map (crdEmb hv.2.1)) = _
  rw [key _ hHP, key _ hEP, AddSubgroup.relIndex_map_map_of_injective _ _ hf,
    AddSubgroup.relIndex_addSubgroupOf hEP]

theorem discrete_latE {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ} {v : Fin r → V}
    (hv : IsFrame K E v) : DiscreteTopology (latE hv.2.1 E) := by
  set n := (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup with hn_def
  have hn : n ≠ 0 := hv.relIndex_ne_zero hE
  have hmem : ∀ y ∈ latE hv.2.1 E, n • y ∈ lat0 K r := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h1 : n • x ∈ (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup :=
      AddSubgroup.nsmul_relIndex_mem _ hx
    have : (lat0 K r).toAddSubgroup = _ := (map_span_crdEmb hv.2.1).symm
    change n • crdEmb hv.2.1 x ∈ (lat0 K r).toAddSubgroup
    rw [this, ← map_nsmul]
    exact AddSubgroup.mem_map_of_mem _ h1
  let g : latE hv.2.1 E → lat0 K r := fun y => ⟨n • (y : Fin r → mixedEmbedding.mixedSpace K), hmem y y.2⟩
  refine DiscreteTopology.of_continuous_injective (f := g) ?_ ?_
  · exact Continuous.subtype_mk ((continuous_const_smul n).comp continuous_subtype_val) _
  · intro a b hab
    have h1 : n • (a : Fin r → mixedEmbedding.mixedSpace K) = n • (b : Fin r → mixedEmbedding.mixedSpace K) :=
      congrArg Subtype.val hab
    have h2 : (n : ℝ) • (a : Fin r → mixedEmbedding.mixedSpace K) = (n : ℝ) • (b : Fin r → mixedEmbedding.mixedSpace K) := by
      simpa only [Nat.cast_smul_eq_nsmul] using h1
    exact Subtype.ext (smul_right_injective _ (Nat.cast_ne_zero.mpr hn) h2)

theorem isZLattice_latE {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ} {v : Fin r → V}
    (hv : IsFrame K E v) : haveI := discrete_latE hE hv; IsZLattice ℝ (latE hv.2.1 E) :=
  haveI := discrete_latE hE hv
  ⟨by rw [eq_top_iff, ← IsZLattice.span_top (L := lat0 K r)]; exact Submodule.span_mono (standardLattice_le_frameLattice hv)⟩

theorem covolume_standardLattice (r : ℕ) :
    ZLattice.covolume (lat0 K r) = (ZLattice.covolume (mixedEmbedding.integerLattice K)) ^ r := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain (lat0 K r) volume
      (ZSpan.isAddFundamentalDomain (latB K r) volume),
    ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (mixedEmbedding.fundamentalDomain_integerLattice K)]
  have : ZSpan.fundamentalDomain (latB K r) =
      Set.pi univ fun _ => ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K) := by
    ext y
    simp only [ZSpan.mem_fundamentalDomain, latB, Pi.basis_repr, Sigma.forall, mem_pi, mem_univ,
      true_implies]
  rw [this, measureReal_def, volume_pi_pi, ENNReal.toReal_prod, measureReal_def]
  simp

theorem covolume_latE {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ} {v : Fin r → V}
    (hv : IsFrame K E v) :
    haveI := discrete_latE hE hv; haveI := isZLattice_latE hE hv
    ZLattice.covolume (latE hv.2.1 E) = ZLattice.covolume (lat0 K r) /
      ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup : ℝ) := by
  haveI := discrete_latE hE hv; haveI := isZLattice_latE hE hv
  have h := covol_div_covol_eq_relIndex volume (lat0 K r) (latE hv.2.1 E) (standardLattice_le_frameLattice hv)
  rw [relIndex_lat hv] at h
  have hn : ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (hv.relIndex_ne_zero hE)
  have hpos := ZLattice.covolume_pos (latE hv.2.1 E) volume
  rw [← h, div_div_cancel₀ (ZLattice.covolume_pos _ _).ne']

end ReciprocityTheory.GeometryOfNumbersTheory
