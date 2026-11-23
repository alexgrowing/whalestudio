import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellBlockShapes.VolRelIndex

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped NNReal ENNReal Pointwise

namespace PositivityTheory.RgUd.CellB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem addHaar_smul_set_eq_distribHaarChar_mul {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A]
    [DistribMulAction kˣ A] [ContinuousConstSMul kˣ A] (μ : Measure A) [μ.IsAddHaarMeasure]
    (z : kˣ) {s : Set A} (hs : IsCompact (closure s)) :
    μ (z • s) = distribHaarChar A z * μ s := by
  have h := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure (DomMulAct.mk z • μ) μ hs
  rw [addHaarScalarFactor_smul_eq_distribHaarChar] at h
  have h2 : (DomMulAct.mk z • μ) s = μ (z • s) := by simp [Measure.domSMul_apply]
  rw [← h2, h, ENNReal.smul_def, smul_eq_mul]

theorem distribHaarChar_pi (ι : Type) [Fintype ι] (z : kˣ) :
    ((distribHaarChar (ι → k) z : ℝ≥0) : ℝ) = nabs k z ^ Fintype.card ι := by
  borelize k
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : k)
  have hK1 : (Measure.addHaar : Measure k) K ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hK0).ne'
  have hK2 : (Measure.addHaar : Measure k) K ≠ ∞ := hK.measure_lt_top.ne
  have e1 : (Measure.addHaar : Measure k) (z • K) =
      distribHaarChar k z * (Measure.addHaar : Measure k) K :=
    addHaar_smul_set_eq_distribHaarChar_mul _ z hK.closure
  have hs : IsCompact (Set.univ.pi (fun _ : ι => K)) := isCompact_univ_pi (fun _ => hK)
  have e2 := addHaar_smul_set_eq_distribHaarChar_mul (Measure.pi (fun _ : ι => (Measure.addHaar : Measure k))) z hs.closure
  rw [Set.smul_set_univ_pi, Measure.pi_pi, Measure.pi_pi] at e2
  simp only [Pi.smul_apply, e1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at e2
  have e3 : ((distribHaarChar k z : ℝ≥0∞)) ^ Fintype.card ι = (distribHaarChar (ι → k) z : ℝ≥0∞) :=
    (ENNReal.mul_left_inj (pow_ne_zero _ hK1) (ENNReal.pow_ne_top hK2)).1 e2
  rw [← ENNReal.coe_pow, ENNReal.coe_inj] at e3
  simp only [nabs, ← e3, NNReal.coe_pow]

private theorem relIndex_map_smul_eq_inv_distribHaarChar {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [LocallyCompactSpace A] [MeasurableSpace A] [BorelSpace A]
    [MeasurableAdd A] [DistribMulAction kˣ A] [ContinuousConstSMul kˣ A] (μ : Measure A)
    [μ.IsAddHaarMeasure] (S : AddSubgroup A) (hc : IsCompact (S : Set A))
    (ho : IsOpen (S : Set A)) (z : kˣ) (hz : ∀ x ∈ S, z • x ∈ S) :
    ((S.map (DistribSMul.toAddMonoidHom A z)).relIndex S : ℝ) =
      ((distribHaarChar A z : ℝ≥0) : ℝ)⁻¹ := by
  set T := S.map (DistribSMul.toAddMonoidHom A z) with hT
  have hTset : (T : Set A) = z • (S : Set A) := by
    rw [hT, AddSubgroup.coe_map]
    rfl
  have hTS : T ≤ S := by
    intro x hx
    rw [← SetLike.mem_coe, hTset] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hz y hy
  have hTo : IsOpen (T : Set A) := by
    rw [hTset]
    exact ho.smul z
  have hne : T.relIndex S ≠ 0 := addRelIndex_ne_zero hTS le_rfl hc hTo (Set.inter_eq_left.2 hTS)
  have hSm : MeasurableSet (S : Set A) := ho.measurableSet
  have hemb : MeasurableEmbedding (S.subtype) := MeasurableEmbedding.subtype_coe hSm
  haveI : (μ.comap S.subtype).IsAddLeftInvariant := Measure.IsAddLeftInvariant.comap μ hemb
  haveI : (T.addSubgroupOf S).FiniteIndex := ⟨hne⟩
  have hHm : MeasurableSet ((T.addSubgroupOf S : AddSubgroup S) : Set S) :=
    measurable_subtype_coe hTo.measurableSet
  have key := AddSubgroup.index_mul_measure (T.addSubgroupOf S) hHm (μ.comap S.subtype)
  rw [hemb.comap_apply, hemb.comap_apply, Set.image_univ, AddSubgroup.coe_addSubgroupOf,
    Set.image_preimage_eq_inter_range] at key
  simp only [AddSubgroup.coe_subtype, Subtype.range_coe_subtype, SetLike.setOf_mem_eq] at key
  rw [Set.inter_eq_left.2 hTS, hTset, addHaar_smul_set_eq_distribHaarChar_mul μ z hc.closure, ← mul_assoc] at key
  have hS0 : μ S ≠ 0 := (ho.measure_pos μ ⟨0, S.zero_mem⟩).ne'
  have hSt : μ S ≠ ∞ := hc.measure_lt_top.ne
  have h1 : ((T.relIndex S : ℝ≥0∞)) * (distribHaarChar A z : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj hS0 hSt).1 (key.trans (one_mul _).symm)
  have h2 : (T.relIndex S : ℝ) * ((distribHaarChar A z : ℝ≥0) : ℝ) = 1 := by
    have := congrArg ENNReal.toReal h1
    simpa using this
  exact eq_inv_of_mul_eq_one_left h2

theorem relIndex_smul (ι : Type) [Fintype ι] (S : AddSubgroup (ι → k)) (hc : IsCompact (S : Set (ι → k)))
    (ho : IsOpen (S : Set (ι → k))) (z : kˣ) (hz : ∀ x ∈ S, z • x ∈ S) :
    ((S.map (DistribSMul.toAddMonoidHom (ι → k) z)).relIndex S : ℝ) = (nabs k z)⁻¹ ^ Fintype.card ι := by
  borelize k
  rw [relIndex_map_smul_eq_inv_distribHaarChar (Measure.pi (fun _ : ι => (Measure.addHaar : Measure k))) S hc ho z hz,
    distribHaarChar_pi, inv_pow]

theorem relIndex_conj {G : Type*} [Group G] (ι : Type) [Fintype ι] (U : Subgroup G)
    (φ : U ≃* Multiplicative (ι → k)) (a : G) (z : kˣ) (haU : ∀ u ∈ U, a * u * a⁻¹ ∈ U)
    (hφ : ∀ (u : G) (hu : u ∈ U),
      Multiplicative.toAdd (φ ⟨a * u * a⁻¹, haU u hu⟩) = z • Multiplicative.toAdd (φ ⟨u, hu⟩))
    (L₀ : Subgroup G) (hL₀ : L₀ ≤ U) (S : AddSubgroup (ι → k))
    (hS : ∀ (u : G) (hu : u ∈ U), u ∈ L₀ ↔ Multiplicative.toAdd (φ ⟨u, hu⟩) ∈ S)
    (hc : IsCompact (S : Set (ι → k))) (ho : IsOpen (S : Set (ι → k))) (hz : ∀ x ∈ S, z • x ∈ S) :
    L₀.map (MulAut.conj a).toMonoidHom ≤ L₀ ∧
      ((L₀.map (MulAut.conj a).toMonoidHom).relIndex L₀ : ℝ) = (nabs k z)⁻¹ ^ Fintype.card ι := by
  set f : Multiplicative (ι → k) →* G := U.subtype.comp φ.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp φ.symm.injective
  set m : Multiplicative (ι → k) →* Multiplicative (ι → k) :=
    AddMonoidHom.toMultiplicative (DistribSMul.toAddMonoidHom (ι → k) z) with hmdef
  set T := S.map (DistribSMul.toAddMonoidHom (ι → k) z) with hT
  have hTS : T ≤ S := by
    rintro x ⟨y, hy, rfl⟩
    exact hz y hy
  have hL : L₀ = (AddSubgroup.toSubgroup S).map f := by
    ext g
    constructor
    · intro hg
      have hu := hL₀ hg
      refine ⟨φ ⟨g, hu⟩, (hS g hu).1 hg, ?_⟩
      simp [hfdef]
    · rintro ⟨x, hx, rfl⟩
      have hu : ((φ.symm x : U) : G) ∈ U := (φ.symm x).2
      refine (hS _ hu).2 ?_
      simpa using hx
  have hcf : (MulAut.conj a).toMonoidHom.comp f = f.comp m := by
    refine MonoidHom.ext fun y => ?_
    have h2 : φ ⟨a * (φ.symm y : G) * a⁻¹, haU _ (φ.symm y).2⟩ =
        Multiplicative.ofAdd (z • Multiplicative.toAdd y) := by
      rw [← ofAdd_toAdd (φ _), hφ _ (φ.symm y).2]
      simp
    have h3 := (MulEquiv.symm_apply_eq φ).2 h2.symm
    have h4 : m y = Multiplicative.ofAdd (z • Multiplicative.toAdd y) := rfl
    show a * (φ.symm y : G) * a⁻¹ = ((φ.symm (m y) : U) : G)
    rw [h4, h3]
  have hTm : AddSubgroup.toSubgroup T = (AddSubgroup.toSubgroup S).map m := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨Multiplicative.ofAdd y, hy, by simp [hmdef, hxy]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Multiplicative.toAdd y, hy, by simp [hmdef]⟩
  have hmap : L₀.map (MulAut.conj a).toMonoidHom = (AddSubgroup.toSubgroup T).map f := by
    rw [hL, Subgroup.map_map, hcf, ← Subgroup.map_map, ← hTm]
  refine ⟨?_, ?_⟩
  · rw [hmap, hL]
    exact Subgroup.map_mono (fun x hx => hTS hx)
  · rw [hmap, hL, Subgroup.relIndex_map_map_of_injective _ _ hf, AddSubgroup.relIndex_toSubgroup]
    exact relIndex_smul ι S hc ho z hz

end PositivityTheory.RgUd.CellB
