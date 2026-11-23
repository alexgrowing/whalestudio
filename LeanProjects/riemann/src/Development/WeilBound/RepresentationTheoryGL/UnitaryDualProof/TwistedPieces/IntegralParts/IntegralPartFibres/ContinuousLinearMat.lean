import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.Zpart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzLocallyConstantSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.LocallyCompactAEf

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil MeasureTheory Filter Topology
open scoped Pointwise ENNReal NNReal

namespace PositivityTheory.RgUd.TP.Nil.Fib1

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def mEqv (n : ℕ) : (Fin n × Fin n → k) ≃ₗ[k] Matrix (Fin n) (Fin n) k where
  toFun y := Matrix.of fun i j => y (i, j)
  invFun x p := x p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem continuous_linear_mat {M : Type} [AddCommGroup M] [Module k M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousSMul k M] (f : Matrix (Fin n) (Fin n) k →ₗ[k] M) : Continuous f := by
  have h1 : Continuous (f ∘ₗ (mEqv (k := k) n).toLinearMap) := LinearMap.continuous_on_pi _
  have h2 : Continuous (fun x : Matrix (Fin n) (Fin n) k => (mEqv (k := k) n).symm x) :=
    continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  have h3 := h1.comp h2
  convert h3 using 1
  ext x
  simp

theorem val_lt_one_of_nabs {t : kˣ} (ht : nabs k t < 1) : ValuativeRel.valuation k (t : k) < 1 := by
  have h1 : nabs k t < nabs k 1 := by rwa [nabs_one]
  have h2 : ¬ (ValuativeRel.valuation k ((1 : kˣ) : k) ≤ ValuativeRel.valuation k (t : k)) := by
    rw [← nabs_le_iff]
    exact not_le.mpr h1
  simpa using not_le.mp h2

private theorem mem_smul_addSubgroup_iff' (c : k) (L : AddSubgroup (Matrix (Fin n) (Fin n) k)) (x : Matrix (Fin n) (Fin n) k) :
    x ∈ c • L ↔ ∃ y ∈ L, c • y = x := Iff.rfl

theorem isLat_smul {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {L : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) (t : kˣ) : IsLat Z ((t : k) • L) := by
  have ht : (t : k) ≠ 0 := t.ne_zero
  obtain ⟨U, hUo, hU0, hUL⟩ := hL.nhd
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (mem_smul_addSubgroup_iff' _ _ _).mp hx
    exact Z.smul_mem (hL.sub hy) _
  · have h : (((t : k) • L : AddSubgroup _) : Set (Matrix (Fin n) (Fin n) k)) = (fun y => (t : k) • y) '' (L : Set _) := by
      ext x
      exact mem_smul_addSubgroup_iff' _ _ _
    rw [h]
    exact hL.cpt.image (continuous_const_smul _)
  · refine ⟨(t : k) • U, hUo.smul₀ ht, ⟨0, hU0, smul_zero _⟩, ?_⟩
    rintro x ⟨⟨u, hu, rfl⟩, hx⟩
    have huZ : u ∈ Z := by
      have h1 := Z.smul_mem hx (t : k)⁻¹
      rwa [inv_smul_smul₀ ht] at h1
    exact (mem_smul_addSubgroup_iff' _ _ _).mpr ⟨u, hUL ⟨hu, huZ⟩, rfl⟩
  · intro a ha x hx
    obtain ⟨y, hy, rfl⟩ := (mem_smul_addSubgroup_iff' _ _ _).mp hx
    exact (mem_smul_addSubgroup_iff' _ _ _).mpr ⟨a • y, hL.int a ha y hy, smul_comm _ _ _⟩

private theorem exists_pow_smul_mem_nhds_of_isCompact {t : kˣ} (ht : nabs k t < 1) {K : Set (Matrix (Fin n) (Fin n) k)}
    (hK : IsCompact K) {W : Set (Matrix (Fin n) (Fin n) k)} (hW : W ∈ 𝓝 0) :
    ∃ j : ℕ, ∀ x ∈ K, ((t : k) ^ j) • x ∈ W := by
  have hv := val_lt_one_of_nabs ht
  have htend : Tendsto (fun j : ℕ => (t : k) ^ j) atTop (𝓝 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
    intro γ _
    obtain ⟨m, hm⟩ := exists_pow_lt₀ hv γ
    filter_upwards [eventually_ge_atTop m] with j hj
    simp only [Set.mem_setOf_eq, map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hv.le hj) hm
  have hev : ∀ᶠ s in 𝓝 (0 : k), ∀ x ∈ K, s • x ∈ W := by
    apply hK.eventually_forall_of_forall_eventually
    intro y _
    have hc : Tendsto (fun z : k × Matrix (Fin n) (Fin n) k => z.1 • z.2) (𝓝 (0, y)) (𝓝 0) := by
      have h1 := (continuous_smul (M := k) (X := Matrix (Fin n) (Fin n) k)).tendsto (0, y)
      simpa using h1
    exact hc hW
  exact (htend.eventually hev).exists

theorem lat_small {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {L : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) {t : kˣ} (ht : nabs k t < 1) {W : Set (Matrix (Fin n) (Fin n) k)} (hW : W ∈ nhds 0) :
    ∃ j : ℕ, ((t ^ j : kˣ) : k) • (L : Set (Matrix (Fin n) (Fin n) k)) ⊆ W := by
  obtain ⟨j, hj⟩ := exists_pow_smul_mem_nhds_of_isCompact ht hL.cpt hW
  refine ⟨j, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  simp only [Units.val_pow_eq_pow_val]
  exact hj x hx

theorem lat_index_pos {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {L M : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) (hM : IsLat Z M) (hML : M ≤ L) : M.relIndex L ≠ 0 := by
  obtain ⟨U, hUo, hU0, hUZ⟩ := hM.nhd
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL.cpt
  have hnhds : (M.addSubgroupOf L : Set L) ∈ 𝓝 (0 : L) := by
    have hpre : IsOpen ((Subtype.val : L → Matrix (Fin n) (Fin n) k) ⁻¹' U) :=
      hUo.preimage continuous_subtype_val
    refine Filter.mem_of_superset (hpre.mem_nhds (by simpa using hU0)) ?_
    intro y hy
    rw [SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf]
    exact hUZ ⟨hy, hL.sub y.2⟩
  have hopen : IsOpen (M.addSubgroupOf L : Set L) := AddSubgroup.isOpen_of_mem_nhds _ hnhds
  haveI : Finite (L ⧸ M.addSubgroupOf L) := AddSubgroup.quotient_finite_of_isOpen _ hopen
  show (M.addSubgroupOf L).index ≠ 0
  exact AddSubgroup.index_ne_zero_of_finite

section Coord

variable (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))

def bZ : Module.Basis (Fin (Module.finrank k Z)) k Z := Module.finBasis k Z

def eZ : (Fin (Module.finrank k Z) → k) →ₗ[k] Matrix (Fin n) (Fin n) k :=
  Z.val.toLinearMap ∘ₗ (bZ Z).equivFun.symm.toLinearMap

theorem eZ_mem (a : Fin (Module.finrank k Z) → k) : eZ Z a ∈ Z := ((bZ Z).equivFun.symm a).2

theorem eZ_injective : Function.Injective (eZ Z) := by
  intro a b h
  exact (bZ Z).equivFun.symm.injective (Subtype.val_injective h)

theorem eZ_surj {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Z) : eZ Z ((bZ Z).equivFun ⟨x, hx⟩) = x := by
  simp [eZ]

theorem continuous_eZ : Continuous (eZ Z) := LinearMap.continuous_on_pi _

theorem exists_PZ : ∃ P : Matrix (Fin n) (Fin n) k →ₗ[k] (Fin (Module.finrank k Z) → k), P ∘ₗ eZ Z = LinearMap.id :=
  (eZ Z).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 (eZ_injective Z))

end Coord

def intV (d : ℕ) : AddSubgroup (Fin d → k) where
  carrier := {a | ∀ i, ValuativeRel.valuation k (a i) ≤ 1}
  add_mem' ha hb i := by
    simp only [Set.mem_ofPred_eq, Pi.add_apply] at *
    exact (Valuation.map_add _ _ _).trans (max_le (ha i) (hb i))
  zero_mem' i := by simp
  neg_mem' ha i := by
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, Valuation.map_neg] at *
    exact ha i

theorem isCompact_intV (d : ℕ) : IsCompact ((intV (k := k) d) : Set (Fin d → k)) := by
  have : ((intV (k := k) d) : Set (Fin d → k)) = Set.univ.pi fun _ => {x : k | ValuativeRel.valuation k x ≤ 1} := by
    ext a; simp [intV]
  rw [this]
  exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1

theorem isOpen_intV (d : ℕ) : IsOpen ((intV (k := k) d) : Set (Fin d → k)) := by
  apply AddSubgroup.isOpen_of_mem_nhds
  have h0 : {x : k | ValuativeRel.valuation k x < ((1 : (ValuativeRel.ValueGroupWithZero k)ˣ) : ValuativeRel.ValueGroupWithZero k)} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero k).mem_of_mem trivial
  have h1 : (Set.univ.pi fun _ : Fin d => {x : k | ValuativeRel.valuation k x < ((1 : (ValuativeRel.ValueGroupWithZero k)ˣ) : ValuativeRel.ValueGroupWithZero k)}) ∈ 𝓝 (0 : Fin d → k) :=
    set_pi_mem_nhds Set.finite_univ fun i _ => h0
  refine Filter.mem_of_superset h1 ?_
  intro a ha i
  have h2 := ha i (Set.mem_univ i)
  simp only [Set.mem_setOf_eq, Units.val_one] at h2
  exact h2.le

theorem exists_lat (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : ∃ L, IsLat Z L := by
  obtain ⟨P, hP⟩ := exists_PZ Z
  have hPe : ∀ a, P (eZ Z a) = a := fun a => LinearMap.congr_fun hP a
  refine ⟨(intV (k := k) (Module.finrank k Z)).map (eZ Z).toAddMonoidHom, ⟨?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨a, -, rfl⟩
    exact eZ_mem Z a
  · rw [AddSubgroup.coe_map]
    exact (isCompact_intV (k := k) _).image (continuous_eZ Z)
  · refine ⟨P ⁻¹' (intV (k := k) (Module.finrank k Z) : Set (Fin (Module.finrank k Z) → k)),
      (isOpen_intV (k := k) _).preimage (continuous_linear_mat P), ?_, ?_⟩
    · simp only [Set.mem_preimage, map_zero]; exact (intV _).zero_mem
    · rintro y ⟨hyU, hyZ⟩
      refine ⟨(bZ Z).equivFun ⟨y, hyZ⟩, ?_, eZ_surj Z hyZ⟩
      have := hyU
      simp only [Set.mem_preimage] at this
      rwa [← eZ_surj Z hyZ, hPe] at this
  · rintro a ha _ ⟨x, hx, rfl⟩
    refine ⟨a • x, fun i => ?_, (eZ Z).map_smul a x⟩
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_one' ha (hx i)

section Index

theorem smul_pi_set {d : ℕ} (g : kˣ) (S : Set k) :
    g • (Set.univ.pi fun _ : Fin d => S) = Set.univ.pi fun _ => g • S := by
  rw [Set.smul_set_pi]
  rfl

theorem distribHaarChar_pi [MeasurableSpace k] [BorelSpace k] (d : ℕ) (g : kˣ) :
    distribHaarChar (Fin d → k) g = distribHaarChar k g ^ d := by
  obtain ⟨S, hSc, hSn⟩ := exists_compact_mem_nhds (0 : k)
  let μk : Measure k := Measure.addHaar
  have h0 : μk S ≠ 0 := (Measure.measure_pos_of_mem_nhds (μ := μk) hSn).ne'
  have hfin : μk S ≠ ∞ := hSc.measure_lt_top.ne
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.pi fun _ : Fin d => μk)
    (s := Set.univ.pi fun _ => S)
  · rw [Measure.pi_pi]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => h0
  · rw [Measure.pi_pi]
    exact ENNReal.prod_ne_top fun _ _ => hfin
  · rw [smul_pi_set, Measure.pi_pi, Measure.pi_pi]
    simp only [← distribHaarChar_mul μk g S]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    rfl

private theorem measure_eq_relIndex_mul_of_le {G : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : Measure G) [μ.IsAddLeftInvariant] {H K : AddSubgroup G} (hHK : H ≤ K)
    (hH : MeasurableSet (H : Set G)) (hK : MeasurableSet (K : Set G)) (hi : H.relIndex K ≠ 0) :
    μ K = H.relIndex K * μ H := by
  haveI : (H.addSubgroupOf K).FiniteIndex := ⟨hi⟩
  have he : MeasurableEmbedding (Subtype.val : K → G) := MeasurableEmbedding.subtype_coe hK
  haveI : MeasurableAdd K :=
    ⟨fun c => ((measurable_const_add (c : G)).comp measurable_subtype_coe).subtype_mk,
      fun c => ((measurable_add_const (c : G)).comp measurable_subtype_coe).subtype_mk⟩
  haveI : (μ.comap (Subtype.val : K → G)).IsAddLeftInvariant := by
    constructor
    intro g
    ext A hA
    rw [Measure.map_apply (measurable_const_add g) hA, he.comap_apply, he.comap_apply]
    have hs : Subtype.val '' ((fun x => g + x) ⁻¹' A) = (fun y => (g : G) + y) ⁻¹' (Subtype.val '' A) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨g + x, hx, rfl⟩
      · rintro ⟨z, hz, hzy⟩
        have hy : y = -(g : G) + z := by
          rw [hzy]
          exact (neg_add_cancel_left _ _).symm
        have hyK : y ∈ K := by
          rw [hy]
          exact K.add_mem (K.neg_mem g.2) z.2
        refine ⟨⟨y, hyK⟩, ?_, rfl⟩
        have hz' : z = g + ⟨y, hyK⟩ := Subtype.ext hzy
        show g + ⟨y, hyK⟩ ∈ A
        rw [← hz']
        exact hz
    rw [hs, measure_preimage_add]
  have hm : MeasurableSet ((H.addSubgroupOf K : AddSubgroup K) : Set K) := measurable_subtype_coe hH
  have h1 := AddSubgroup.index_mul_measure (H.addSubgroupOf K) hm (μ.comap (Subtype.val : K → G))
  rw [he.comap_apply, he.comap_apply, Set.image_univ, Subtype.range_coe] at h1
  have h2 : Subtype.val '' ((H.addSubgroupOf K : AddSubgroup K) : Set K) = H := by
    ext y
    simp only [Set.mem_image, SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      exact ⟨⟨y, hHK hy⟩, hy, rfl⟩
  rw [h2] at h1
  rw [← h1]
  rfl

theorem lat_index_smul {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {L : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) (t : kˣ) (ht : nabs k t < 1) :
    (L.relIndex (((t⁻¹ : kˣ) : k) • L) : ℝ) = (nabs k t)⁻¹ ^ Module.finrank k Z := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨P, hP⟩ := exists_PZ Z
  have hPe : ∀ a, P (eZ Z a) = a := fun a => LinearMap.congr_fun hP a
  have hsurj : ∀ x ∈ Z, ∃ a, eZ Z a = x := fun x hx => ⟨_, eZ_surj Z hx⟩
  have hvt : ValuativeRel.valuation k (t : k) ≤ 1 := (val_lt_one_of_nabs ht).le
  have hLsub : L ≤ ((t⁻¹ : kˣ) : k) • L := by
    intro x hx
    rw [AddSubgroup.mem_smul_pointwise_iff_exists]
    refine ⟨(t : k) • x, hL.int _ hvt x hx, ?_⟩
    rw [smul_smul, Units.inv_mul, one_smul]
  have hi : L.relIndex (((t⁻¹ : kˣ) : k) • L) ≠ 0 := lat_index_pos (isLat_smul hL t⁻¹) hL hLsub
  let e : (Fin (Module.finrank k Z) → k) →+ Matrix (Fin n) (Fin n) k := (eZ Z).toAddMonoidHom
  have he : ∀ a, e a = eZ Z a := fun _ => rfl
  have hidx : L.relIndex (((t⁻¹ : kˣ) : k) • L) =
      (L.comap e).relIndex ((((t⁻¹ : kˣ) : k) • L).comap e) := by
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq]
    congr 1
    refine (inf_eq_right.mpr ?_).symm
    intro x hx
    rw [AddSubgroup.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨a, ha⟩ := hsurj _ (Z.smul_mem (hL.sub hb) _)
    exact ⟨a, ha⟩
  have hLK : L.comap e ≤ (((t⁻¹ : kˣ) : k) • L).comap e := fun y hy => hLsub hy
  have hLeq : ((L.comap e : AddSubgroup _) : Set (Fin (Module.finrank k Z) → k)) = P '' (L : Set _) := by
    ext y
    constructor
    · intro hy
      exact ⟨e y, hy, hPe y⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := hsurj x (hL.sub hx)
      show e (P (eZ Z a)) ∈ L
      rw [hPe]
      exact hx
  have hKeq : (((((t⁻¹ : kˣ) : k) • L).comap e : AddSubgroup _) : Set (Fin (Module.finrank k Z) → k)) =
      (t⁻¹ : kˣ) • ((L.comap e : AddSubgroup _) : Set (Fin (Module.finrank k Z) → k)) := by
    ext y
    simp only [SetLike.mem_coe, AddSubgroup.mem_comap, Set.mem_smul_set, AddSubgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨b, hb, hby⟩
      obtain ⟨a, rfl⟩ := hsurj b (hL.sub hb)
      refine ⟨a, hb, ?_⟩
      rw [Units.smul_def]
      apply_fun P at hby
      rw [he, ← LinearMap.map_smul, hPe, hPe] at hby
      exact hby
    · rintro ⟨a, ha, rfl⟩
      refine ⟨e a, ha, ?_⟩
      rw [Units.smul_def, he, he, LinearMap.map_smul]
  obtain ⟨U, hUo, hU0, hUL⟩ := hL.nhd
  have hopen : IsOpen ((L.comap e : AddSubgroup _) : Set (Fin (Module.finrank k Z) → k)) := by
    apply AddSubgroup.isOpen_of_mem_nhds _ (g := 0)
    have hU : (eZ Z) ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank k Z) → k) :=
      (continuous_eZ Z).continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hUo.mem_nhds hU0)
    refine Filter.mem_of_superset hU fun y hy => ?_
    exact hUL ⟨hy, eZ_mem Z y⟩
  have hcpt : IsCompact ((L.comap e : AddSubgroup _) : Set (Fin (Module.finrank k Z) → k)) := by
    rw [hLeq]
    exact hL.cpt.image (continuous_linear_mat P)
  let μ : Measure (Fin (Module.finrank k Z) → k) := Measure.addHaar
  have hK : MeasurableSet (((((t⁻¹ : kˣ) : k) • L).comap e : AddSubgroup _) : Set (Fin (Module.finrank k Z) → k)) := by
    rw [hKeq]
    exact (hopen.smul _).measurableSet
  have h1 := measure_eq_relIndex_mul_of_le μ hLK hopen.measurableSet hK (hidx ▸ hi)
  have h2 := distribHaarChar_mul μ (t⁻¹ : kˣ) ((L.comap e : AddSubgroup _) : Set (Fin (Module.finrank k Z) → k))
  rw [← hKeq, h1, distribHaarChar_pi, map_inv, ← hidx] at h2
  have h0 : μ ((L.comap e : AddSubgroup _) : Set (Fin (Module.finrank k Z) → k)) ≠ 0 :=
    (Measure.measure_pos_of_mem_nhds (μ := μ) (hopen.mem_nhds (AddSubgroup.zero_mem _))).ne'
  have htop := hcpt.measure_lt_top (μ := μ)
  have h3 := (ENNReal.mul_left_inj h0 htop.ne).mp h2
  have h4 := congrArg ENNReal.toReal h3
  simp only [ENNReal.toReal_natCast, ENNReal.coe_toReal, NNReal.coe_pow, NNReal.coe_inv] at h4
  rw [← h4]
  rfl

end Index

end PositivityTheory.RgUd.TP.Nil.Fib1
