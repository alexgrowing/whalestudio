import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitOfSumEqZero

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele

namespace GlobalTheory.IdeleCovolume

open NumberField.Units NumberField.Units.dirichletUnitTheorem in

theorem exists_bound_log (E : Type) [Field E] [NumberField E] :
    ∃ R : ℝ, ∀ t : InfinitePlace E → ℝ, ∃ (u : (𝓞 E)ˣ) (n : ℤ), ∀ w : InfinitePlace E,
      |t w + Real.log (w (u : E)) + n| ≤ R := by
  first
  | exact @_root_.GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le
  | exact _root_.GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le
  | (apply _root_.GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerUnitBound.exists_unit_int_abs_le ..)

theorem isCompact_units {A : Type} [Monoid A] [TopologicalSpace A] [ContinuousMul A] [T1Space A] {C : Set A}
    (hC : IsCompact C) : IsCompact {x : Aˣ | (x : A) ∈ C ∧ ((x⁻¹ : Aˣ) : A) ∈ C} := by
  have h2 := (Units.isClosedEmbedding_embedProduct (α := A)).isCompact_preimage
    (hC.prod (hC.image MulOpposite.continuous_op))
  convert h2 using 1
  ext g
  constructor
  · rintro ⟨h1, h1'⟩
    exact ⟨h1, _, h1', rfl⟩
  · rintro ⟨h1, m, hm, hm'⟩
    refine ⟨h1, ?_⟩
    have : m = ((g⁻¹ : Aˣ) : A) := MulOpposite.op_injective hm'
    rw [← this]; exact hm

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]

abbrev diag : Eˣ →* (Ad E)ˣ := Units.map (algebraMap E (Ad E)).toMonoidHom

def eIdele : (Ad E)ˣ := infId E (expU fun _ : InfinitePlace E => ((1 : ℝ) : ℂ))

theorem pInf_eIdele (w : InfinitePlace E) : pInf E (eIdele E : Ad E) w = Complex.exp 1 := by
  have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  change pInf E (1 - sInf E 1 + sInf E _) w = _
  simp only [map_add, map_sub, map_one, h, sub_self, zero_add]
  rfl

theorem pFin_eIdele : pFin E (eIdele E : Ad E) = 1 := by
  change (1 : Af E) - 0 + 0 = 1
  simp

theorem isCompact_box (r : ℝ) :
    IsCompact {x : Ad E | (∀ w, ‖pInf E x w‖ ≤ r) ∧ ∀ v, pFin E x v ∈ v.adicCompletionIntegers E} := by
  have h1 : IsCompact (Set.pi Set.univ fun _ : InfinitePlace E => Metric.closedBall (0 : ℂ) r) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have h2 := (h1.image (continuous_infEq E)).prod (GlobalTheory.AdeleCocompact.isCompact_integral E)
  have h3 : IsCompact (X := Ad E) _ := h2
  refine Eq.mpr (congrArg IsCompact (Set.ext fun x => ?_)) h3
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨⟨pInf E x, fun w _ => mem_closedBall_zero_iff.2 (h w), (infEq E).apply_symm_apply _⟩, h'⟩
  · rintro ⟨⟨y, hy, e⟩, h'⟩
    refine ⟨fun w => ?_, h'⟩
    have : pInf E x = y := (infEq E).symm_apply_eq.2 e.symm
    rw [this]
    exact mem_closedBall_zero_iff.1 (hy w trivial)

theorem exists_compact_unit : ∃ K : Set (Ad E)ˣ, IsCompact K ∧ ∀ a ∈ GlobalTheory.Mem.Chr.unitIdl E,
    ∃ (k : Eˣ) (n : ℤ), diag E k * eIdele E ^ n * a ∈ K := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  obtain ⟨R, hR⟩ := exists_bound_log E
  refine ⟨_, isCompact_units (isCompact_box E (Real.exp R)), fun a ha => ?_⟩
  obtain ⟨u, n, hu⟩ := hR fun w => Real.log ‖pInf E (a : Ad E) w‖
  let k : Eˣ := Units.map (algebraMap (𝓞 E) E).toMonoidHom u
  refine ⟨k, n, ?_⟩
  have hk : diag E k ∈ GlobalTheory.Mem.Chr.unitIdl E := fun v => by
    have h1 : ∀ z : (𝓞 E)ˣ, Valued.v (pFin E (diag E (Units.map (algebraMap (𝓞 E) E).toMonoidHom z) : Ad E) v) ≤ 1 :=
      fun z => HeightOneSpectrum.coe_mem_adicCompletionIntegers v (z : 𝓞 E)
    have h2 := h1 u⁻¹
    rw [map_inv, map_inv] at h2
    have e : pFin E (diag E k : Ad E) v * pFin E (((diag E k)⁻¹ : (Ad E)ˣ) : Ad E) v = 1 :=
      congrArg (fun a : Ad E => a.2 v) (diag E k).mul_inv
    have e' := congrArg Valued.v e
    rw [map_mul, map_one] at e'
    exact eq_one_of_one_le_mul_left (h1 u) h2 e'.ge
  have he : eIdele E ∈ GlobalTheory.Mem.Chr.unitIdl E := fun v => by
    change Valued.v (pFin E (eIdele E : Ad E) v) = 1
    rw [pFin_eIdele]
    exact map_one _
  have hmem : diag E k * eIdele E ^ n * a ∈ GlobalTheory.Mem.Chr.unitIdl E := mul_mem (mul_mem hk (zpow_mem he n)) ha
  let N : InfinitePlace E → ((Ad E)ˣ →* ℝ) := fun w =>
    ((normHom (α := ℂ)).toMonoidHom.comp
      (((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).comp (pInf E)).toMonoidHom)).comp (Units.coeHom _)
  have hN : ∀ w x, N w x = ‖pInf E (x : Ad E) w‖ := fun _ _ => rfl
  have hpos : ∀ w x, 0 < N w x := fun w x =>
    lt_of_le_of_ne (hN w x ▸ norm_nonneg _) ((Group.isUnit x).map (N w)).ne_zero.symm
  have hlog : ∀ w, |Real.log (N w (diag E k * eIdele E ^ n * a))| ≤ R := fun w => by
    have h1 : N w (diag E k) = w (u : E) := by
      rw [hN]
      change ‖pInf E (algebraMap E (Ad E) (u : E)) w‖ = _
      rw [pInf_algebraMap, InfinitePlace.norm_embedding_eq]
    have h2 : Real.log (N w (eIdele E)) = 1 := by
      rw [hN, pInf_eIdele, Complex.norm_exp, Real.log_exp, Complex.one_re]
    rw [map_mul, map_mul, Real.log_mul (mul_pos (hpos _ _) (hpos _ _)).ne' (hpos _ _).ne',
      Real.log_mul (hpos _ _).ne' (hpos _ _).ne', map_zpow, Real.log_zpow, h2, h1, hN]
    convert hu w using 2
    ring
  refine ⟨⟨fun w => ?_, fun v => (hmem v).le⟩, fun w => ?_, fun v => (inv_mem hmem v).le⟩
  · rw [← hN, ← Real.log_le_iff_le_exp (hpos _ _)]
    exact (abs_le.1 (hlog w)).2
  · rw [← hN, ← Real.log_le_iff_le_exp (hpos _ _), map_inv, Real.log_inv]
    linarith [(abs_le.1 (hlog w)).1]

theorem exists_compact_idele : ∃ K : Set (Ad E)ˣ, IsCompact K ∧ ∀ x : (Ad E)ˣ,
    ∃ (k : Eˣ) (n : ℤ), diag E k * eIdele E ^ n * x ∈ K := by
  obtain ⟨K, hK, h⟩ := exists_compact_unit E
  let S : Subgroup (Ad E)ˣ := GlobalTheory.Mem.Chr.unitIdl E ⊔ (diag E).range
  haveI : S.FiniteIndex := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup E
  refine ⟨⋃ q : (Ad E)ˣ ⧸ S, (· * q.out) '' K,
    isCompact_iUnion fun q => hK.image (continuous_id.mul continuous_const), fun x => ?_⟩
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S x
  obtain ⟨a, ha, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 (inv_mem s.2)
  obtain ⟨k', n, hk⟩ := h a ha
  refine ⟨k' * k⁻¹, n, Set.mem_iUnion.2 ⟨(x : (Ad E)ˣ ⧸ S), _, hk, ?_⟩⟩
  have : a = (s : (Ad E)ˣ)⁻¹ * (diag E k)⁻¹ := eq_mul_inv_of_mul_eq e
  simp only [hs, map_mul, map_inv, this]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem one_lt_ideleNorm_eIdele : 1 < ideleNorm (E := E) (eIdele E) := by
  have h1 : ∀ v : InfinitePlace E, ‖(eIdele E : Ad E).1 v‖ = Real.exp 1 := fun v => by
    have := pInf_eIdele E v
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]
    refine (congrArg norm this).trans ?_
    rw [Complex.norm_exp, Complex.one_re]
  have h2 : ∀ v : HeightOneSpectrum (𝓞 E), ‖(eIdele E : Ad E).2 v‖ = 1 := fun v => by
    change ‖pFin E (eIdele E : Ad E) v‖ = 1
    rw [pFin_eIdele]
    exact norm_one
  change 1 < (∏ v : InfinitePlace E, ‖(eIdele E : Ad E).1 v‖ ^ v.mult) *
    (∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖(eIdele E : Ad E).2 v‖)
  simp only [h1, h2, finprod_one, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  exact one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) Module.finrank_pos.ne'

theorem exists_nhds_idele : ∃ W ∈ 𝓝 (1 : (Ad E)ˣ), ∀ (k : Eˣ) (n : ℤ), diag E k * eIdele E ^ n ∈ W →
    diag E k * eIdele E ^ n = 1 := by
  obtain ⟨U, hU, h⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero E
  have hL : 0 < Real.log (ideleNorm (E := E) (eIdele E)) := Real.log_pos (one_lt_ideleNorm_eIdele E)
  have h1 : (fun x : (Ad E)ˣ => (x : Ad E) - 1) ⁻¹' U ∈ 𝓝 (1 : (Ad E)ˣ) :=
    (Units.continuous_val.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hU)
  have h2 : {x : (Ad E)ˣ | |Real.log (ideleNorm (E := E) x)| < Real.log (ideleNorm (E := E) (eIdele E))} ∈
      𝓝 (1 : (Ad E)ˣ) :=
    (isOpen_lt (continuous_ideleNorm.log ideleNorm_ne_zero).abs continuous_const).mem_nhds (by simpa using hL)
  refine ⟨_, Filter.inter_mem h1 h2, fun k n ⟨h3, h4⟩ => ?_⟩
  have h5 : ideleNorm (E := E) (diag E k) = 1 := ideleNorm_principalIdele k
  rw [Set.mem_setOf_eq, map_mul, h5, one_mul, map_zpow, Real.log_zpow, abs_mul, abs_of_pos hL,
    mul_lt_iff_lt_one_left hL] at h4
  have hn : n = 0 := Int.abs_lt_one_iff.1 (by exact_mod_cast h4)
  subst hn
  rw [zpow_zero, mul_one] at h3 ⊢
  have h6 := h ((k : E) - 1) (by rw [map_sub, map_one]; exact h3)
  rw [show k = 1 from Units.ext (sub_eq_zero.1 h6), map_one]

abbrev toGL : (Ad E)ˣ →* GA E 1 := GeneralLinearGroup.scalar (Fin 1)

omit [IsTotallyComplex E] in
theorem det_toGL (x : (Ad E)ˣ) : GeneralLinearGroup.det (toGL E x) = x :=
  Units.ext (by
    change (Matrix.scalar (Fin 1) (x : Ad E)).det = x
    simp)

omit [IsTotallyComplex E] in
theorem toGL_det (g : GA E 1) : toGL E (GeneralLinearGroup.det g) = g := by
  ext i j
  change Matrix.scalar (Fin 1) (g : Matrix (Fin 1) (Fin 1) (Ad E)).det i j = _
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, Matrix.det_fin_one]
  simp

omit [IsTotallyComplex E] in
theorem continuous_toGL : Continuous (toGL E) :=
  Continuous.units_map _ (by
    change Continuous fun x : Ad E => Matrix.diagonal fun _ : Fin 1 => x
    exact (continuous_pi fun _ => continuous_id).matrix_diagonal)

theorem det_splitCentre : GeneralLinearGroup.det (splitCentre E 1 1) = eIdele E := by
  rw [splitCentre, det_infGL, eIdele]
  congr 1
  refine Units.ext ?_
  change (Matrix.scalar (Fin 1) _).det = _
  simp

omit [IsTotallyComplex E] in
theorem det_ratGL (g : GL (Fin 1) E) : GeneralLinearGroup.det (ratGL E 1 g) = diag E (GeneralLinearGroup.det g) :=
  Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)

theorem mem_latticeGL (g : GA E 1) :
    g ∈ latticeGL E 1 ↔ ∃ (k : Eˣ) (n : ℤ), diag E k * eIdele E ^ n = GeneralLinearGroup.det g := by
  constructor
  · intro hg
    have : latticeGL E 1 ≤ ((diag E).range ⊔ Subgroup.zpowers (eIdele E)).comap GeneralLinearGroup.det := by
      refine sup_le ?_ ?_
      · rintro _ ⟨g, rfl⟩
        exact Subgroup.mem_sup_left ⟨_, (det_ratGL E g).symm⟩
      · rw [Subgroup.zpowers_le, Subgroup.mem_comap, det_splitCentre]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    obtain ⟨_, ⟨k, rfl⟩, _, ⟨n, rfl⟩, e⟩ := Subgroup.mem_sup.1 (this hg)
    exact ⟨k, n, e⟩
  · rintro ⟨k, n, e⟩
    have h1 : toGL E (diag E k) = ratGL E 1 (GeneralLinearGroup.scalar (Fin 1) k) := by
      rw [← toGL_det E (ratGL E 1 _), det_ratGL]
      congr 2
      refine Units.ext ?_
      change _ = (Matrix.scalar (Fin 1) (k : E)).det
      simp
    rw [← toGL_det E g, ← e, map_mul, map_zpow, ← det_splitCentre, toGL_det, h1]
    exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨n, rfl⟩

theorem discrete_latticeGL : DiscreteTopology (latticeGL E 1) := by
  obtain ⟨W, hW, h⟩ := exists_nhds_idele E
  refine discreteTopology_of_isOpen_singleton_one ?_
  have h1 : (fun γ : latticeGL E 1 => GeneralLinearGroup.det (γ : GA E 1)) ⁻¹' W ∈ 𝓝 1 :=
    (GeneralLinearGroup.continuous_det.comp continuous_subtype_val).continuousAt.preimage_mem_nhds (by simpa using hW)
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ rfl
  refine Filter.mem_of_superset h1 fun γ hγ => ?_
  obtain ⟨k, n, e⟩ := (mem_latticeGL E γ).1 γ.2
  refine Subtype.ext ?_
  have h2 := h k n (e ▸ hγ)
  rw [← toGL_det E γ, ← e, h2, map_one]
  rfl

theorem exists_compact_latticeGL :
    ∃ K : Set (GA E 1), IsCompact K ∧ ∀ g, ∃ γ ∈ latticeGL E 1, γ * g ∈ K := by
  obtain ⟨K, hK, h⟩ := exists_compact_idele E
  refine ⟨toGL E '' K, hK.image (continuous_toGL E), fun g => ?_⟩
  obtain ⟨k, n, hk⟩ := h (GeneralLinearGroup.det g)
  exact ⟨toGL E (diag E k * eIdele E ^ n), (mem_latticeGL E _).2 ⟨k, n, (det_toGL E _).symm⟩,
    _, hk, by rw [map_mul (toGL E), toGL_det]⟩

theorem isSqInt_const (c : ℂ) : IsSqInt fun _ : GA E 1 => c := by
  refine ⟨fun _ _ => rfl, ?_⟩
  letI : MeasurableSpace (GA E 1) := borel _
  haveI : BorelSpace (GA E 1) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin 1) (Fin 1) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 1 → Fin 1 → Ad E))
  haveI : LocallyCompactSpace (Matrix (Fin 1) (Fin 1) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GA E 1) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin 1) (Fin 1) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin 1 → Fin 1 → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin 1) (Fin 1) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GA E 1) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI := discrete_latticeGL E
  haveI : Countable (latticeGL E 1) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, hK, hcov⟩ := exists_compact_latticeGL E
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (latticeGL E 1) Measure.haar
  refine ⟨Measure.haar, 𝓕, inferInstance, h𝓕, ?_⟩
  have h := GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (latticeGL E 1) K hK hcov Measure.haar inferInstance 𝓕 h𝓕
    (fun _ => c ^ 2) continuous_const fun _ _ _ => rfl
  simpa only [HasFiniteIntegral, enorm_pow] using h.2

theorem isDiscrete_const_one : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E],
    GlobalTheory.UnitaryBC.IsDiscrete (Submodule.span ℂ {GlobalTheory.CuspRep.oneFn E 1}) :=
  fun E _ _ _ => isDiscrete_const fun c => isSqInt_const E (c * 1)

end GlobalTheory.IdeleCovolume

end
