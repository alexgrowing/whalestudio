import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScalingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AnnihilatorOfAnnihilatorLeStatement
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHI
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups nonZeroDivisors Pointwise

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.Core.SelfDual

section Arith

variable (F : Type) [Field F] [NumberField F]

def dinv : AddSubgroup F := (Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 F) F)).toAddSubgroup

def oG : AddSubgroup F := (1 : Submodule (𝓞 F) F).toAddSubgroup

variable {F}

theorem mem_oG {b : F} : b ∈ oG F ↔ ∃ r : 𝓞 F, (r : F) = b := by
  unfold oG
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_one]

theorem mem_dinv {b : F} :
    b ∈ dinv F ↔ ∀ r : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (b * (r : F)) = n := by
  unfold dinv
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_traceDual]
  constructor
  · intro h r
    obtain ⟨n, hn⟩ := h r (Submodule.mem_one.2 ⟨r, rfl⟩)
    exact ⟨n, by simpa [Algebra.traceForm_apply] using hn.symm⟩
  · intro h a ha
    obtain ⟨r, rfl⟩ := Submodule.mem_one.1 ha
    obtain ⟨n, hn⟩ := h r
    exact ⟨n, by simpa [Algebra.traceForm_apply] using hn.symm⟩

theorem oG_le_dinv : oG F ≤ dinv F := fun _ hx => Submodule.one_le_traceDual_one hx

theorem oG_eq_closure : oG F = AddSubgroup.closure (Set.range (integralBasis F)) := by
  ext x
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    mem_span_integralBasis, mem_oG]
  rfl

open scoped Classical in
theorem dinv_eq_closure :
    dinv F = AddSubgroup.closure (Set.range (integralBasis F).traceDual) := by
  have h := Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 F) F) (integralBasis F) (by
    ext x
    rw [Submodule.restrictScalars_mem, mem_span_integralBasis, Submodule.mem_one]
    rfl)
  rw [← Submodule.span_int_eq_addSubgroupClosure, ← h]
  rfl

theorem relIndex_oG_dinv : (oG F).relIndex (dinv F) = (discr F).natAbs := by
  classical
  set e := integralBasis F with he
  have h2 : dinv F = AddSubgroup.closure (Set.range e.traceDual) := dinv_eq_closure
  have key := AddSubgroup.relIndex_eq_abs_det (oG F) (dinv F) oG_le_dinv e e.traceDual
    oG_eq_closure h2
  have hdet : e.traceDual.det e = ((discr F : ℤ) : ℚ) := by
    rw [coe_discr, Algebra.discr_def, Module.Basis.det_apply]
    congr 1
    ext i j
    simp [Module.Basis.toMatrix_apply, Module.Basis.traceDual_repr_apply,
      Algebra.traceMatrix_apply, Algebra.traceForm_apply, he, mul_comm]
  rw [hdet] at key
  have : (((oG F).relIndex (dinv F) : ℕ) : ℚ) = (((discr F).natAbs : ℕ) : ℚ) := by
    rw [key, Nat.cast_natAbs, Int.cast_abs]
  exact_mod_cast this

theorem mem_oG_of_dual {b : F} (h : ∀ d ∈ dinv F, ∃ n : ℤ, Algebra.trace ℚ F (d * b) = n) :
    b ∈ oG F := by
  classical
  set e := integralBasis F with he
  have hmem : ∀ i, e.traceDual i ∈ dinv F := by
    intro i
    rw [dinv_eq_closure]
    exact AddSubgroup.subset_closure (Set.mem_range_self i)
  have hrepr : ∀ i, ∃ n : ℤ, e.repr b i = n := by
    intro i
    obtain ⟨n, hn⟩ := h _ (hmem i)
    refine ⟨n, ?_⟩
    have := Module.Basis.traceDual_repr_apply e.traceDual b i
    rw [Module.Basis.traceDual_traceDual, Algebra.traceForm_apply, mul_comm] at this
    rw [this, hn]
  rw [← e.sum_repr b, oG_eq_closure]
  refine sum_mem fun i _ => ?_
  obtain ⟨n, hn⟩ := hrepr i
  rw [hn, Int.cast_smul_eq_zsmul]
  exact zsmul_mem (AddSubgroup.subset_closure (Set.mem_range_self i)) n

end Arith

section Generic

variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

theorem isCompact_of_relIndex {H K : AddSubgroup G} (hHK : H ≤ K) (hi : H.relIndex K ≠ 0)
    (hH : IsCompact (H : Set G)) : IsCompact (K : Set G) := by
  have : (H.addSubgroupOf K).FiniteIndex := ⟨hi⟩
  have hT : (Set.range fun q : K ⧸ H.addSubgroupOf K => ((Quotient.out q : K) : G)).Finite :=
    Set.finite_range _
  have e : (K : Set G) =
      (Set.range fun q : K ⧸ H.addSubgroupOf K => ((Quotient.out q : K) : G)) + (H : Set G) := by
    ext x
    constructor
    · intro hx
      have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq'
        (QuotientAddGroup.mk (⟨x, hx⟩ : K) : K ⧸ H.addSubgroupOf K))
      refine Set.mem_add.2 ⟨_, ⟨QuotientAddGroup.mk (⟨x, hx⟩ : K), rfl⟩, _, ?_, add_neg_cancel_left _ x⟩
      simpa [AddSubgroup.mem_addSubgroupOf] using h
    · rintro ⟨_, ⟨q, rfl⟩, h, hh, rfl⟩
      exact K.add_mem (Quotient.out q).2 (hHK hh)
  rw [e]
  exact hT.isCompact.add hH

end Generic

section Adelic

variable (F : Type) [Field F] [NumberField F]

def ohG : AddSubgroup (A F) where
  carrier := Oh F
  add_mem' := fun ha hb v => add_mem (ha v) (hb v)
  zero_mem' := fun v => zero_mem (v.adicCompletionIntegers F)
  neg_mem' := fun ha v => neg_mem (ha v)

def fr : F →+ A F := (algebraMap F (A F)).toAddMonoidHom

variable {F}

theorem oh_mul {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x * y ∈ Oh F :=
  fun v => mul_mem (hx v) (hy v)

def perpG (ψ : AddChar (A F) ℂ) (L : AddSubgroup (A F)) : AddSubgroup (A F) where
  carrier := perp (fun x y => ψ (x * y)) L
  add_mem' := fun {a b} ha hb x hx => by
    have h1 : ψ (x * a) = 1 := ha x hx
    have h2 : ψ (x * b) = 1 := hb x hx
    show ψ (x * (a + b)) = 1
    rw [mul_add, AddChar.map_add_eq_mul, h1, h2, one_mul]
  zero_mem' := fun x _ => by
    show ψ (x * 0) = 1
    rw [mul_zero, AddChar.map_zero_eq_one]
  neg_mem' := fun {a} ha x hx => by
    have h1 : ψ (x * a) = 1 := ha x hx
    show ψ (x * -a) = 1
    rw [mul_neg, AddChar.map_neg_eq_inv, h1, inv_one]

abbrev MG (ψ : AddChar (A F) ℂ) : AddSubgroup (A F) := perpG ψ (ohG F)

variable {ψ : AddChar (A F) ℂ}

theorem ohG_le_MG (hψ : IsStdChar F ψ) : ohG F ≤ MG ψ :=
  fun _ hx z hz => ((GlobalTheory.T.standard_adelic_character F).2 ψ hψ).2.1 _ (oh_mul hz hx)

theorem algebraMap_mem_MG_iff (hψ : IsStdChar F ψ) {b : F} :
    algebraMap F (A F) b ∈ MG ψ ↔ b ∈ dinv F := by
  rw [mem_dinv, ← ((GlobalTheory.T.standard_adelic_character F).2 ψ hψ).2.2 b]
  exact forall₂_congr fun z _ => by
    show ψ (z * _) = 1 ↔ _
    rw [mul_comm]

theorem MG_eq (hψ : IsStdChar F ψ) : MG ψ = (dinv F).map (fr F) ⊔ ohG F := by
  obtain ⟨-, -, -, -, hop, hden, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  apply le_antisymm
  · intro x hx
    have hopen : IsOpen {y : A F | y - x ∈ Oh F} :=
      hop.preimage (continuous_id.sub continuous_const)
    obtain ⟨b, hb⟩ := hden.exists_mem_open hopen ⟨x, by
      show x - x ∈ Oh F
      rw [sub_self]
      exact (ohG F).zero_mem⟩
    have hb' : algebraMap F (A F) b - x ∈ ohG F := hb
    have hbM : algebraMap F (A F) b ∈ MG ψ := by
      have := (MG ψ).add_mem hx (ohG_le_MG hψ hb')
      simpa using this
    have e : x = algebraMap F (A F) b + -(algebraMap F (A F) b - x) := by abel
    rw [e]
    exact add_mem (AddSubgroup.mem_sup_left ⟨b, (algebraMap_mem_MG_iff hψ).1 hbM, rfl⟩)
      (AddSubgroup.mem_sup_right (neg_mem hb'))
  · refine sup_le ?_ (ohG_le_MG hψ)
    rintro _ ⟨b, hb, rfl⟩
    exact (algebraMap_mem_MG_iff hψ).2 hb

theorem comap_ohG : (ohG F).comap (fr F) = oG F := by
  obtain ⟨-, -, -, -, -, -, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  ext b
  rw [mem_oG, ← hint b]
  rfl

theorem relIndex_MG (hψ : IsStdChar F ψ) : (ohG F).relIndex (MG ψ) = (discr F).natAbs := by
  rw [MG_eq hψ, AddSubgroup.relIndex_sup_right, ← AddSubgroup.relIndex_comap, comap_ohG]
  exact relIndex_oG_dinv

theorem perp_MG_subset (hψ : IsStdChar F ψ) :
    perp (fun x y => ψ (x * y)) (MG ψ : Set (A F)) ⊆ Oh F := by
  obtain ⟨-, -, -, -, -, -, hint, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  intro y hy
  have hyM : y ∈ MG ψ := fun z hz => hy z (ohG_le_MG hψ hz)
  rw [MG_eq hψ] at hyM
  obtain ⟨u, hu, o, ho, rfl⟩ := AddSubgroup.mem_sup.1 hyM
  obtain ⟨b, hb, rfl⟩ := hu
  have hbO : b ∈ oG F := by
    refine mem_oG_of_dual fun d hd => ?_
    have hd' : algebraMap F (A F) d ∈ MG ψ := (algebraMap_mem_MG_iff hψ).2 hd
    have h1 : ψ (algebraMap F (A F) d * (fr F b + o)) = 1 := hy _ hd'
    have h2 : ψ (o * algebraMap F (A F) d) = 1 := hd' o ho
    have e : fr F b = algebraMap F (A F) b := rfl
    rw [e, mul_add, AddChar.map_add_eq_mul, mul_comm (algebraMap F (A F) d) o, h2, mul_one,
      ← map_mul, hψ.2] at h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
    refine ⟨-n, ?_⟩
    have h3 : ((Algebra.trace ℚ F (d * b) : ℚ) : ℂ) = ((-n : ℤ) : ℂ) := by
      refine mul_right_cancel₀ Complex.two_pi_I_ne_zero ?_
      push_cast
      linear_combination -hn
    exact_mod_cast h3
  exact (ohG F).add_mem ((hint b).2 (mem_oG.1 hbO)) ho

def sc (c : F) (hc : c ≠ 0) : A F ≃ₜ A F where
  toFun x := algebraMap F (A F) c * x
  invFun x := algebraMap F (A F) c⁻¹ * x
  left_inv x := by
    show algebraMap F (A F) c⁻¹ * (algebraMap F (A F) c * x) = x
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
  right_inv x := by
    show algebraMap F (A F) c * (algebraMap F (A F) c⁻¹ * x) = x
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

def lat (c : F) : AddSubgroup (A F) := (ohG F).map (AddMonoidHom.mulLeft (algebraMap F (A F) c))

theorem coe_lat (c : F) : (lat c : Set (A F)) = (fun x => algebraMap F (A F) c * x) '' Oh F := rfl

theorem perp_lat {c : F} (hc : c ≠ 0) : perp (fun x y => ψ (x * y)) (lat c : Set (A F)) =
    (fun x => algebraMap F (A F) c⁻¹ * x) '' (MG ψ : Set (A F)) := by
  have hcc : algebraMap F (A F) c * algebraMap F (A F) c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  ext y
  constructor
  · intro hy
    refine ⟨algebraMap F (A F) c * y, fun z hz => ?_, ?_⟩
    · have h : ψ (algebraMap F (A F) c * z * y) = 1 := hy _ ⟨z, hz, rfl⟩
      show ψ (z * (algebraMap F (A F) c * y)) = 1
      rwa [mul_left_comm, ← mul_assoc]
    · show algebraMap F (A F) c⁻¹ * (algebraMap F (A F) c * y) = y
      rw [← mul_assoc, mul_comm (algebraMap F (A F) c⁻¹), hcc, one_mul]
  · rintro ⟨m, hm, rfl⟩ _ ⟨z, hz, rfl⟩
    have h : ψ (z * m) = 1 := hm z hz
    show ψ (AddMonoidHom.mulLeft (algebraMap F (A F) c) z * (algebraMap F (A F) c⁻¹ * m)) = 1
    have e : AddMonoidHom.mulLeft (algebraMap F (A F) c) z * (algebraMap F (A F) c⁻¹ * m) = z * m := by
      show algebraMap F (A F) c * z * (algebraMap F (A F) c⁻¹ * m) = z * m
      calc _ = (algebraMap F (A F) c * algebraMap F (A F) c⁻¹) * (z * m) := by ring
        _ = z * m := by rw [hcc, one_mul]
    rw [e, h]

theorem perp_perp_lat (hψ : IsStdChar F ψ) {c : F} (hc : c ≠ 0) :
    perp (fun x y => ψ (x * y)) (perp (fun x y => ψ (x * y)) (lat c : Set (A F))) ⊆
      (lat c : Set (A F)) := by
  rw [perp_lat hc]
  intro y hy
  have hcc : algebraMap F (A F) c * algebraMap F (A F) c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  have h1 : algebraMap F (A F) c⁻¹ * y ∈ Oh F := by
    refine perp_MG_subset hψ fun m hm => ?_
    have h : ψ (algebraMap F (A F) c⁻¹ * m * y) = 1 := hy _ ⟨m, hm, rfl⟩
    show ψ (m * (algebraMap F (A F) c⁻¹ * y)) = 1
    rwa [mul_left_comm, ← mul_assoc]
  refine ⟨_, h1, ?_⟩
  show algebraMap F (A F) c * (algebraMap F (A F) c⁻¹ * y) = y
  rw [← mul_assoc, hcc, one_mul]

theorem natCast_mul_mem_lat (N : ℕ) {z : A F} (hz : z ∈ Oh F) : (N : A F) * z ∈ lat (N : F) :=
  ⟨z, hz, by
    show algebraMap F (A F) (N : F) * z = _
    rw [map_natCast]⟩

theorem mem_lat_inv {N : ℕ} (hN : 0 < N) {x : A F} (h : (N : A F) * x ∈ Oh F) :
    x ∈ lat ((N : F)⁻¹) :=
  ⟨_, h, by
    show algebraMap F (A F) (N : F)⁻¹ * ((N : A F) * x) = x
    have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
    rw [← map_natCast (algebraMap F (A F)) N, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hN', map_one,
      one_mul]⟩

theorem kap_sq : kap F ^ 2 * |(discr F : ℝ)| = 1 := by
  have hd : 0 < |(discr F : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  unfold kap
  rw [inv_pow, Real.sq_sqrt hd.le, inv_mul_cancel₀ hd.ne']

theorem kap_pos : 0 < kap F := by
  have hd : 0 < |(discr F : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  exact inv_pos.2 (Real.sqrt_pos.2 hd)

variable [MeasurableSpace (A F)] [BorelSpace (A F)]

theorem lat_all (hψ : IsStdChar F ψ) (lf : Measure (A F)) (hlf : lf.IsAddHaarMeasure)
    (h1 : lf (Oh F) = 1) {c : F} (hc : c ≠ 0) :
    IsCompact (lat c : Set (A F)) ∧ IsOpen (lat c : Set (A F)) ∧
      IsCompact (perp (fun x y => ψ (x * y)) (lat c : Set (A F))) ∧
      IsOpen (perp (fun x y => ψ (x * y)) (lat c : Set (A F))) ∧
      perp (fun x y => ψ (x * y)) (perp (fun x y => ψ (x * y)) (lat c : Set (A F))) ⊆
        (lat c : Set (A F)) ∧
      (ENNReal.ofReal (kap F) • lf) (lat c : Set (A F)) *
        (ENNReal.ofReal (kap F) • lf) (perp (fun x y => ψ (x * y)) (lat c : Set (A F))) = 1 := by
  obtain ⟨hlc, hsc, ht2, hcpt, hop, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hne : (ohG F).relIndex (MG ψ) ≠ 0 := by
    rw [relIndex_MG hψ]
    exact Int.natAbs_ne_zero.2 (discr_ne_zero F)
  have hMc : IsCompact (MG ψ : Set (A F)) := isCompact_of_relIndex (ohG_le_MG hψ) hne hcpt
  have hMo : IsOpen (MG ψ : Set (A F)) := AddSubgroup.isOpen_mono (ohG_le_MG hψ) hop
  have hMm : lf (MG ψ : Set (A F)) = ((discr F).natAbs : ℝ≥0∞) := by
    have h := PI.VolStabS.measure_eq_relIndex_mul lf (ohG F) (MG ψ) (ohG_le_MG hψ)
      hMo.measurableSet hop.measurableSet hne
    rw [h, relIndex_MG hψ]
    have h1' : lf (ohG F : Set (A F)) = 1 := h1
    rw [h1', mul_one]
  have hci : c⁻¹ ≠ 0 := inv_ne_zero hc
  have hs := (GlobalTheory.T.adelic_haar_measure_scaling F lf hlf h1).1
  refine ⟨?_, ?_, ?_, ?_, perp_perp_lat hψ hc, ?_⟩
  · rw [coe_lat]
    exact hcpt.image (sc c hc).continuous
  · rw [coe_lat]
    exact (sc c hc).isOpenMap _ hop
  · rw [perp_lat hc]
    exact hMc.image (sc c⁻¹ hci).continuous
  · rw [perp_lat hc]
    exact (sc c⁻¹ hci).isOpenMap _ hMo
  · rw [perp_lat hc, coe_lat, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      hs c hc _ hop.measurableSet, hs c⁻¹ hci _ hMo.measurableSet, h1, hMm, mul_one]
    have hr : 0 < |((Algebra.norm ℚ c : ℚ) : ℝ)| :=
      abs_pos.2 (by exact_mod_cast Algebra.norm_ne_zero_iff.2 hc)
    have hinv : |((Algebra.norm ℚ c⁻¹ : ℚ) : ℝ)|⁻¹ = |((Algebra.norm ℚ c : ℚ) : ℝ)| := by
      have hn : Algebra.norm ℚ c⁻¹ * Algebra.norm ℚ c = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hc, map_one]
      rw [eq_inv_of_mul_eq_one_left hn, Rat.cast_inv, abs_inv, inv_inv]
    have hD : ((discr F).natAbs : ℝ≥0∞) = ENNReal.ofReal |(discr F : ℝ)| := by
      rw [← ENNReal.ofReal_natCast, Nat.cast_natAbs, Int.cast_abs]
    rw [hinv, hD]
    generalize |((Algebra.norm ℚ c : ℚ) : ℝ)| = r at hr
    have hk : 0 ≤ kap F := kap_pos.le
    have e : kap F * r⁻¹ * (kap F * (r * |(discr F : ℝ)|)) = 1 := by
      calc _ = (kap F ^ 2 * |(discr F : ℝ)|) * (r⁻¹ * r) := by ring
        _ = 1 := by rw [kap_sq, inv_mul_cancel₀ hr.ne', one_mul]
    calc _ = ENNReal.ofReal (kap F * r⁻¹ * (kap F * (r * |(discr F : ℝ)|))) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hk (inv_nonneg.2 hr.le)), ENNReal.ofReal_mul hk,
            ENNReal.ofReal_mul hk, ENNReal.ofReal_mul hr.le]
      _ = 1 := by rw [e, ENNReal.ofReal_one]

end Adelic

theorem finiteAdeles_selfDual : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)]
    [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 →
    ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ →
      NADual (A F) (fun x y => ψ (x * y)) (ENNReal.ofReal (kap F) • lf) := by
  intro F _ _ _ _ lf hlf h1 ψ hψ
  obtain ⟨hlc, hsc, ht2, hcpt, hop, -, -, hsm, hbd, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hnorm := ((GlobalTheory.T.standard_adelic_character F).2 ψ hψ).1
  have hμ : (ENNReal.ofReal (kap F) • lf).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul lf (by simpa using kap_pos) ENNReal.ofReal_ne_top
  have hsymm : ∀ x y : A F, (fun x y => ψ (x * y)) x y = (fun x y => ψ (x * y)) y x :=
    fun x y => by simp only [mul_comm]
  have hadd : ∀ x x' y : A F, (fun x y => ψ (x * y)) (x + x') y =
      (fun x y => ψ (x * y)) x y * (fun x y => ψ (x * y)) x' y :=
    fun x x' y => by simp only [add_mul, AddChar.map_add_eq_mul]
  have hl := fun {c : F} (hc : c ≠ 0) => lat_all hψ lf hlf h1 hc
  have hNF : ∀ {N : ℕ}, 0 < N → (N : F) ≠ 0 := fun h => by exact_mod_cast h.ne'
  unfold NADual
  refine ⟨inferInstance, ht2, hlc, hsc, inferInstance, hμ, ?_, ?_, ?_, hsymm, fun x y => hnorm _,
    hadd, ?_⟩
  · intro U hU
    obtain ⟨N, hN, h⟩ := hsm U hU
    refine ⟨lat (N : F), (hl (hNF hN)).1, (hl (hNF hN)).2.1, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have e : AddMonoidHom.mulLeft (algebraMap F (A F) (N : F)) z = (N : A F) * z := by
      show algebraMap F (A F) (N : F) * z = _
      rw [map_natCast]
    rw [e]
    exact h z hz
  · intro x
    obtain ⟨N, hN, h⟩ := hbd {x} isCompact_singleton
    have hi := inv_ne_zero (hNF hN)
    exact ⟨lat (N : F)⁻¹, (hl hi).1, (hl hi).2.1, mem_lat_inv hN (h x rfl)⟩
  · exact hψ.1.comp (continuous_fst.mul continuous_snd)
  · intro L hLc hLo
    obtain ⟨N₁, hN₁, k₁⟩ := hsm _ (hLo.mem_nhds L.zero_mem)
    obtain ⟨N₂, hN₂, k₂⟩ := hbd _ hLc
    have a := hl (hNF hN₁)
    have b := hl (inv_ne_zero (hNF hN₂))
    refine GlobalTheory.T.annihilator_of_annihilator_le (A F) (fun x y => ψ (x * y)) (ENNReal.ofReal (kap F) • lf) hμ hsymm
      (fun x y => hnorm _) hadd (lat (N₁ : F)) L (lat (N₂ : F)⁻¹) ?_ ?_ a.2.1 b.1 a.2.2.1 b.2.2.2.1
      a.2.2.2.2.1 b.2.2.2.2.1 a.2.2.2.2.2 b.2.2.2.2.2
    · rintro _ ⟨z, hz, rfl⟩
      have e : AddMonoidHom.mulLeft (algebraMap F (A F) (N₁ : F)) z = (N₁ : A F) * z := by
        show algebraMap F (A F) (N₁ : F) * z = _
        rw [map_natCast]
      rw [e]
      exact k₁ z hz
    · exact fun x hx => mem_lat_inv hN₂ (k₂ x hx)

end GlobalTheory.CompanionTheory.SW.Core.SelfDual
