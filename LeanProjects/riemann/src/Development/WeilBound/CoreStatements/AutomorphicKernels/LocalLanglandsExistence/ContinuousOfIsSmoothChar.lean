import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DeligneLocalConstants
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PowFamIsDeligneMeas
import GroundTheory.GlobalFields.TateThesis.HeckeChar
import GroundTheory.LocalFields.LocalZetaEpsilon
import GroundTheory.LocalFields.LocalZetaGauss

noncomputable section

namespace PositivityTheory.Pf1.LocalLanglands.KernelCondition.G7

section Bridge

open ValuativeRel GroundTheory.LocalField

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ord_eq (x : kˣ) : GlobalTheory.SmGL.ord k x = ord (x : k) := by
  simp [GlobalTheory.SmGL.ord, ord, normalizedValuation_apply]

theorem val_le_iff_mem (y : k) (x : kˣ) : valuation k y ≤ valuation k (x : k) ↔ y ∈ valBall k (ord (x : k)) := by
  rw [mem_valBall, ← normalizedValuation_eq_exp_ord x.ne_zero, normalizedValuation_le_iff]

theorem mul_mem_valBall_iff (g : kˣ) (z : k) (j : ℤ) :
    (g : k) * z ∈ valBall k j ↔ z ∈ valBall k (j - ord (g : k)) := by
  by_cases hz : z = 0
  · subst hz; simp only [mul_zero]; exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  · rw [mem_valBall_iff_le_ord (mul_ne_zero g.ne_zero hz), mem_valBall_iff_le_ord hz, ord_mul g.ne_zero hz]
    omega

theorem continuous_of_isSmoothChar (χ : kˣ →* ℂˣ) (hχ : GlobalTheory.SmGL.IsSmoothChar χ) : Continuous χ := by
  refine continuous_of_continuousAt_one χ ?_
  have h : (χ.ker : Set kˣ) ∈ nhds (1 : kˣ) := hχ.mem_nhds χ.ker.one_mem
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [h] with x hx
  exact (MonoidHom.mem_ker.mp hx).symm

theorem hasConductor (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) :
    GlobalTheory.SplitWeil.HasConductor ψ (unifUnit k ^ addCharConductor ψ) := by
  intro x
  rw [val_le_iff_mem x (unifUnit k ^ addCharConductor ψ), ord_unifUnit_zpow]
  constructor
  · intro h
    by_cases hx : x = 0
    · subst hx; exact zero_mem _
    · have htriv : IsTrivialOn ψ (ord x) := fun y hy => h y (by
        rw [← normalizedValuation_le_iff, normalizedValuation_eq_exp_ord hx]; exact hy)
      exact (mem_valBall_iff_le_ord hx).2 ((isTrivialOn_iff hψ h1 (ord x)).1 htriv)
  · intro hx y hy
    exact isTrivialOn_addCharConductor hψ h1 y ((normalizedValuation_le_iff.2 hy).trans hx)

theorem mem_unitFilt_iff (b : ℕ) (x : kˣ) :
    x ∈ GlobalTheory.LocLanglands.unitFilt k b ↔ x ∈ unitFiltrationUnits k b := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [mem_unitFiltrationUnits_zero_iff]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rw [pow_zero]
    exact (Valuation.map_sub _ _ _).trans (by simp [h])
  · rw [mem_unitFiltrationUnits_iff_valBall hb]
    obtain ⟨p, hp, hpo⟩ := GlobalTheory.LocLanglands.exists_unit_pow k b
    have hpo' : ord (p : k) = b := by rw [← ord_eq]; exact hpo
    constructor
    · intro h
      have := (val_le_iff_mem ((x : k) - 1) p).1 (h.2.trans_eq hp.symm)
      rwa [hpo'] at this
    · intro h
      refine ⟨mem_unitFiltrationUnits_zero_iff.1
        (unitFiltrationUnits_antitone (Nat.zero_le b) ((mem_unitFiltrationUnits_iff_valBall hb).2 h)), ?_⟩
      rw [← hp]
      exact (val_le_iff_mem ((x : k) - 1) p).2 (by rwa [hpo'])

theorem hasExponent (χ : kˣ →* ℂˣ) (hχ : Continuous χ) :
    GlobalTheory.LocLanglands.HasExponent χ (quasiCharConductor χ) := by
  refine ⟨fun x hx => unitFiltrationUnits_quasiCharConductor_le_ker hχ ((mem_unitFilt_iff _ x).1 hx), fun b hb => ?_⟩
  by_contra h
  push Not at h
  have hle : quasiCharConductor χ ≤ b :=
    Nat.sInf_le (fun x hx => MonoidHom.mem_ker.2 (h x ((mem_unitFilt_iff b x).2 hx)))
  omega

theorem isUnram_of (χ : kˣ →* ℂˣ) (hu : IsUnramifiedChar χ) : GlobalTheory.SplitWeil.IsUnram χ := fun x hx =>
  isUnramifiedChar_iff.1 hu x (by rw [← ord_eq]; exact GlobalTheory.SmGL.ord_eq_zero hx)

theorem nabs_unif (n : ℤ) : GlobalTheory.SplitWeil.nabs k (unifUnit k ^ n) = (residueCard k : ℝ) ^ (-n) := by
  rw [GlobalTheory.LGrp.nabs_eq_zpow, ord_eq, ord_unifUnit_zpow]
  rfl

end Bridge

end PositivityTheory.Pf1.LocalLanglands.KernelCondition.G7

end

noncomputable section

namespace PositivityTheory.Pf1.LocalLanglands.KernelCondition.G7

section Shell

open ValuativeRel GroundTheory.LocalField

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def shellPt (m : ℤ) {a : ℕ} (t : unitsModFiltration k a) : kˣ := unifUnit k ^ m * unitsModRep t

theorem ord_shellPt (m : ℤ) {a : ℕ} (t : unitsModFiltration k a) : ord ((shellPt m t : kˣ) : k) = m := by
  rw [shellPt, ord_units_mul, ord_unifUnit_zpow, mem_unitFiltrationUnits_zero_iff_ord.1 (unitsModRep_mem t), add_zero]

theorem shellPt_injective (m : ℤ) (a : ℕ) : Function.Injective (shellPt (k := k) m (a := a)) := by
  intro x y h
  have h2 : unitsModRep x = unitsModRep y := mul_left_cancel h
  exact Quotient.out_inj.1 (Subtype.ext h2)

theorem shell_val_le_iff {n : ℤ} {a : ℕ} (ha : 1 ≤ a) (y : kˣ)
    (t : unitsModFiltration k a) :
    valuation k ((y : k) - (shellPt (n - a) t : k)) ≤ valuation k ((unifUnit k ^ n : kˣ) : k) ↔
      unifUnit k ^ (-(n - a)) * y ∈ unitsModCoset t := by
  set m : ℤ := n - a
  set u : kˣ := unifUnit k ^ (-m) * y
  set w : kˣ := unitsModRep t
  have hy' : y = unifUnit k ^ m * u := by
    simp only [u, ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  have hw0 : ord (w : k) = 0 := mem_unitFiltrationUnits_zero_iff_ord.1 (unitsModRep_mem t)
  have hdiff : (y : k) - (shellPt m t : k) = ((unifUnit k ^ m * w : kˣ) : k) * (((w⁻¹ * u : kˣ) : k) - 1) := by
    have hw : (w : k) ≠ 0 := w.ne_zero
    rw [hy', shellPt]
    push_cast
    field_simp
    rfl
  rw [val_le_iff_mem, ord_unifUnit_zpow, hdiff, mul_mem_valBall_iff, ord_units_mul, ord_unifUnit_zpow, hw0,
    mem_unitsModCoset, mem_unitFiltrationUnits_iff_valBall ha]
  constructor <;> intro h <;> convert h using 2 <;> simp [m]

open Classical in

theorem isShellReps {n : ℤ} {a : ℕ} (ha : 1 ≤ a) :
    GlobalTheory.LocLanglands.IsShellReps (unifUnit k ^ n) a
      (Finset.univ.image (shellPt (k := k) (n - a) (a := a))) := by
  classical
  have hc : GlobalTheory.SmGL.ord k (unifUnit k ^ n) = n := by rw [ord_eq, ord_unifUnit_zpow]
  refine ⟨fun r hr => ?_, fun y hy => ?_⟩
  · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hr
    rw [ord_eq, ord_shellPt, hc]
  · rw [hc, ord_eq] at hy
    set u : kˣ := unifUnit k ^ (-(n - a)) * y
    have hu0 : u ∈ unitFiltrationUnits k 0 := by
      rw [mem_unitFiltrationUnits_zero_iff_ord, ord_units_mul, ord_unifUnit_zpow, hy]
      ring
    refine ⟨shellPt (n - a) (QuotientGroup.mk ⟨u, hu0⟩ : unitsModFiltration k a),
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
        (shell_val_le_iff ha y _).2 (mem_unitsModCoset_mk hu0)⟩, ?_⟩
    rintro r ⟨hr, hv⟩
    obtain ⟨t', -, rfl⟩ := Finset.mem_image.1 hr
    rw [eq_of_mem_unitsModCoset ((shell_val_le_iff ha y t').1 hv) (mem_unitsModCoset_mk hu0)]

end Shell

end PositivityTheory.Pf1.LocalLanglands.KernelCondition.G7

end

noncomputable section

namespace PositivityTheory.Pf1.LocalLanglands.KernelCondition.G7

section Main

open ValuativeRel GroundTheory.LocalField

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

omit [MeasurableSpace k] [BorelSpace k] in

theorem real_factor (t : ℝ) (n : ℤ) :
    ((t / (residueCard k : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * (residueCard k : ℂ) ^ (-(n : ℂ) / 2) =
      ((t * (residueCard k : ℝ) ^ (-n) : ℝ) : ℂ) := by
  have hq : (0 : ℝ) < (residueCard k : ℝ) := residueCard_pos_real
  rw [show (residueCard k : ℂ) ^ (-(n : ℂ) / 2) = (((residueCard k : ℝ) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) by
    rw [Complex.ofReal_cpow hq.le]; push_cast; ring_nf]
  rw [← Complex.ofReal_mul]
  congr 1
  rw [div_eq_mul_inv, ← Real.rpow_neg hq.le, mul_assoc, ← Real.rpow_add hq, ← Real.rpow_intCast]
  congr 2
  push_cast
  ring

theorem main (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) (χ : kˣ →* ℂˣ)
    (hχ : GlobalTheory.SmGL.IsSmoothChar χ) (t : ℝ) :
    GlobalTheory.LocLanglands.IsTateMeas ψ t χ (((t / (selfDualMeasure ψ (valBall k 0 : Set k)).toReal : ℝ) : ℂ) *
      localEpsilon χ ψ 0) := by
  classical
  have hχc := continuous_of_isSmoothChar χ hχ
  have hvol : (selfDualMeasure ψ (valBall k 0 : Set k)).toReal =
      (residueCard k : ℝ) ^ ((addCharConductor ψ : ℝ) / 2) := selfDualMeasure_real_valBall_zero ψ
  rw [hvol]
  have hc := hasConductor ψ hψ h1
  by_cases hu : IsUnramifiedChar χ
  · have := GlobalTheory.LocLanglands.MeasModel.isTateMeas_of_isUnram hc (isUnram_of χ hu) t
    convert this using 1
    rw [localEpsilon_of_isUnramified hu, nabs_unif, map_zpow, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val,
      ← zpow_neg]
    have e : (residueCard k : ℂ) ^ ((addCharConductor ψ : ℂ) * (0 - 1 / 2)) =
        (residueCard k : ℂ) ^ (-(addCharConductor ψ : ℂ) / 2) := by congr 1; ring
    rw [e, ← real_factor]
    ring
  · have ha := hasExponent χ hχc
    have ha1 := quasiCharConductor_pos hχc hu
    refine ⟨_, _, _, hc, ha, isShellReps (n := addCharConductor ψ) ha1, ?_⟩
    rw [Finset.sum_image (fun x _ y _ h => shellPt_injective _ _ h), localEpsilon_eq_gaussSum hψ h1 hχc hu 0,
      nabs_unif]
    have e : (residueCard k : ℂ) ^ (((addCharConductor ψ - quasiCharConductor χ : ℤ) : ℂ) * 0 -
        (addCharConductor ψ : ℂ) / 2) = (residueCard k : ℂ) ^ (-(addCharConductor ψ : ℂ) / 2) := by
      congr 1; ring
    rw [e, ← mul_assoc, real_factor, GroundTheory.LocalField.gaussSum]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Units.val_inv_eq_inv_val]
    rfl

end Main

end PositivityTheory.Pf1.LocalLanglands.KernelCondition.G7

end

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.LocalLanglands.KernelCondition

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable [MeasurableSpace k] [BorelSpace k]

theorem isTateMeas_localEpsilon (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) (χ : kˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) (t : ℝ) (ht : 0 < t) :
    IsTateMeas ψ t χ (((t / (GroundTheory.LocalField.selfDualMeasure ψ (GroundTheory.LocalField.valBall k 0 : Set k)).toReal : ℝ) : ℂ) *
      GroundTheory.LocalField.localEpsilon χ ψ 0) :=
  G7.main ψ hψ h1 χ hχ t

end Local

end PositivityTheory.Pf1.LocalLanglands.KernelCondition
