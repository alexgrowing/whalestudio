import Mathlib
import GroundTheory.PAdicHodge.PerfectoidField
import GroundTheory.PAdicHodge.TiltValuation
import GroundTheory.PAdicHodge.TiltField
import GroundTheory.PAdicHodge.KerTheta
import GroundTheory.PAdicHodge.TiltMap
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section Functor

variable {K L M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [NontriviallyNormedField M] [IsUltrametricDist M]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
  [IsPerfectoidField M p]
omit [IsUltrametricDist K] [IsUltrametricDist L] [IsUltrametricDist M] in
theorem norm_comp_eq {φ : K →+* L} (hφ : ∀ x, ‖φ x‖ = ‖x‖) {ψ : L →+* M}
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (x : K) : ‖(ψ.comp φ) x‖ = ‖x‖ := by
  rw [RingHom.comp_apply, hψ, hφ]

variable (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (ψ : L →+* M) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)

theorem preTiltMap_comp :
    preTiltMap p (ψ.comp φ) (norm_comp_eq hφ hψ) =
      (preTiltMap p ψ hψ).comp (preTiltMap p φ hφ) := by
  refine RingHom.ext fun x => Perfection.ext fun n => ?_
  rw [RingHom.comp_apply, coeff_preTiltMap, coeff_preTiltMap, coeff_preTiltMap]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (Perfection.coeff (ModP (normInteger K) p) p n x)
  rw [← ha, modPMap_mk, modPMap_mk, modPMap_mk]
  rfl

theorem tiltMap_comp :
    tiltMap p (ψ.comp φ) (norm_comp_eq hφ hψ) = (tiltMap p ψ hψ).comp (tiltMap p φ hφ) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (PreTilt (normInteger K) p)) ?_
  ext a
  simp only [RingHom.comp_apply, tiltMap_algebraMap]
  rw [preTiltMap_comp φ hφ ψ hψ]
  rfl

end Functor

section Density

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]

omit [IsUltrametricDist K] in

theorem exists_norm_mem_Ioc_of_dense (hnd : ∀ r : ℝ, r < 1 → ∃ x : K, r < ‖x‖ ∧ ‖x‖ < 1)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) : ∃ x : K, a < ‖x‖ ∧ ‖x‖ ≤ b := by
  have hb : 0 < b := ha.trans hab
  obtain ⟨z, hz1, hz2⟩ := hnd (a / b) ((div_lt_one hb).2 hab)
  have hz0 : 0 < ‖z‖ := (div_pos ha hb).trans hz1
  obtain ⟨y, hy⟩ := NormedField.exists_lt_norm K b
  have hex : ∃ m : ℕ, ‖y * z ^ m‖ ≤ b := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hb (hb.trans hy)) hz2
    refine ⟨m, ?_⟩
    rw [norm_mul, norm_pow]
    have hy0 : 0 < ‖y‖ := hb.trans hy
    calc ‖y‖ * ‖z‖ ^ m ≤ ‖y‖ * (b / ‖y‖) := by gcongr
      _ = b := by field_simp
  classical
  set m := Nat.find hex with hmdef
  have hm : ‖y * z ^ m‖ ≤ b := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, pow_zero, mul_one] at hm
    exact (lt_irrefl _) (hy.trans_le hm)
  have hprev : b < ‖y * z ^ (m - 1)‖ := by
    have := Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
    exact not_le.1 this
  refine ⟨y * z ^ m, ?_, hm⟩
  have e : m = m - 1 + 1 := by omega
  rw [e, pow_succ, ← mul_assoc, norm_mul]
  calc a = b * (a / b) := by field_simp
    _ < ‖y * z ^ (m - 1)‖ * ‖z‖ := by
      apply mul_lt_mul hprev hz1.le (div_pos ha hb) (norm_nonneg _)

theorem exists_norm_mem_Ioc (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ x : K, a < ‖x‖ ∧ ‖x‖ ≤ b :=
  exists_norm_mem_Ioc_of_dense (IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p)) ha hab

theorem norm_untilt_sum_sub_le {ι : Type*} (s : Finset ι) (x : ι → PreTilt (normInteger K) p) :
    ‖(((∑ i ∈ s, x i).untilt : normInteger K) : K) - ∑ i ∈ s, ((x i).untilt : K)‖ ≤
      ‖(p : K)‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have h1 := norm_untilt_add_sub_le (x j) (∑ i ∈ s, x i)
    have e : (((x j + ∑ i ∈ s, x i).untilt : normInteger K) : K) -
        (((x j).untilt : K) + ∑ i ∈ s, ((x i).untilt : K)) =
        ((((x j + ∑ i ∈ s, x i).untilt : normInteger K) : K) -
          (((x j).untilt + (∑ i ∈ s, x i).untilt : normInteger K) : K)) +
        ((((∑ i ∈ s, x i).untilt : normInteger K) : K) - ∑ i ∈ s, ((x i).untilt : K)) := by
      push_cast; ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ih)

end Density

section Algebra

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p

instance tiltAlgebra : Algebra K♭ C♭ :=
  (tiltMap p (algebraMap K C) (norm_algebraMap' C)).toAlgebra

theorem algebraMap_tilt_eq :
    algebraMap K♭ C♭ = tiltMap p (algebraMap K C) (norm_algebraMap' C) :=
  rfl

theorem norm_algebraMap_tilt (x : K♭) : ‖algebraMap K♭ C♭ x‖ = ‖x‖ :=
  norm_tiltMap _ _ x

theorem tiltSharp_algebraMap_tilt (x : K♭) :
    tiltSharp C p (algebraMap K♭ C♭ x) = algebraMap K C (tiltSharp K p x) :=
  tiltSharp_tiltMap _ _ x

instance tiltNormedAlgebra : NormedAlgebra K♭ C♭ where
  norm_smul_le r x := by
    rw [Algebra.smul_def, norm_mul, norm_algebraMap_tilt]

end Algebra

section IntermediateField

variable {K C : Type*} [NontriviallyNormedField K] [NormedField C] [NormedAlgebra K C]

instance (F : IntermediateField K C) : NontriviallyNormedField F where
  __ := (inferInstance : NormedField F)
  non_trivial := by
    obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
    refine ⟨algebraMap K F c, ?_⟩
    change 1 < ‖((algebraMap K F c : F) : C)‖
    rw [IntermediateField.coe_algebraMap_apply, norm_algebraMap']
    exact hc

theorem IntermediateField.norm_coe (F : IntermediateField K C) (x : F) : ‖(x : C)‖ = ‖x‖ :=
  rfl

end IntermediateField

section TiltIntermediate

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p

variable (F : IntermediateField K C) [IsPerfectoidField F p]

local notation "F♭" => Tilt F NormedField.valuation (normInteger F) normInteger_integers p

omit [IsUltrametricDist K] [IsUltrametricDist C] in
theorem norm_val (x : F) : ‖(F.val : F →+* C) x‖ = ‖x‖ := rfl

variable (p) in

def tiltInclusion : F♭ →+* C♭ :=
  tiltMap p (F.val : F →+* C) (norm_val F)

theorem algebraMap_tilt_eq_comp :
    algebraMap K♭ C♭ = (tiltInclusion p F).comp
      (tiltMap p (algebraMap K F) (norm_algebraMap' F)) := by
  rw [algebraMap_tilt_eq, tiltInclusion, ← tiltMap_comp]
  rfl

variable (p) in

def tiltIntermediateField : IntermediateField K♭ C♭ where
  carrier := (tiltInclusion p F).fieldRange
  mul_mem' ha hb := Subfield.mul_mem _ ha hb
  add_mem' ha hb := Subfield.add_mem _ ha hb
  inv_mem' _ hx := Subfield.inv_mem _ hx
  algebraMap_mem' x := by
    rw [algebraMap_tilt_eq_comp F]
    exact ⟨_, rfl⟩

theorem mem_tiltIntermediateField {z : C♭} :
    z ∈ tiltIntermediateField p F ↔ ∃ y : F♭, tiltInclusion p F y = z :=
  RingHom.mem_fieldRange

theorem tiltSharp_mem_of_mem_tiltIntermediateField {z : C♭}
    (hz : z ∈ tiltIntermediateField p F) : tiltSharp C p z ∈ F := by
  obtain ⟨y, rfl⟩ := hz
  rw [tiltInclusion, tiltSharp_tiltMap]
  exact (tiltSharp F p y).2

theorem algebraMap_mem_tiltIntermediateField {a : 𝒪C♭}
    (ha : ∀ n, ((PreTilt.untilt ((frobeniusEquiv 𝒪C♭ p).symm^[n] a) : normInteger C) : C) ∈ F) :
    algebraMap 𝒪C♭ C♭ a ∈ tiltIntermediateField p F := by
  let y : ℕ → normInteger F := fun n =>
    ⟨⟨_, ha n⟩, mem_normInteger.2 (mem_normInteger.1
      (PreTilt.untilt ((frobeniusEquiv 𝒪C♭ p).symm^[n] a)).2)⟩
  have hy : ∀ n, y (n + 1) ^ p = y n := fun n => by
    apply Subtype.ext; apply Subtype.ext
    change ((PreTilt.untilt ((frobeniusEquiv 𝒪C♭ p).symm^[n + 1] a) : normInteger C) : C) ^ p = _
    rw [← SubmonoidClass.coe_pow, IsPerfectoidField.untilt_iterate_succ_pow]
  refine ⟨algebraMap _ _ (IsPerfectoidField.ofCompatible p y hy), ?_⟩
  rw [tiltInclusion, tiltMap_algebraMap]
  congr 1
  refine IsPerfectoidField.preTilt_ext p fun n => ?_
  change Perfection.coeff (ModP (normInteger C) p) p n (preTiltMap p _ _ _) = _
  rw [coeff_preTiltMap]
  change modPMap _ _ (Ideal.Quotient.mk _ (y n)) = _
  rw [modPMap_mk, ← IsPerfectoidField.mk_untilt_iterate]
  rfl

end TiltIntermediate

end GroundTheory.PAdicHodge
