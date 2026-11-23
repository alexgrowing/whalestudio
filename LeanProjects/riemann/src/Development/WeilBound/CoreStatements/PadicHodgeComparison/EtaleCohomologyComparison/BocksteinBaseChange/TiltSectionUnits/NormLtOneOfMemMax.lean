import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsUnitWitt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.TiltSectionUnits.ResAbs

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem norm_algebraMap_Zl (z : ℤ_[l]) : ‖((algebraMap ℤ_[l] K z : K) : PadicAlgCl l)‖ = ‖z‖ := by
  have h : ((algebraMap ℤ_[l] K z : K) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]) := rfl
  rw [h, PadicAlgCl.norm_extends, PadicInt.norm_def]

def zToOK : ℤ_[l] →+* OK l K :=
  (algebraMap ℤ_[l] K).codRestrict (OK l K) fun z => (mem_OK _).2 (by
    rw [norm_algebraMap_Zl]; exact PadicInt.norm_le_one z)

abbrev algZ : Algebra ℤ_[l] (OK l K) := (zToOK (K := K)).toAlgebra

attribute [local instance] algZ

theorem towZ : IsScalarTower ℤ_[l] (OK l K) K := by
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

attribute [local instance] towZ

theorem closZ : IsIntegralClosure (OK l K) ℤ_[l] K := by
  have key : ∀ x : K, x ∈ OK l K ↔ IsIntegral ℤ_[l] x := fun x => by
    rw [OK_eq, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  refine ⟨Subtype.coe_injective, fun {x} => ⟨fun hx => ⟨⟨x, (key x).2 hx⟩, rfl⟩, ?_⟩⟩
  rintro ⟨y, rfl⟩
  exact (key y).1 y.2

attribute [local instance] closZ

theorem norm_zToOK (z : ℤ_[l]) : ‖(((algebraMap ℤ_[l] (OK l K) z : OK l K) : K) : PadicAlgCl l)‖ = ‖z‖ := by
  exact norm_algebraMap_Zl z

variable [FiniteDimensional ℚ_[l] K]

theorem locZ : IsLocalHom (algebraMap ℤ_[l] (OK l K)) := by
  exact ⟨fun z hz => PadicInt.isUnit_iff.2 ((norm_zToOK z).symm.trans ((isUnit_OK_iff _).1 hz))⟩

attribute [local instance] locZ

theorem finZ : Module.Finite ℤ_[l] (OK l K) := by
  exact IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (OK l K)

attribute [local instance] finZ

theorem finite_res : Finite (IsLocalRing.ResidueField (OK l K)) := by
  have : Finite (IsLocalRing.ResidueField ℤ_[l]) := Finite.of_equiv _ PadicInt.residueField.symm.toEquiv
  exact Module.finite_of_finite (IsLocalRing.ResidueField ℤ_[l])

theorem l_mem_max : ((l : ℕ) : OK l K) ∈ IsLocalRing.maximalIdeal (OK l K) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_OK_iff]
  have h : ((((l : ℕ) : OK l K) : K) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]
  have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact (inv_lt_one_of_one_lt₀ h1).ne

instance charP_res : CharP (IsLocalRing.ResidueField (OK l K)) l :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 (by
    rw [← map_natCast (IsLocalRing.residue (OK l K)), IsLocalRing.residue_eq_zero_iff]
    exact l_mem_max)

instance perf_res : PerfectRing (IsLocalRing.ResidueField (OK l K)) l := by
  have := finite_res (l := l) (K := K)
  infer_instance

theorem mem_span_l_of_norm_le (w : OC l) (h : ‖(w : ℂ_[l])‖ ≤ ‖((l : ℕ) : ℂ_[l])‖) : w ∈ Ideal.span {((l : ℕ) : OC l)} := by
  have hl : ((l : ℕ) : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hmem : (w : ℂ_[l]) / (l : ℂ_[l]) ∈ GroundTheory.PAdicHodge.normInteger ℂ_[l] := by
    rw [GroundTheory.PAdicHodge.mem_normInteger, norm_div]
    exact div_le_one_of_le₀ h (norm_nonneg _)
  rw [Ideal.mem_span_singleton']
  refine ⟨⟨_, hmem⟩, ?_⟩
  apply Subtype.ext
  simp [hl]

theorem norm_okToOC (x : OK l K) : ‖((okToOC l K x : OC l) : ℂ_[l])‖ = ‖((x : K) : PadicAlgCl l)‖ := by
  exact PadicComplex.norm_extends l _

theorem norm_l_lt_one : ‖((l : ℕ) : ℂ_[l])‖ < 1 := by
  have h : ((l : ℕ) : ℂ_[l]) = ((algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) : PadicAlgCl l) : ℂ_[l]) := by
    simp
  rw [h, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem norm_lt_one_of_mem_max {m : OK l K} (hm : m ∈ IsLocalRing.maximalIdeal (OK l K)) :
    ‖((m : K) : PadicAlgCl l)‖ < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_OK_iff] at hm
  exact lt_of_le_of_ne (norm_OK_le m) hm

theorem exists_pow_mem_span : ∃ n : ℕ, ∀ y ∈ IsLocalRing.maximalIdeal (OK l K),
    okToOC l K y ^ l ^ n ∈ Ideal.span {((l : ℕ) : OC l)} := by
  haveI := OK_dvr (l := l) (K := K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OK l K)
  have h1 := norm_lt_one_of_irreducible hϖ
  have h0 : 0 < ‖((l : ℕ) : ℂ_[l])‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one h0 h1
  refine ⟨N, fun y hy => mem_span_l_of_norm_le _ ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hy
  obtain ⟨u, rfl⟩ := hy
  have hu : ‖((u : K) : PadicAlgCl l)‖ ≤ 1 := norm_OK_le u
  have key : ‖(((u * ϖ : OK l K) : K) : PadicAlgCl l)‖ ≤ ‖((ϖ : K) : PadicAlgCl l)‖ := by
    have e : (((u * ϖ : OK l K) : K) : PadicAlgCl l) = ((u : K) : PadicAlgCl l) * ((ϖ : K) : PadicAlgCl l) := by
      norm_cast
    rw [e, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hu
  calc ‖((okToOC l K (u * ϖ) ^ l ^ N : OC l) : ℂ_[l])‖
        = ‖((okToOC l K (u * ϖ) : OC l) : ℂ_[l])‖ ^ l ^ N := by
          rw [SubmonoidClass.coe_pow, norm_pow]
    _ = ‖(((u * ϖ : OK l K) : K) : PadicAlgCl l)‖ ^ l ^ N := by rw [norm_okToOC]
    _ ≤ ‖((ϖ : K) : PadicAlgCl l)‖ ^ l ^ N := pow_le_pow_left₀ (norm_nonneg _) key _
    _ ≤ ‖((ϖ : K) : PadicAlgCl l)‖ ^ N :=
          pow_le_pow_of_le_one (norm_nonneg _) h1.le (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
    _ ≤ ‖((l : ℕ) : ℂ_[l])‖ := hN.le

theorem resEx : ResEx := by
  intro l _ K _
  obtain ⟨n, hn⟩ := exists_pow_mem_span (l := l) (K := K)
  obtain ⟨s, hs⟩ := exists_tilt_section (p := l) (O := OC l) (R := OK l K) (okToOC l K) n hn
  refine ⟨⟨IsLocalRing.ResidueField (OK l K), IsLocalRing.residue (OK l K),
    IsLocalRing.residue_surjective, s, fun x => ?_⟩⟩
  obtain ⟨a, m, hm, h⟩ := hs x
  rw [h]
  have ha : ‖(a : ℂ_[l])‖ ≤ 1 := GroundTheory.PAdicHodge.mem_normInteger.1 a.2
  have hm' : ‖((okToOC l K m : OC l) : ℂ_[l])‖ < 1 := by
    rw [norm_okToOC]
    exact norm_lt_one_of_mem_max hm
  have hla : ‖((((l : ℕ) : OC l) * a : OC l) : ℂ_[l])‖ < 1 := by
    have e : ((((l : ℕ) : OC l) * a : OC l) : ℂ_[l]) = ((l : ℕ) : ℂ_[l]) * (a : ℂ_[l]) := by
      norm_cast
    rw [e, norm_mul]
    calc ‖((l : ℕ) : ℂ_[l])‖ * ‖(a : ℂ_[l])‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ * 1 :=
          mul_le_mul_of_nonneg_left ha (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact norm_l_lt_one
  have e2 : ((((l : ℕ) : OC l) * a + okToOC l K m : OC l) : ℂ_[l]) =
      ((((l : ℕ) : OC l) * a : OC l) : ℂ_[l]) + ((okToOC l K m : OC l) : ℂ_[l]) := by
    norm_cast
  rw [e2]
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hla hm')

end CrystallineSemistableComparison
