import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockStepBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChangeOfLatticeNested
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Module

noncomputable section

namespace TwoBlockStepBound

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem relIndex_le_pow {H K : Submodule ℤ Ω} [Module.Finite ℤ K] {N : ℕ} (hN : 0 < N)
    (hNK : ∀ u ∈ K, (N : Ω) * u ∈ H) :
    H.toAddSubgroup.relIndex K.toAddSubgroup ≠ 0 ∧
      H.toAddSubgroup.relIndex K.toAddSubgroup ≤ N ^ finrank ℤ K := by
  have : Module.Finite ℤ (AddSubgroup.toIntSubmodule K.toAddSubgroup) := ‹Module.Finite ℤ K›
  have : Module.Free ℤ (AddSubgroup.toIntSubmodule K.toAddSubgroup) := Module.free_of_finite_type_torsion_free'
  have key := AddSubgroup.relIndex_map_nsmul N K.toAddSubgroup
  have hsub : K.toAddSubgroup.map (nsmulAddMonoidHom (α := Ω) N) ≤ H.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [nsmul_eq_mul] using hNK y hy
  have hne : (K.toAddSubgroup.map (nsmulAddMonoidHom (α := Ω) N)).relIndex K.toAddSubgroup ≠ 0 := by
    rw [key]
    exact pow_ne_zero _ hN.ne'
  refine ⟨fun h0 => hne (AddSubgroup.relIndex_eq_zero_of_le_left hsub h0), ?_⟩
  calc H.toAddSubgroup.relIndex K.toAddSubgroup ≤ _ := AddSubgroup.relIndex_le_of_le_left hsub hne
    _ = N ^ finrank ℤ K := key

theorem pow_mul_mem_sec {x x' : Ix κ → Ω} {M : ℕ} (hM : ∀ s ∈ sec ℤ x' 1, (M : Ω) * s ∈ sec ℤ x 1) :
    ∀ n : ℕ, ∀ s ∈ sec ℤ x' n, (M : Ω) ^ n * s ∈ sec ℤ x n
  | 0, s, hs => by
    rw [sec_zero'] at hs ⊢
    simpa using hs
  | n + 1, s, hs => by
    rw [← sec_mul_sec] at hs ⊢
    induction hs using Submodule.mul_induction_on' with
    | mem_mul_mem u hu v hv =>
      have := Submodule.mul_mem_mul (pow_mul_mem_sec hM n u hu) (hM v hv)
      convert this using 1
      ring
    | add u _ v _ hu hv =>
      rw [mul_add]
      exact add_mem hu hv

theorem exists_finrank_sec_le (hRank : RankOfSections.Statement) {x : Ix κ → Ω} {D : ℕ}
    (hX : IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ m : ℕ, 1 ≤ m → (finrank ℤ (sec ℤ x m) : ℝ) ≤ R * (m : ℝ) ^ D := by
  obtain ⟨hqP, hqd⟩ := GenericFibre.proof Ω κ x D hX
  obtain ⟨C, hC⟩ := hRank κ _ D hqP hqd
  set δ : ℝ := (GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ
    ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ : Fin D => fun _ => (1 : ℤ)) : ℝ)
  refine ⟨|δ| + |C| * 2 ^ D, by positivity, fun m hm => ?_⟩
  have e : (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
      ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (m : ℤ)) : ℝ) =
      (finrank ℤ (sec ℤ x m) : ℝ) := by exact_mod_cast SectionsRank.proof Ω κ x m
  have h := (abs_le.mp (hC m)).2
  rw [e] at h
  have ht : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (0 : ℝ) ≤ (m : ℝ) ^ D := by positivity
  have h1 : ((m : ℝ) + 1) ^ ((D : ℝ) - 1) ≤ ((m : ℝ) + 1) ^ D := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : ((m : ℝ) + 1) ^ D ≤ 2 ^ D * (m : ℝ) ^ D := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) D
  have h3 : δ * (m : ℝ) ^ D / D.factorial ≤ |δ| * (m : ℝ) ^ D := by
    have hf : (1 : ℝ) ≤ D.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero D)
    rw [div_le_iff₀ (by linarith)]
    calc δ * (m : ℝ) ^ D ≤ |δ| * (m : ℝ) ^ D := mul_le_mul_of_nonneg_right (le_abs_self δ) hp
      _ ≤ |δ| * (m : ℝ) ^ D * D.factorial := le_mul_of_one_le_right (by positivity) hf
  have h4 : C * ((m : ℝ) + 1) ^ ((D : ℝ) - 1) ≤ |C| * (2 ^ D * (m : ℝ) ^ D) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg C))
  nlinarith

end TwoBlockStepBound

open TwoBlockStepBound in

theorem TwoBlockStepBound.proof (hRank : RankOfSections.Statement) : TwoBlockStepBound.Statement := by
  intro D Ω _ _ κ _ x B hX _ _ hsp
  set x' := matAct B x
  obtain ⟨M, hM0, hM⟩ := ChangeOfLatticeNested.exists_mul_mem_sec_one x B
  obtain ⟨R, hR0, hR⟩ := exists_finrank_sec_le hRank hX
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM0)
  refine ⟨R * Real.log M, fun a b => ?_⟩
  have hsp1 : sec ℤ x 1 ≤ sec ℤ x' 1 := by
    rw [sec_one', sec_one']
    exact hsp
  have eH : sec ℤ x (a + 1) * sec ℤ x' b = sec ℤ x a * sec ℤ x' b * sec ℤ x 1 := by
    rw [← sec_mul_sec x a 1, mul_right_comm]
  have eK : sec ℤ x a * sec ℤ x' (b + 1) = sec ℤ x a * sec ℤ x' b * sec ℤ x' 1 := by
    rw [← sec_mul_sec x' b 1, mul_assoc]
  have hKQ : sec ℤ x a * sec ℤ x' (b + 1) ≤ sec ℤ x' (a + b + 1) := by
    rw [add_assoc, ← sec_mul_sec x' a (b + 1)]
    exact mul_le_mul' (ChangeOfLattice.sec_mono hsp a) le_rfl
  have : Module.Finite ℤ (sec ℤ x a * sec ℤ x' (b + 1)) :=
    Module.Finite.iff_fg.mpr ((sec_fg x a).mul (sec_fg x' (b + 1)))
  obtain ⟨hne, hle⟩ := relIndex_le_pow (H := sec ℤ x (a + 1) * sec ℤ x' b)
    (K := sec ℤ x a * sec ℤ x' (b + 1)) hM0 (by rw [eH, eK]; exact mul_mem_of_forall hM _)
  have hMn : ((M : Ω) ^ (a + b + 1)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hM0.ne')
  let f := (LinearMap.mulLeft ℤ ((M : Ω) ^ (a + b + 1))).restrict (pow_mul_mem_sec hM (a + b + 1))
  have hf : Function.Injective f := fun s t hst =>
    Subtype.ext (mul_left_cancel₀ hMn (congrArg Subtype.val hst))
  have hrk : finrank ℤ (sec ℤ x a * sec ℤ x' (b + 1)) ≤ finrank ℤ (sec ℤ x (a + b + 1)) :=
    (Submodule.finrank_mono hKQ).trans (LinearMap.finrank_le_finrank_of_injective hf)
  have hpos : (0 : ℝ) ≤ twoBlockStep x x' a b :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne)
  have ht : ((a + b : ℝ) + 1) = ((a + b + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [abs_of_nonneg hpos, ht]
  unfold twoBlockStep
  calc Real.log ((sec ℤ x (a + 1) * sec ℤ x' b).toAddSubgroup.relIndex (sec ℤ x a * sec ℤ x' (b + 1)).toAddSubgroup)
      ≤ Real.log ((M ^ finrank ℤ (sec ℤ x a * sec ℤ x' (b + 1)) : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hne) (by exact_mod_cast hle)
    _ = finrank ℤ (sec ℤ x a * sec ℤ x' (b + 1)) * Real.log M := by
        push_cast
        rw [Real.log_pow]
    _ ≤ finrank ℤ (sec ℤ x (a + b + 1)) * Real.log M :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hrk) hlogM
    _ ≤ R * ((a + b + 1 : ℕ) : ℝ) ^ D * Real.log M :=
        mul_le_mul_of_nonneg_right (hR _ (by omega)) hlogM
    _ = R * Real.log M * ((a + b + 1 : ℕ) : ℝ) ^ D := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
