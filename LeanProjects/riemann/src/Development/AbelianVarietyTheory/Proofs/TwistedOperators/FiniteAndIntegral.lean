import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

set_option autoImplicit false

noncomputable section

open IsDedekindDomain IsLocalRing Formalism.L2.Pj

namespace GlobalTheory.CompleteValExt

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem exists_algebraMap_eq_iff (x : K) : (∃ a : V, algebraMap V K a = x) ↔ 0 ≤ vV V x := by
  by_cases hx : x = 0
  · subst hx
    exact ⟨fun _ => by simp [vV], fun _ => ⟨0, map_zero _⟩⟩
  have h1 := WithZero.log_le_log (valV_ne_zero (V := V) hx) one_ne_zero
  rw [WithZero.log_one] at h1
  have h2 : 0 ≤ vV V x ↔ valV V x ≤ 1 := by
    rw [← h1]
    unfold vV
    omega
  rw [h2]
  refine ⟨?_, fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K) h⟩
  rintro ⟨a, rfl⟩
  exact HeightOneSpectrum.valuation_le_one _ a

variable {W L : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
  [IsFractionRing W L]

theorem finite_and_integral_of_scale [IsAdicComplete (maximalIdeal V) V] (i : K →+* L) {r : ℕ} (hr : 0 < r)
    (hi : ∀ z, vV W (i z) = (r : ℤ) * vV V z) (h' : Finite (ResidueField W)) :
    i.Finite ∧ ∀ b : W, (i.comp (algebraMap V K)).IsIntegralElem (algebraMap W L b) := by
  have hint : ∀ a : V, ∃ v : W, algebraMap W L v = i (algebraMap V K a) := fun a =>
    (exists_algebraMap_eq_iff _).2 (by
      rw [hi]; exact mul_nonneg (by positivity) ((exists_algebraMap_eq_iff _).1 ⟨a, rfl⟩))
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective W L
  let g : V →+* W :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap W L (g a) = i (algebraMap V K a) := hg0
  letI : Algebra V W := g.toAlgebra
  letI : Algebra K L := i.toAlgebra
  letI : Algebra V L := (i.comp (algebraMap V K)).toAlgebra
  have : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq fun a => (hg a).symm
  have : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hgi : Function.Injective (algebraMap V W) := fun a b hab => by
    apply IsFractionRing.injective V K
    apply i.injective
    rw [← hg, ← hg]
    exact congrArg _ hab
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hgi
  have hle : (maximalIdeal V).map (algebraMap V W) ≤ maximalIdeal W := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, mem_maximalIdeal]
    intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb' : i (algebraMap V K a) * algebraMap W L b = 1 := by
      rw [← hg, ← map_mul, ← map_one (algebraMap W L)]
      exact congrArg _ hb
    have h0 : algebraMap V K a ≠ 0 := fun h => by
      rw [h, map_zero, zero_mul] at hb'
      exact zero_ne_one hb'
    have h1 : algebraMap W L b = i (algebraMap V K a)⁻¹ := by
      rw [map_inv₀]
      exact eq_inv_of_mul_eq_one_right hb'
    have h2 := (exists_algebraMap_eq_iff (V := W) _).1 ⟨b, h1⟩
    rw [hi] at h2
    obtain ⟨c, hc⟩ := (exists_algebraMap_eq_iff (V := V) _).2
      (nonneg_of_mul_nonneg_right h2 (by exact_mod_cast hr))
    refine (mem_maximalIdeal a).1 ha (IsUnit.of_mul_eq_one c (IsFractionRing.injective V K ?_))
    rw [map_mul, hc, map_one, mul_inv_cancel₀ h0]
  have hne : (maximalIdeal V).map (algebraMap V W) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hgi]
    exact IsDiscreteValuationRing.not_a_field V
  have htop : (maximalIdeal V).map (algebraMap V W) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal W).ne_top hle
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have : Finite (W ⧸ maximalIdeal W) := h'
  have : Module.Finite V W := GlobalTheory.finite_of_forall_prime_mem hϖ.ne_zero (fun P hP h0 => by
    rw [eq_maximalIdeal (hP.isMaximal h0)]
    exact hϖ.not_isUnit) hne htop
  refine ⟨Module.Finite.of_isLocalization V W (nonZeroDivisors V), fun b => ?_⟩
  exact (Algebra.IsIntegral.isIntegral (R := V) b).algebraMap (B := L)

theorem finite_and_integral : ∀ (T T' : CDVR) (i : T.Fr →+* T'.Fr) (r : ℕ), 0 < r →
    (∀ a : T.Fr, vV T'.V (i a) = (r : ℤ) * vV T.V a) → T'.FinRes →
    i.Finite ∧ ∀ b : T'.V, (i.comp (algebraMap T.V T.Fr)).IsIntegralElem (algebraMap T'.V T'.Fr b) :=
  fun T T' i _ hr hi h' => finite_and_integral_of_scale (V := T.V) (W := T'.V) i hr hi h'

end GlobalTheory.CompleteValExt
