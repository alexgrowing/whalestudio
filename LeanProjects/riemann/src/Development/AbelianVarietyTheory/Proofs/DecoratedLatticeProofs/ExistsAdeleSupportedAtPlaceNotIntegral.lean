import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.FinPl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FinPl.NotIntAt

variable {D : D7}

def trAt (D : D7) (v : Pl D) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] Fv D.host.F v :=
  (evalV D.host.F v).toLinearMap ∘ₗ (TensorProduct.rid D.host.F (Af D.host.F)).toLinearMap ∘ₗ
    LinearMap.lTensor (Af D.host.F) (Algebra.trace D.host.F D.host.E)

theorem trAt_tmul (v : Pl D) (a : Af D.host.F) (x : D.host.E) :
    trAt D v (a ⊗ₜ[D.host.F] x) =
      algebraMap D.host.F (Fv D.host.F v) (Algebra.trace D.host.F D.host.E x) * evalV D.host.F v a := by
  simp [trAt, Algebra.smul_def]

theorem algebraMap_int_mem (v : Pl D) (r : 𝓞 D.host.F) :
    algebraMap D.host.F (Fv D.host.F v) (r : D.host.F) ∈ v.adicCompletionIntegers D.host.F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (r : D.host.F)
  erw [this]
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact v.intValuation_le_one r

theorem trAt_int (v : Pl D) {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    trAt D v y ∈ v.adicCompletionIntegers D.host.F := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have hle : intAE D ≤ (v.adicCompletionIntegers D.host.F).toSubring.toAddSubgroup.comap
      (trAt D v).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, rfl⟩
    change trAt D v (a ⊗ₜ[D.host.F] (x : D.host.E)) ∈ v.adicCompletionIntegers D.host.F
    rw [trAt_tmul]
    have hint : IsIntegral ℤ (Algebra.trace D.host.F D.host.E (x : D.host.E)) :=
      Algebra.isIntegral_trace x.isIntegral_coe
    exact mul_mem (algebraMap_int_mem v ⟨_, hint⟩) (ha v)
  exact hle hy

theorem evalV_single_same (v : Pl D) (y : Fv D.host.F v) : evalV D.host.F v (singleV D.host.F v y) = y := by
  classical
  exact RestrictedProduct.single_eq_same (fun w : Pl D => w.adicCompletionIntegers D.host.F) v y

theorem evalV_single_ne (v : Pl D) (y : Fv D.host.F v) {w : Pl D} (hw : w ≠ v) :
    evalV D.host.F w (singleV D.host.F v y) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne (fun w : Pl D => w.adicCompletionIntegers D.host.F) y hw

theorem inv_not_mem (v : Pl D) {π : 𝓞 D.host.F} (hπ : π ∈ v.asIdeal) (hπ0 : π ≠ 0) :
    (algebraMap D.host.F (Fv D.host.F v) (π : D.host.F))⁻¹ ∉ v.adicCompletionIntegers D.host.F := by
  intro h
  have hv : Valued.v (algebraMap D.host.F (Fv D.host.F v) (π : D.host.F)) < 1 := by
    have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (π : D.host.F)
    erw [this]
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_lt_one_iff_mem π).2 hπ
  have hne : algebraMap D.host.F (Fv D.host.F v) (π : D.host.F) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hπ0
  have h1 : Valued.v ((algebraMap D.host.F (Fv D.host.F v) (π : D.host.F)) *
      (algebraMap D.host.F (Fv D.host.F v) (π : D.host.F))⁻¹) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h)) hv
  rw [mul_inv_cancel₀ hne, map_one] at h1
  exact lt_irrefl _ h1

theorem exists_not_intAt : ∀ (D : D7) (v : Pl D), ∃ u ∈ idAt D (· = v), u ∉ intAt D (· = v) := by
  intro D v
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  set n : ℕ := Module.finrank D.host.F D.host.E
  have hn : (n : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  set c : Fv D.host.F v := (algebraMap D.host.F (Fv D.host.F v) ((n : D.host.F) * (π : D.host.F)))⁻¹
  refine ⟨pairA D.host.F 0 (singleV D.host.F v c) ⊗ₜ[D.host.F] (1 : D.host.E),
    GlobalTheory.FinPl.LatMem.tmul_mem_idAt (P := (· = v))
      (fun w hw => evalV_single_ne v c hw) 1, fun h => ?_⟩
  have h2 := trAt_int v h.2
  change trAt D v (singleV D.host.F v c ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ _ at h2
  have htr : Algebra.trace D.host.F D.host.E 1 = (n : D.host.F) := by
    simpa using Algebra.trace_algebraMap (R := D.host.F) (S := D.host.E) 1
  rw [trAt_tmul, evalV_single_same, htr] at h2
  have e : algebraMap D.host.F (Fv D.host.F v) (n : D.host.F) * c =
      (algebraMap D.host.F (Fv D.host.F v) (π : D.host.F))⁻¹ := by
    simp only [c, map_mul, map_natCast, mul_inv, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  rw [e] at h2
  exact inv_not_mem v hπ hπ0 h2

end GlobalTheory.FinPl.NotIntAt
