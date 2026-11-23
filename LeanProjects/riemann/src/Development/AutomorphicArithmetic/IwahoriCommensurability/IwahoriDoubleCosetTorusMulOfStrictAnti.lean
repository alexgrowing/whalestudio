import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetTorusNilpotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAddCharConductorMaxIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeedOrbKVanish

open Formalism.UG

namespace UpperTheory.IwMul

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem upper_entries {ϖ : kˣ} (hϖ : ord k ϖ = 1) {ν : Fin n → ℤ} (hν : StrictAnti ν)
    {c : GL (Fin n) k} (hc : c ∈ iwahori k (Fin n) ⊓ unipB k (Fin n)) (i j : Fin n) :
    valuation k (((tor ϖ ν * c * (tor ϖ ν)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ 1 ∧
      (j < i → valuation k (((tor ϖ ν * c * (tor ϖ ν)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) < 1) := by
  have hconj : tor ϖ ν * c * (tor ϖ ν)⁻¹ = (tor ϖ (fun i => -ν i))⁻¹ * c * tor ϖ (fun i => -ν i) := by
    rw [DCoset.tor_inv ϖ (fun i => -ν i), DCoset.tor_inv ϖ ν]
    simp only [neg_neg]
  rw [hconj, DCoset.conj_apply]
  obtain ⟨hc1, hc2⟩ := hc
  have hint := ((GlobalTheory.SplitFlip.mem_KO_iff c).mp (mem_iwahori.mp hc1).1).1 i j
  have hup := (mem_unipB k).mp hc2
  rcases lt_or_ge j i with hji | hij
  · rw [hup.1 i j hji]
    simp
  · refine ⟨?_, fun h => absurd h (not_lt.mpr hij)⟩
    rw [map_mul]
    have hpow : valuation k ((ϖ ^ (-ν j - -ν i) : kˣ) : k) ≤ 1 := by
      rcases hij.lt_or_eq with hlt | heq
      · exact (DCoset.val_zpow_lt_one hϖ (by have := hν hlt; omega)).le
      · subst heq
        simp
    exact mul_le_one' hpow hint

private theorem upper_conj_mem {ϖ : kˣ} (hϖ : ord k ϖ = 1) {ν : Fin n → ℤ} (hν : StrictAnti ν)
    {c : GL (Fin n) k} (hc : c ∈ iwahori k (Fin n) ⊓ unipB k (Fin n)) :
    tor ϖ ν * c * (tor ϖ ν)⁻¹ ∈ iwahori k (Fin n) := by
  refine mem_iwahori.2 ⟨(GlobalTheory.SplitFlip.mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩,
    fun i j hij => (upper_entries hϖ hν hc i j).2 hij⟩
  · exact (Valuation.mem_integer_iff _ _).2 (upper_entries hϖ hν hc i j).1
  · have e : (tor ϖ ν * c * (tor ϖ ν)⁻¹)⁻¹ = tor ϖ ν * c⁻¹ * (tor ϖ ν)⁻¹ := by group
    rw [e]
    exact (Valuation.mem_integer_iff _ _).2 (upper_entries hϖ hν (inv_mem hc) i j).1

private theorem lower_conj_mem {ϖ : kˣ} (hϖ : ord k ϖ = 1) {ν : Fin n → ℤ} (hν : StrictAnti ν)
    {l : GL (Fin n) k} (hl : l ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n)) (m : ℕ) :
    (GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν ^ m)⁻¹ * l * GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν ^ m ∈
      iwahori k (Fin n) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using hl.1
  · rw [GlobalTheory.TorusElementPower.torusElt_pow_eq]
    have hν' : StrictAnti (fun i : Fin n => (m : ℤ) * ν i) := by
      intro i j hij
      exact mul_lt_mul_of_pos_left (hν hij) (by exact_mod_cast hm)
    exact DCoset.conj_mem_iwahori hϖ hν' hl

end UpperTheory.IwMul

theorem UpperTheory.iwahori_doubleCoset_torus_mul_of_strictAnti :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), ValuativeRel.valuation k (ϖ : k) = ValuativeRel.uniformizer k → ∀ ν : Fin n → ℤ, StrictAnti ν → ∀ m : ℕ, ∀ a ∈ DoubleCoset.doubleCoset (GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)), ∀ b ∈ DoubleCoset.doubleCoset (GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν ^ m) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)), a * b ∈ DoubleCoset.doubleCoset (GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν ^ (m + 1)) (GlobalTheory.SmGL.iwahori k (Fin n) : Set (GL (Fin n) k)) (GlobalTheory.SmGL.iwahori k (Fin n)) := by
  intro k _ _ _ _ n ϖ hϖu ν hν m a ha b hb
  have hϖ := GlobalTheory.DZero.PsiM.ord_eq_one hϖu
  have htt : GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν = GlobalTheory.CompanionTheory.IwJac.tor ϖ ν := rfl
  obtain ⟨i1, hi1, i2, hi2, rfl⟩ := DoubleCoset.mem_doubleCoset.mp ha
  obtain ⟨i3, hi3, i4, hi4, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hb
  have hx : i2 * i3 ∈ GlobalTheory.SmGL.iwahori k (Fin n) := mul_mem hi2 hi3
  obtain ⟨c, hc, d, hd, l, hl, hcdl⟩ := GlobalTheory.CompanionTheory.IwahoriDatumGL.fact_up' k n hx
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hd.2
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨i1 * (GlobalTheory.CompanionTheory.IwJac.tor ϖ ν * c * (GlobalTheory.CompanionTheory.IwJac.tor ϖ ν)⁻¹) * d,
    mul_mem (mul_mem hi1 (UpperTheory.IwMul.upper_conj_mem hϖ hν hc)) hd.1,
    (GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν ^ m)⁻¹ * l * GlobalTheory.GLDoubling.torusElt k (Fin n) ϖ ν ^ m * i4,
    mul_mem (UpperTheory.IwMul.lower_conj_mem hϖ hν hl m) hi4, ?_⟩
  rw [htt, ← hs, ← GlobalTheory.CompanionTheory.IwJac.DCoset.diagT_conj_tor ϖ ν s, hs]
  have h2 : i2 = c * d * l * i3⁻¹ := by
    rw [← hcdl]
    group
  subst h2
  group
