import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt

noncomputable section

open Module Polynomial
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne

namespace GlobalTheory.LocalInv

theorem pow_finrank_eq_zero_of_isNilpotent {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {N : End ℂ V} (hN : IsNilpotent N) : N ^ finrank ℂ V = 0 := by
  obtain ⟨m, hm⟩ := hN
  have h := Module.End.ker_pow_le_ker_pow_finrank N m
  rw [hm, LinearMap.ker_zero] at h
  exact LinearMap.ker_eq_top.mp (top_le_iff.mp h)

theorem norm_le_of_isPurePair {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {q : ℝ} (hq : 1 < q) {f N : End ℂ V} (hN : IsNilpotent N) (hp : IsPurePair q f N) {α : ℂ}
    (hα : f.HasEigenvalue α) :
    q ^ (-(((finrank ℂ V : ℝ) - 1) / 2)) ≤ ‖α‖ ∧ ‖α‖ ≤ q ^ (((finrank ℂ V : ℝ) - 1) / 2) := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  have hmem : ∀ r : ℝ, ‖α‖ = r → v ∈ absSpace f r := fun r hr =>
    Submodule.mem_iSup_of_mem α (Submodule.mem_iSup_of_mem hr hv.1)

  obtain ⟨i, hi⟩ : ∃ i : ℤ, ‖α‖ = q ^ ((i : ℝ) / 2) := by
    by_contra hc
    push_neg at hc
    have hle : (⨆ i : ℤ, absSpace f (q ^ ((i : ℝ) / 2))) ≤ ⨆ (β : ℂ) (_ : β ≠ α), f.eigenspace β := by
      refine iSup_le fun i => iSup₂_le fun β hβ => le_iSup₂_of_le β (fun h => hc i (h ▸ hβ)) le_rfl
    rw [hp.1] at hle
    have hd := (f.eigenspaces_iSupIndep α)
    have hv0 : v ∈ (⨆ (β : ℂ) (_ : β ≠ α), f.eigenspace β) := hle Submodule.mem_top
    exact hv.2 ((Submodule.disjoint_def.mp hd) v hv.1 hv0)

  set j := i.natAbs with hj
  have hNj : N ^ j ≠ 0 := by
    intro h0
    rcases le_or_gt 0 i with h | h
    · have hij : (i : ℝ) = (j : ℝ) := by
        rw [hj, Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast h)]
      obtain ⟨u, -, hu⟩ := (hp.2 j).surjOn (hmem _ (by rw [hi, hij]))
      rw [h0, LinearMap.zero_apply] at hu
      exact hv.2 hu.symm
    · have hij : (i : ℝ) / 2 = -(j : ℝ) / 2 := by
        rw [hj, Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast h)]; ring
      have h1 := (hp.2 j).injOn (hmem _ (by rw [hi, hij])) (Submodule.zero_mem _)
        (by rw [h0]; simp)
      exact hv.2 h1
  have hjd : j + 1 ≤ finrank ℂ V := by
    by_contra hc
    exact hNj (pow_eq_zero_of_le (by omega) (pow_finrank_eq_zero_of_isNilpotent hN))
  have hjr : ((j : ℕ) : ℝ) ≤ (finrank ℂ V : ℝ) - 1 := by
    have : ((j + 1 : ℕ) : ℝ) ≤ (finrank ℂ V : ℝ) := by exact_mod_cast hjd
    push_cast at this; linarith
  have habs : |(i : ℝ)| = (j : ℝ) := by rw [hj, Nat.cast_natAbs, Int.cast_abs]
  have h1 : (i : ℝ) ≤ (finrank ℂ V : ℝ) - 1 := (le_abs_self _).trans (habs ▸ hjr)
  have h2 : -((finrank ℂ V : ℝ) - 1) ≤ (i : ℝ) := by
    have := neg_abs_le (i : ℝ); rw [habs] at this; linarith
  rw [hi]
  exact ⟨Real.rpow_le_rpow_of_exponent_le hq.le (by linarith),
    Real.rpow_le_rpow_of_exponent_le hq.le (by linarith)⟩

theorem temperedSizes_of_tie : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N) (T : GlobalTheory.RowTie.WDTie N A), GlobalTheory.LocalInv.TemperedSizes N A T.eig := by
  intro R H what₂ N A T w σ hσ a ha α hα
  have hm := mem_Weil_of_isFrob (N.plOm.2 w) hσ
  rw [← T.dim w a]
  rw [T.tempered w a] at ha
  change α ∈ ((T.e w a).inePol σ).roots at hα
  generalize T.e w a = x at ha hα ⊢
  induction x using WD.ind with
  | hP n b =>
    rw [WD.inePol_of_mem _ hm, WD.charPol_mk] at hα
    rw [WD.tempered_mk] at ha
    rw [WD.lpDim_mk]
    have hroot : IsRoot (b.ρ ⟨σ, hm⟩).charpoly α :=
      (mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hα
    have hev : Module.End.HasEigenvalue (b.ρ ⟨σ, hm⟩) α :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr hroot
    have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
    exact norm_le_of_isPurePair hq b.nilpotent (ha ⟨σ, hm⟩ (deg_eq_one_iff.mpr hσ)) hev

end GlobalTheory.LocalInv
