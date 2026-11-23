import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddOfMemLdivSet
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.RdivSlice

theorem frobSlice_frob_mul {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime] {i : ℕ} (hi : i < l)
    (f z : K⟦X⟧) : frobSlice l i (frob K l f * z) = f * frobSlice l i z := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [coeff_frobSlice, coeff_mul, coeff_mul]
  symm
  refine Finset.sum_of_injOn (fun p : ℕ × ℕ => (l * p.1, l * p.2 + i)) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ - ⟨p', q'⟩ - h
    simp only [Prod.mk.injEq, add_left_inj] at h ⊢
    exact ⟨Nat.eq_of_mul_eq_mul_left hl h.1, Nat.eq_of_mul_eq_mul_left hl h.2⟩
  · rintro ⟨p, q⟩ h
    simp only [Finset.mem_coe, Finset.HasAntidiagonal.mem_antidiagonal] at h ⊢
    rw [← h]; ring
  · rintro ⟨p, q⟩ h hn
    rw [coeff_frob]
    split_ifs with hd
    · exfalso
      obtain ⟨t, rfl⟩ := hd
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at h
      have ht : t ≤ n := by
        by_contra hc
        have : l * (n + 1) ≤ l * t := Nat.mul_le_mul_left l (by omega)
        rw [mul_add, mul_one] at this
        omega
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
      refine hn ⟨(t, s), by simp, ?_⟩
      rw [mul_add] at h
      simp only [Prod.mk.injEq, true_and]
      omega
    · simp
  · rintro ⟨p, q⟩ -
    simp only [coeff_frob, coeff_frobSlice, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hl]

theorem frobSlice_sum {K : Type} [Field K] (l i : ℕ) {μ : Type} (s : Finset μ) (f : μ → K⟦X⟧) :
    frobSlice l i (∑ j ∈ s, f j) = ∑ j ∈ s, frobSlice l i (f j) := by
  ext n
  simp only [coeff_frobSlice, map_sum]

theorem bdd_matrix_mul {K : Type} [NormedField K] [IsUltrametricDist K] {μ ν ρ : Type} [Fintype ν]
    {Y : Matrix μ ν K⟦X⟧} {Z : Matrix ν ρ K⟦X⟧} (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c)
    (hZ : ∃ c : ℝ, ∀ i j n, ‖coeff n (Z i j)‖ ≤ c) :
    ∃ c : ℝ, ∀ i j n, ‖coeff n ((Y * Z) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hY
  obtain ⟨b, hb⟩ := hZ
  refine ⟨max a 0 * max b 0, fun i j n => ?_⟩
  rw [Matrix.mul_apply, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    (le_max_right a 0) (le_max_right b 0) (f := Y i k) (g := Z k j)
    (fun m => by rw [mul_one]; exact (ha i k m).trans (le_max_left _ _))
    (fun m => by rw [mul_one]; exact (hb k j m).trans (le_max_left _ _)) n

theorem exists_pow_smul_bdd {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} [NeZero a] {μ : Type} [Fintype μ]
    (Y : ZMod a → Matrix μ μ K⟦X⟧) (hY : ∀ τ i j, Y τ i j ∈ invE l e (A O K)) :
    ∃ N : ℕ, ∀ τ i j n, ‖coeff n ((E K l e ^ N • Y τ) i j)‖ ≤ 1 := by
  choose n hn using fun p : ZMod a × μ × μ => hY p.1 p.2.1 p.2.2
  refine ⟨Finset.univ.sup n, fun τ i j => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i, j)))
  rw [Matrix.smul_apply, smul_eq_mul, hc, pow_add, mul_assoc]
  exact mem_A.1 (mul_mem (pow_mem (E_mem l e (A O K)) c) (hn (τ, i, j)))

theorem exists_frobSlice_mem_rdivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet τ, ∀ i < l, frobSlice l i (E K l e ^ M * h) ∈ F.rdivSet (τ - 1) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  obtain ⟨α, hα⟩ := exists_pow_smul_bdd P.mxInv P.mxInv_mem
  obtain ⟨β, hβ⟩ := exists_pow_smul_bdd Q.mx Q.mx_mem
  refine ⟨α + β, fun τ h hh i hi => ?_⟩
  obtain ⟨hb, Y, hY, hFY⟩ := hh
  obtain ⟨c, hc⟩ := GlobalTheory.BK.Hom.bdd_mul (f := E K l e ^ (α + β))
    ⟨1, mem_A.1 (pow_mem (E_mem l e (A O K)) _)⟩ hb
  obtain ⟨d, hd⟩ := bdd_matrix_mul (bdd_matrix_mul ⟨1, hα τ⟩ hY) ⟨1, hβ τ⟩
  have h1 : (F.mat (τ - 1)).map (frob K l) * P.mxInv τ = Q.mxInv τ * F.mat τ := by
    calc _ = Q.mxInv τ * (Q.mx τ * (F.mat (τ - 1)).map (frob K l)) * P.mxInv τ := by
          rw [← Matrix.mul_assoc, Q.mxInv_mul_mx, Matrix.one_mul]
      _ = _ := by
          rw [← F.comm, Matrix.mul_assoc, Matrix.mul_assoc, P.mx_mul_mxInv, Matrix.mul_one]
  have h2 : (F.mat (τ - 1)).map (frob K l) *
      ((E K l e ^ α • P.mxInv τ) * Y * (E K l e ^ β • Q.mx τ)) =
      (E K l e ^ (α + β) * h) • (1 : Matrix κ κ K⟦X⟧) := by
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc (Q.mxInv τ), hFY,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Q.mxInv_mul_mx, smul_smul, smul_smul,
      pow_add]
  refine ⟨⟨c, fun n => by rw [coeff_frobSlice]; exact hc _⟩,
    ((E K l e ^ α • P.mxInv τ) * Y * (E K l e ^ β • Q.mx τ)).map (frobSlice l i),
    ⟨d, fun s t n => by rw [Matrix.map_apply, coeff_frobSlice]; exact hd _ _ _⟩, ?_⟩
  ext1 s t
  have h3 := congrArg (fun M : Matrix κ κ K⟦X⟧ => frobSlice l i (M s t)) h2
  simp only [Matrix.mul_apply (M := (F.mat (τ - 1)).map (frob K l)), frobSlice_sum,
    Matrix.map_apply, frobSlice_frob_mul l hi] at h3
  rw [Matrix.mul_apply]
  simp only [Matrix.map_apply]
  rw [h3, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs
  · simp
  · ext n
    simp [coeff_frobSlice]

end GlobalTheory.BK.RdivSlice
