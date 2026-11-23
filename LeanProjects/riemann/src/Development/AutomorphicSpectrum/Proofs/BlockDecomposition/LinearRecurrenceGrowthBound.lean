import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundOfNatDegree

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.LinRec

lemma eq_zero_of_natDegree_eq_zero {p : ℂ[X]} (hp : p.Monic) (hd : p.natDegree = 0)
    {u : ℕ → ℂ} (hu : aeval shift p u = 0) : u = 0 := by
  have hp1 : p = 1 := by
    have h1 : p.coeff 0 = 1 := by
      have h2 := hp.coeff_natDegree
      rwa [hd] at h2
    rw [eq_C_of_natDegree_eq_zero hd, h1, C_1]
  subst hp1
  simpa using hu

theorem uniform_aeval (D : ℕ) (κ' κ : ℝ) (hκ : κ' < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℂ[X], p.Monic → p.natDegree ≤ D →
      (∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp κ') → ∀ (u : ℕ → ℂ) (M : ℝ), aeval shift p u = 0 →
      (∀ j < p.natDegree, ‖u j‖ ≤ M) → 0 ≤ M →
      ∀ i : ℕ, ‖u i‖ ≤ C * Real.exp (κ * i) * M := by
  have hδ : 0 < Real.exp κ - Real.exp κ' := sub_pos.2 (Real.exp_lt_exp.2 hκ)
  induction D with
  | zero =>
    refine ⟨0, le_rfl, fun p hp hd _ u M hu _ _ i => ?_⟩
    have hu0 := eq_zero_of_natDegree_eq_zero hp (Nat.le_zero.1 hd) hu
    simp [hu0]
  | succ D ih =>
    obtain ⟨C', hC', hB⟩ := ih
    have hE' : 0 < Real.exp κ' := Real.exp_pos _
    have hc : 0 ≤ C' * (1 + Real.exp κ') := by positivity
    have hC0 : 0 ≤ 1 + C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ') := by positivity
    refine ⟨_, hC0, fun p hp hd hr u M hu hM hM0 i => ?_⟩
    by_cases hd0 : p.natDegree = 0
    · have hu0 := eq_zero_of_natDegree_eq_zero hp hd0 hu
      have : 0 ≤ (1 + C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ')) *
          Real.exp (κ * i) * M := by positivity
      simpa [hu0] using this
    obtain ⟨z, hz⟩ : ∃ z, p.IsRoot z := IsAlgClosed.exists_root p (by
      intro h0
      exact hd0 (natDegree_eq_zero_iff_degree_le_zero.2 h0.le))
    have hzle := hr z hz
    have hzlt : ‖z‖ < Real.exp κ := hzle.trans_lt (Real.exp_lt_exp.2 hκ)
    obtain ⟨q, rfl⟩ := dvd_iff_isRoot.2 hz
    have hq : q.Monic := (monic_X_sub_C z).of_mul_monic_left hp
    have hqd : ((X - C z) * q).natDegree = q.natDegree + 1 := by
      rw [(monic_X_sub_C z).natDegree_mul hq, natDegree_X_sub_C]
      omega
    have hv : ∀ i : ℕ, ‖u (i + 1) - z * u i‖ ≤
        C' * (1 + Real.exp κ') * Real.exp (κ * i) * M := by
      intro i
      have hb := hB q hq (by omega)
        (fun w hw => hr w (by
          have hw' : eval w q = 0 := hw
          simp [IsRoot, hw']))
        (fun i => u (i + 1) - z * u i) ((1 + Real.exp κ') * M) (aeval_diff q z u hu)
        (fun j hj => ?_) (by positivity) i
      · calc ‖u (i + 1) - z * u i‖ ≤ C' * Real.exp (κ * i) * ((1 + Real.exp κ') * M) := hb
          _ = _ := by ring
      · calc ‖u (j + 1) - z * u j‖ ≤ ‖u (j + 1)‖ + ‖z * u j‖ := norm_sub_le _ _
          _ = ‖u (j + 1)‖ + ‖z‖ * ‖u j‖ := by rw [norm_mul]
          _ ≤ M + Real.exp κ' * M := add_le_add (hM _ (by omega))
              (mul_le_mul hzle (hM _ (by omega)) (norm_nonneg _) hE'.le)
          _ = _ := by ring
    have hg := geom_step z κ _ M hzlt hc hM0 u (hM 0 (by omega)) hv i
    refine hg.trans ?_
    have hdiv : C' * (1 + Real.exp κ') / (Real.exp κ - ‖z‖) ≤
        C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ') :=
      div_le_div_of_nonneg_left hc hδ (by linarith)
    have hEM : 0 ≤ Real.exp (κ * i) * M := by positivity
    calc _ = (1 + C' * (1 + Real.exp κ') / (Real.exp κ - ‖z‖)) * (Real.exp (κ * i) * M) := by ring
      _ ≤ (1 + C' * (1 + Real.exp κ') / (Real.exp κ - Real.exp κ')) * (Real.exp (κ * i) * M) :=
        mul_le_mul_of_nonneg_right (by linarith) hEM
      _ = _ := by ring

theorem uniformRecBound :
    ∀ (D : ℕ) (κ' κ : ℝ), κ' < κ → ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℂ[X], p.Monic → p.natDegree ≤ D →
  (∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp κ') → ∀ (u : ℕ → ℂ) (M : ℝ),
  (∀ i, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * u (i + j) = 0) → (∀ j < p.natDegree, ‖u j‖ ≤ M) → 0 ≤ M →
  ∀ i : ℕ, ‖u i‖ ≤ C * Real.exp (κ * i) * M := by
  intro D κ' κ hκ
  obtain ⟨C, hC, h⟩ := uniform_aeval D κ' κ hκ
  refine ⟨C, hC, fun p hp hd hr u M hu hM hM0 i => h p hp hd hr u M ?_ hM hM0 i⟩
  funext i
  rw [aeval_shift]
  exact hu i

end GlobalTheory.CompanionTheory.LinRec
