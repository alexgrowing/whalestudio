import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaFinsetSumSmulOfXiExists
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaSelfReNonneg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BetaCapelliSymmOfXiExists
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FoldrCapelliSumEigen
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GramBlockDiagonalEnergyBound
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem levelZero_energy_le_of_eigen_sum :
    GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (s : ℂ) (nn : ℝ → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (s = 1 ∨ s = -1) → B.AB k r ≤ A → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) → (∀ y : ℝ, ∏ t, (|y + lam t| + (d : ℝ)) ≤ nn y) → ∀ w : List (Bool × ℝ), (C7.principalHermitianLattice D s w F).re ≤ (w.map fun l => nn l.2).prod * (B.beta D F F).re := by
  intro hXi k r Wp Wq _ _ _ _ _ _ D lam d A s nn F hs hA hex hnn w
  obtain ⟨N₀, Fi, ν, hν, hcl, hev, hF⟩ := hex
  obtain ⟨σ, hσs, hσ⟩ : ∃ σ : ℝ, s = (σ : ℂ) ∧ |σ| = 1 := by
    rcases hs with h | h
    · exact ⟨1, by simp [h], by simp⟩
    · exact ⟨-1, by simp [h], by simp⟩
  have h5 : ∀ i, B.InCC A 5 (Fi i) := fun i => (hcl i).2 5
  set e : Fin N₀ → ℝ → ℝ := fun i Y => ∏ t, (Y + lam t + (ν i t : ℝ)) with he
  set c : Fin N₀ → Bool × ℝ → ℝ := fun i a => σ * e i a.2 with hc
  have hF1 : ∀ g ∈ B.GV k r, F g = ∑ i ∈ Finset.univ, (1 : ℂ) • Fi i g := by
    intro g hg; simpa using hF g hg
  have hfold := GlobalTheory.foldr_capelli_sum_eigen k r Wp Wq N₀ Fi (fun i Y => ((e i Y : ℝ) : ℂ)) s F (fun i => (hcl i).1)
    (fun i Y g hg => hev i Y g hg) hF w
  have e1 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) Finset.univ Finset.univ _ (fun _ => 1) Fi _ F hA h5 hfold hF1
  have e2 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) Finset.univ Finset.univ (fun _ => 1) (fun _ => 1) Fi F F hA h5
    hF1 hF1
  have hcast : ∀ i, (w.map fun a => s * ((e i a.2 : ℝ) : ℂ)).prod = (((w.map (c i)).prod : ℝ) : ℂ) := by
    intro i
    have : ∀ v : List (Bool × ℝ),
        (v.map fun a => s * ((e i a.2 : ℝ) : ℂ)).prod = (((v.map (c i)).prod : ℝ) : ℂ) := by
      intro v
      induction v with
      | nil => simp
      | cons a v ih =>
        rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, hσs]
        simp only [hc, Complex.ofReal_mul]
    exact this w
  have key := gram_blockDiagonal_energy_bound (Fin N₀) (Bool × ℝ) (fun i j => B.beta D (Fi i) (Fi j)) c w
    (fun l => nn l.2) ?_ ?_ ?_
  · unfold C7.principalHermitianLattice
    rw [e1, e2]
    simp only [star_one, mul_one, one_mul, hcast]
    exact key
  · intro S
    have e3 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) S S (fun _ => 1) (fun _ => 1) Fi
      (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g) (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g) hA h5
      (fun _ _ => rfl) (fun _ _ => rfl)
    have e4 := GlobalTheory.BetaPos.beta_self_re_nonneg k r Wp Wq D (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g)
    rw [e3] at e4
    simpa only [star_one, mul_one, one_mul] using e4
  · intro i j a _ hne
    have hne' : e i a.2 ≠ e j a.2 := fun h => hne (by simp only [hc, h])
    have hsym := GlobalTheory.beta_capelli_symm_of_bessel hXi k r Wp Wq D a.2 A (Fi i) (Fi j) hA (hcl i) (hcl j)
    have h1 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) {i} {j}
      (fun _ => ((e i a.2 : ℝ) : ℂ)) (fun _ => 1) Fi (Q.CV k r (a.2 : ℂ) (Fi i)) (Fi j) hA h5
      (fun g hg => by rw [Finset.sum_singleton]; exact hev i a.2 g hg) (fun g _ => by simp)
    have h2 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) {i} {j}
      (fun _ => 1) (fun _ => ((e j a.2 : ℝ) : ℂ)) Fi (Fi i) (Q.CV k r (a.2 : ℂ) (Fi j)) hA h5
      (fun g _ => by simp) (fun g hg => by rw [Finset.sum_singleton]; exact hev j a.2 g hg)
    simp only [Finset.sum_singleton, star_one, mul_one, one_mul,
      Complex.star_def, Complex.conj_ofReal] at h1 h2
    rw [h1, h2] at hsym
    have hcc : ((e i a.2 : ℂ) - (e j a.2 : ℂ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne')
    have h0 : ((e i a.2 : ℂ) - (e j a.2 : ℂ)) * B.beta D (Fi i) (Fi j) = 0 := by
      rw [sub_mul, hsym, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left hcc
  · intro i a _
    refine le_trans ?_ (hnn a.2)
    simp only [hc, he, abs_mul, hσ, one_mul, Finset.abs_prod]
    refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun t _ => (abs_add_le _ _).trans ?_)
    have : |(ν i t : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν i t
    linarith

end GlobalTheory
