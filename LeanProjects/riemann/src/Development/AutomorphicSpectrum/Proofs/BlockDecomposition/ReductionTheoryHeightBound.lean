import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvecSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmallHeightVectorIsotropicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryPointsHeightBoundCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryPointsHeightBoundFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusSiegelHeightLowerBoundStatement

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

namespace GlobalTheory.CompanionTheory.RedCov.First

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

omit [NumberField F] [NumberField E] in
theorem form_eq_hE (u v : Fin n → E) :
    toLinearMapₛₗ₂' E (σ : E →+* E) (RingHom.id E) J u v = hE σ J u v := by
  simp only [toLinearMapₛₗ₂'_apply, smul_eq_mul, RingHom.id_apply, RingHom.coe_coe, hE, Formalism.UG.hform]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField F] [NumberField E] in
theorem hE_mulVec {m : Matrix (Fin n) (Fin n) E} (hm : cT (σ : E →+* E) m * J * m = J) (u : Fin n → E) :
    hE σ J (m *ᵥ u) (m *ᵥ u) = hE σ J u u := by
  have e : Matrix.of (fun a (_ : Fin 1) => (m *ᵥ u) a) = m * Matrix.of (fun a (_ : Fin 1) => u a) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have h1 := gram_apply (σ := σ) (J := J) (s := 1) (r := 1) (Matrix.of fun a _ => (m *ᵥ u) a) (Matrix.of fun a _ => (m *ᵥ u) a) 0 0
  have h2 := gram_apply (σ := σ) (J := J) (s := 1) (r := 1) (Matrix.of fun a _ => u a) (Matrix.of fun a _ => u a) 0 0
  rw [e, pgram_unitary hm] at h1
  rw [h2] at h1
  rw [← form_eq_hE, ← form_eq_hE]
  rw [e] at *
  exact h1.symm

theorem exists_sends {γ : GAd σ J} (hγ : γ ∈ ratPts σ J) {u : Fin n → E} (hu : u ≠ 0) (hi : hE σ J u u = 0) :
    ∃ v : Fin n → E, v ≠ 0 ∧ hE σ J v v = 0 ∧ Sends σ J γ u v := by
  obtain ⟨m, hm, e⟩ := hγ
  refine ⟨m.1 *ᵥ u, ?_, ?_, ?_⟩
  · intro h0
    apply hu
    have := congrArg (fun z => (m⁻¹).1 *ᵥ z) h0
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this
  · rw [hE_mulVec hm, hi]
  · have e1 : (matHom _ σ J γ).1 = m.1.map (inclR (F := F) (AF F)) := by
      rw [matHom_apply]
      exact (congrArg Units.val e).symm
    unfold Sends
    rw [e1]
    funext i
    simp only [ratV]
    exact (RingHom.map_mulVec (inclR (F := F) (AF F)) m.1 u i).symm

omit [NumberField F] [NumberField E] in
theorem first_witt_vector_ne_zero {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) : Xᵀ 0 ≠ 0 := by
  intro h0
  have h1 := gram_apply (σ := σ) (J := J) X Y 0 0
  rw [hW.xy, h0] at h1
  simp at h1

omit [NumberField F] [NumberField E] in
theorem first_witt_vector_isotropic {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) :
    hE σ J (Xᵀ 0) (Xᵀ 0) = 0 := by
  have h1 := gram_apply (σ := σ) (J := J) X X 0 0
  rw [hW.xx, form_eq_hE] at h1
  exact h1.symm

theorem exists_isotropic_le
    (hS : ∃ ε : ℝ, 0 < ε ∧ ∀ (g : GAd σ J) (v : Fin n → E), v ≠ 0 → hgt σ J g v < ε → hE σ J v v = 0)
    (hM : ∀ t : ℝ, 0 < t → ∃ C₀ : Set (GAd σ J), IsCompact C₀ ∧ ∀ g : GAd σ J,
      (∀ v : Fin n → E, v ≠ 0 → t ≤ hgt σ J g v) → ∃ γ ∈ ratPts σ J, γ⁻¹ * g ∈ C₀)
    (hB : ∀ {C : Set (GAd σ J)}, IsCompact C → ∀ {v : Fin n → E}, v ≠ 0 → ∃ B : ℝ, ∀ c ∈ C, hgt σ J c v ≤ B)
    {x : Fin n → E} (hx : x ≠ 0) (hi : hE σ J x x = 0) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ g : GAd σ J, ∃ u : Fin n → E, u ≠ 0 ∧ hE σ J u u = 0 ∧ hgt σ J g u ≤ C₁ := by
  obtain ⟨ε, hε, hS⟩ := hS
  obtain ⟨C₀, hC₀, hC⟩ := hM ε hε
  obtain ⟨B, hB⟩ := hB hC₀ hx
  refine ⟨max ε B, lt_max_of_lt_left hε, fun g => ?_⟩
  by_cases h : ∃ v : Fin n → E, v ≠ 0 ∧ hgt σ J g v < ε
  · obtain ⟨v, hv, hlt⟩ := h
    exact ⟨v, hv, hS g v hv hlt, hlt.le.trans (le_max_left _ _)⟩
  · push_neg at h
    obtain ⟨γ, hγ, hγC⟩ := hC g h
    obtain ⟨v, hv, hvi, hs⟩ := exists_sends hγ hx hi
    refine ⟨v, hv, hvi, ?_⟩
    rw [← hgt_mul hs.inv]
    exact (hB _ hγC).trans (le_max_right _ _)

theorem exp_neg_le_rpow {d : ℝ} (hd : 0 < d) {s D : ℝ} (h : Real.exp (-(d * s)) ≤ D) :
    Real.exp (-s) ≤ D ^ (1 / d) := by
  have e : Real.exp (-s) = Real.exp (-(d * s)) ^ (1 / d) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  rw [e]
  exact Real.rpow_le_rpow (Real.exp_pos _).le h (by positivity)

end GlobalTheory.CompanionTheory.RedCov.First

open GlobalTheory.CompanionTheory.RedCov.First in

theorem GlobalTheory.CompanionTheory.RedCov.First.exp_neg_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin (r + 1)) E) (hW : IsWittFrame σ J X Y) (a) (ha : IsTorus σ J X Y a)
    (Ω C : Set (GAd σ J)) (hΩ : IsCompact Ω) (hΩP : Ω ⊆ minParOne σ J X) (hC : IsCompact C) :
    ∃ M : ℝ, 0 < M ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 →
      NearMin σ J (ω * a s * κ) (e • Xᵀ 0) → Real.exp (- s 0) ≤ M := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  obtain ⟨C₁, hC₁, hu⟩ := exists_isotropic_le (GlobalTheory.T.small_height_vector_isotropic F E σ h n J hJ) ((GlobalTheory.T.unitary_points_height_bound_finite GlobalTheory.T.unitary_points_height_bound_compact) F E σ h n J hJ)
    (fun hC _ hv => GlobalTheory.CompanionTheory.RedCov.Bridge.exists_hgt_le σ J hC hv) (first_witt_vector_ne_zero hW) (first_witt_vector_isotropic hW)
  obtain ⟨P, hP, hlow⟩ := GlobalTheory.T.torus_siegel_height_lower_bound F E σ h n J hJ r X Y hW a ha Ω C hΩ
    (hΩP.trans minParOne_subset) hC
  have hd : (0 : ℝ) < Module.finrank ℚ F := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨(2 * P * C₁) ^ (1 / (Module.finrank ℚ F : ℝ)), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro ω hω s κ hκ e he hN
  obtain ⟨u, hu0, hui, hule⟩ := hu (ω * a s * κ)
  refine exp_neg_le_rpow hd ((hlow ω hω s κ hκ e he).trans ?_)
  calc P * hgt σ J (ω * a s * κ) (e • Xᵀ 0) ≤ P * (2 * hgt σ J (ω * a s * κ) u) :=
        mul_le_mul_of_nonneg_left (hN.2.2 u hu0 hui) hP.le
    _ ≤ P * (2 * C₁) := by gcongr
    _ = 2 * P * C₁ := by ring
