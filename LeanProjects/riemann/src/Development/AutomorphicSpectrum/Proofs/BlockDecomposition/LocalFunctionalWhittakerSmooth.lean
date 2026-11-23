import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.LFS
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFSmooth

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem modulus_det_eq_one {u : GL (Fin 3) F} (hu : u ∈ GLnLocal.integralGL F 3) :
    modulus ((GeneralLinearGroup.det u : Fˣ) : F) = 1 := by
  have key : ∀ w ∈ GLnLocal.integralGL F 3,
      modulus ((GeneralLinearGroup.det w : Fˣ) : F) ≤ 1 := by
    rintro _ ⟨v, rfl⟩
    rw [modulus_le_one_iff]
    have h : ((GeneralLinearGroup.det (GLnLocal.integralGLHom F 3 v) : Fˣ) : F) =
        (𝒪[F]).subtype (v : Matrix (Fin 3) (Fin 3) 𝒪[F]).det := by
      rw [RingHom.map_det]
      rfl
    rw [h]
    exact Subtype.property _
  have h1 := key u hu
  have h2 := key u⁻¹ (inv_mem hu)
  rw [map_inv, Units.val_inv_eq_inv_val, modulus_inv] at h2
  exact le_antisymm h1 ((inv_le_one₀ (modulus_pos (Units.ne_zero _))).1 h2)

theorem exists_openSubgroup_invariant {Φ : Matrix (Fin 2) (Fin 3) F → ℂ}
    (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) :
    ∃ U : OpenSubgroup (GL (Fin 3) F), (∀ u ∈ U, u ∈ GLnLocal.integralGL F 3) ∧
      ∀ u ∈ U, ∀ X : Matrix (Fin 2) (Fin 3) F,
        Φ (X * (u : Matrix (Fin 3) (Fin 3) F)) = Φ X := by
  have hcont : Continuous fun p : Matrix (Fin 2) (Fin 3) F × GL (Fin 3) F =>
      p.1 * (p.2 : Matrix (Fin 3) (Fin 3) F) :=
    continuous_fst.matrix_mul (Units.continuous_val.comp continuous_snd)
  have hlc : IsLocallyConstant fun p : Matrix (Fin 2) (Fin 3) F × GL (Fin 3) F =>
      Φ (p.1 * (p.2 : Matrix (Fin 3) (Fin 3) F)) - Φ p.1 :=
    (hl.comp_continuous hcont).sub (hl.comp_continuous continuous_fst)
  have hopen := hlc.isOpen_fiber 0
  have hsub : tsupport Φ ×ˢ ({1} : Set (GL (Fin 3) F)) ⊆
      (fun p : Matrix (Fin 2) (Fin 3) F × GL (Fin 3) F =>
        Φ (p.1 * (p.2 : Matrix (Fin 3) (Fin 3) F)) - Φ p.1) ⁻¹' {0} := by
    rintro ⟨X, u⟩ ⟨-, hu⟩
    obtain rfl : u = 1 := hu
    simp
  obtain ⟨A, B, -, hB, hA, h1, hAB⟩ :=
    generalized_tube_lemma hc isCompact_singleton hopen hsub
  obtain ⟨m, -, hm⟩ :=
    (GLnLocal.hasBasis_nhds_one F 3).mem_iff.1 (hB.mem_nhds (h1 rfl))
  have hfix : ∀ u ∈ GLnLocal.congruenceSubgroup F 3 m, ∀ X, Φ X ≠ 0 →
      Φ (X * (u : Matrix (Fin 3) (Fin 3) F)) = Φ X := by
    intro u hu X hX
    have : (X, u) ∈ A ×ˢ B := ⟨hA (subset_tsupport _ hX), hm hu⟩
    exact sub_eq_zero.1 (hAB this)
  refine ⟨⟨GLnLocal.congruenceSubgroup F 3 m, GLnLocal.isOpen_congruenceSubgroup F 3 m⟩,
    fun u hu => GLnLocal.congruenceSubgroup_le F 3 m hu, fun u hu X => ?_⟩
  have hu' : u ∈ GLnLocal.congruenceSubgroup F 3 m := hu
  by_cases hX : Φ X = 0
  · by_cases hY : Φ (X * (u : Matrix (Fin 3) (Fin 3) F)) = 0
    · rw [hX, hY]
    · have h := hfix u⁻¹ (inv_mem hu') _ hY
      rw [Matrix.mul_assoc, Units.mul_inv_of_eq rfl, Matrix.mul_one] at h
      exact h.symm
  · exact hfix u hu' X hX

theorem smoothW : Ad3.LFS.SSmoothW := by
  intro F _ _ _ _ _ _ ψ ν W' Φ h
  obtain ⟨hl, hc⟩ := h.2.2.2
  obtain ⟨U, hUK, hU⟩ := exists_openSubgroup_invariant hl hc
  refine ⟨U, fun g u hu => ?_⟩
  have hinn : ∀ k, inn ψ Φ k (g * u) = inn ψ Φ k g := by
    intro k
    simp only [inn, Units.val_mul, ← Matrix.mul_assoc, hU u hu]
  have hdet : mp (GeneralLinearGroup.det (g * u)) 1 = mp (GeneralLinearGroup.det g) 1 := by
    simp only [mp, map_mul, Units.val_mul, modulus_mul, modulus_det_eq_one (hUK u hu), mul_one]
  simp only [Wp, hinn, hdet]

end GlobalTheory.CompanionTheory.LFSmooth
