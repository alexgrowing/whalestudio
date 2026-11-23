import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.SubMat

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.irrSub :
    ∀ (G : Type) [Monoid G] (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ), 0 < d →
      ∃ (d' : ℕ) (A : Matrix (Fin d) (Fin d') ℂ) (B : Matrix (Fin d') (Fin d) ℂ) (ρ' : G →* Matrix (Fin d') (Fin d') ℂ),
        0 < d' ∧ d' ≤ d ∧ B * A = 1 ∧ (∀ y, ρ' y = B * ρ y * A) ∧ (∀ y, ρ y * A = A * ρ' y) ∧
        ∀ W : Submodule ℂ (Fin d' → ℂ), (∀ y, ∀ v ∈ W, ρ' y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro G _ d ρ hd
  classical
  have hex : ∃ m, ∃ S : Submodule ℂ (Fin d → ℂ), (∀ y, ∀ v ∈ S, ρ y *ᵥ v ∈ S) ∧ S ≠ ⊥ ∧
      Module.finrank ℂ S = m := by
    refine ⟨_, ⊤, fun y v _ => Submodule.mem_top, ?_, rfl⟩
    intro h
    have h1 : Module.finrank ℂ (⊤ : Submodule ℂ (Fin d → ℂ)) = 0 := by
      rw [h]; exact finrank_bot ℂ (Fin d → ℂ)
    rw [finrank_top, Module.finrank_fin_fun] at h1
    omega
  obtain ⟨S, hSinv, hSne, hSrank⟩ := Nat.find_spec hex
  obtain ⟨d', A, B, ρ', hd', hBA, -, hρ', hint⟩ := subMat G d ρ S hSinv
  have hSpos : Module.finrank ℂ S ≠ 0 := fun h => hSne (Submodule.finrank_eq_zero.mp h)
  refine ⟨d', A, B, ρ', ?_, ?_, hBA, hρ', hint, ?_⟩
  · omega
  · have hle := Submodule.finrank_le S
    rw [Module.finrank_fin_fun] at hle
    omega
  · intro W hW
    by_cases hWb : W = ⊥
    · exact Or.inl hWb
    right
    have hinj : Function.Injective A.mulVecLin := by
      intro v w h
      have h2 := congrArg (fun u => B *ᵥ u) h
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hBA] using h2
    have hrank : Module.finrank ℂ (W.map A.mulVecLin) = Module.finrank ℂ W :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W)).symm
    have hW'inv : ∀ y, ∀ v ∈ W.map A.mulVecLin, ρ y *ᵥ v ∈ W.map A.mulVecLin := by
      intro y v hv
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
      refine Submodule.mem_map.mpr ⟨ρ' y *ᵥ w, hW y w hw, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint]
    have hW'ne : W.map A.mulVecLin ≠ ⊥ := by
      intro h
      apply hWb
      rw [← Submodule.finrank_eq_zero, ← hrank, h]
      exact finrank_bot ℂ (Fin d → ℂ)
    have hmin := Nat.find_min' hex ⟨W.map A.mulVecLin, hW'inv, hW'ne, rfl⟩
    apply Submodule.eq_top_of_finrank_eq
    have hle := Submodule.finrank_le W
    rw [Module.finrank_fin_fun] at hle ⊢
    omega
