import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop

open Matrix UpperTheory.V.Weyl

theorem UpperTheory.V.Weyl.subMat :
    ∀ (G : Type) [Monoid G] (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (S : Submodule ℂ (Fin d → ℂ)),
      (∀ y, ∀ v ∈ S, ρ y *ᵥ v ∈ S) →
      ∃ (d' : ℕ) (A : Matrix (Fin d) (Fin d') ℂ) (B : Matrix (Fin d') (Fin d) ℂ) (ρ' : G →* Matrix (Fin d') (Fin d') ℂ),
        d' = Module.finrank ℂ S ∧ B * A = 1 ∧ (∀ w, A *ᵥ w ∈ S) ∧ (∀ y, ρ' y = B * ρ y * A) ∧ ∀ y, ρ y * A = A * ρ' y := by
  intro G _ d ρ S hS
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl S
  let b := Module.finBasis ℂ S
  let P : (Fin d → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    b.equivFun.toLinearMap ∘ₗ Submodule.linearProjOfIsCompl S T hT
  let I : (Fin (Module.finrank ℂ S) → ℂ) →ₗ[ℂ] (Fin d → ℂ) := S.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hIP : ∀ v, v ∈ S → I (P v) = v := by
    intro v hv
    have e : S.linearProjOfIsCompl T hT v = ⟨v, hv⟩ := Submodule.linearProjOfIsCompl_apply_left hT ⟨v, hv⟩
    show ((b.equivFun.symm (b.equivFun (S.linearProjOfIsCompl T hT v)) : S) : Fin d → ℂ) = v
    rw [e, LinearEquiv.symm_apply_apply]
  have hPI : P ∘ₗ I = LinearMap.id := by
    apply LinearMap.ext
    intro w
    have e : S.linearProjOfIsCompl T hT ((b.equivFun.symm w : S) : Fin d → ℂ) = b.equivFun.symm w :=
      Submodule.linearProjOfIsCompl_apply_left hT _
    show b.equivFun (S.linearProjOfIsCompl T hT ((b.equivFun.symm w : S) : Fin d → ℂ)) = w
    rw [e, LinearEquiv.apply_symm_apply]
  let A := LinearMap.toMatrix' I
  let B := LinearMap.toMatrix' P
  have hAw : ∀ w, A *ᵥ w = I w := fun w => LinearMap.toMatrix'_mulVec I w
  have hBw : ∀ v, B *ᵥ v = P v := fun v => LinearMap.toMatrix'_mulVec P v
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp, hPI, LinearMap.toMatrix'_id]
  have key : ∀ M : Matrix (Fin d) (Fin (Module.finrank ℂ S)) ℂ, (∀ w, M *ᵥ w ∈ S) → A * (B * M) = M := by
    intro M hM
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBw, hAw,
      hIP _ (hM w)]
  have hAS : ∀ w, A *ᵥ w ∈ S := by
    intro w
    rw [hAw]
    exact (b.equivFun.symm w).2
  have hcol : ∀ y w, (ρ y * A) *ᵥ w ∈ S := by
    intro y w
    rw [← Matrix.mulVec_mulVec]
    exact hS y _ (hAS w)
  let ρ' : G →* Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ :=
    { toFun := fun y => B * ρ y * A
      map_one' := by simp only [map_one, Matrix.mul_one, hBA]
      map_mul' := by
        intro x y
        simp only [map_mul, Matrix.mul_assoc]
        rw [key _ (hcol y)] }
  refine ⟨_, A, B, ρ', rfl, hBA, hAS, fun y => rfl, fun y => ?_⟩
  show ρ y * A = A * (B * ρ y * A)
  rw [Matrix.mul_assoc B, key _ (hcol y)]
