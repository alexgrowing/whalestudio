import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootDenseAlt

theorem aeval_grassPolyCoord {f j m : ℕ} (x : Fin f × Fin j × Fin m → ℂ)
    (p : Σ _ : Fin f, PlIdx j m) :
    aeval x (grassPolyCoord f j m p) = rootCoord (fun τ a b => x (τ, a, b)) p := by
  simp only [grassPolyCoord, rootCoord]
  rw [← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext a b
  simp only [colsOf, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, id,
    onePipe, Matrix.of_apply]
  generalize (p.2.1.orderEmbOfFin p.2.2) b = c
  induction c using Fin.addCases with
  | left c => simp [Fin.append_left, Matrix.one_apply, apply_ite]
  | right c => simp [Fin.append_right]

theorem aeval_rootCoord {f j m : ℕ} (x : Fin f × Fin j × Fin m → ℂ) (g : MRing (plBlocks f j m)) :
    aeval (rootCoord (fun τ a b => x (τ, a, b))) g = aeval x (aeval (grassPolyCoord f j m) g) := by
  rw [show aeval x (aeval (grassPolyCoord f j m) g) =
      ((aeval x).restrictScalars ℤ).comp (aeval (grassPolyCoord f j m)) g from rfl, comp_aeval]
  exact congrArg (fun y => aeval y g) (funext fun p => (aeval_grassPolyCoord x p).symm)

theorem aeval_comp_ringHom {σ τ Ω : Type*} [Field Ω] (φ : MvPolynomial σ ℚ →+* Ω)
    (P : τ → MvPolynomial σ ℚ) (g : MvPolynomial τ ℤ) :
    aeval (fun i => φ (P i)) g = φ (aeval P g) := by
  have : (aeval (fun i => φ (P i)) : MvPolynomial τ ℤ →ₐ[ℤ] Ω).toRingHom =
      φ.comp (aeval P).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  exact congrArg (fun ψ : MvPolynomial τ ℤ →+* Ω => ψ g) this

end RootDenseAlt

theorem RootDense.proof (h₁ : MultiHomogMemCoord.Statement) (h₂ : RootsOfUnityDense.Statement) :
    RootDense.Statement := by
  intro f j m g ⟨a, ha⟩ hg
  have hQ0 : aeval (grassPolyCoord f j m) g ≠ 0 := by
    intro h0
    apply hg
    rw [grassIdeal, h₁ (Fin f) (plBlocks f j m) (GrassField f j m) (grassCoord f j m) g a ha]
    exact (RootDenseAlt.aeval_comp_ringHom
      (algebraMap (MvPolynomial (Fin f × Fin j × Fin m) ℚ) (GrassField f j m)) _ g).trans
      (by rw [h0, map_zero])
  let e := Fintype.equivFin (Fin f × Fin j × Fin m)
  have hP : rename e (map (algebraMap ℚ ℂ) (aeval (grassPolyCoord f j m) g)) ≠ 0 := by
    intro h
    apply hQ0
    apply map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
    apply rename_injective e e.injective
    simpa using h
  obtain ⟨z, hz, hzQ⟩ : ∃ z : Fin (Fintype.card (Fin f × Fin j × Fin m)) → ℂ,
      (∀ i, ∃ k : ℕ, 0 < k ∧ z i ^ k = 1) ∧
        eval z (rename e (map (algebraMap ℚ ℂ) (aeval (grassPolyCoord f j m) g))) ≠ 0 := by
    by_contra! H
    exact hP (h₂ _ _ H)
  refine ⟨rootPointIdeal (fun τ a b => (z ∘ e) (τ, a, b)), ⟨_, fun τ a b => hz _, rfl⟩, ?_⟩
  show g ∉ mCoordIdeal _
  rw [h₁ (Fin f) (plBlocks f j m) ℂ _ g a ha]
  refine fun h => hzQ ?_
  rw [eval_rename, eval_map, ← aeval_def, ← RootDenseAlt.aeval_rootCoord]
  exact h

end

end GroundTheory.Heights₂.Heights
