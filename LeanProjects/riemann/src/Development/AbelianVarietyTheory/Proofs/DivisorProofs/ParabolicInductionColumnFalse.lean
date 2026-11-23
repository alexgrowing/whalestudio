import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothColRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SmGL.RowOneCell Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.RowOneCell

theorem parInd_colPart_false_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₂ → ∀ (u v : ℕ), Nonempty ((parInd (colPart u v false) (colRep χ₁ χ₂ u v false)).Equiv
      (detRep (Fin 1) (χ₂ * absPow k (-(v : ℂ) / 2)))) := by
  intro k _ _ _ _ χ₁ χ₂ h₂ u v
  have h0 : ∀ j, j ≠ true → sz u v j false = 0 := by
    intro j hj
    cases j
    · rfl
    · exact absurd rfl hj
  have hP : ∀ x : GL (Fin 1) k, x ∈ parab k (colPart u v false) := fun x =>
    OneBlockCell.mem_parab_of_single (n := fun i => sz u v i false) (colPart u v false) true h0 x
  have hδ : ∀ z, deltaHalf k (fun i => Fin (sz u v i false)) z = 1 := fun z =>
    OneBlockCell.deltaHalf_eq_one_of_single true h0 z
  have hd0 : ∀ p : parab k (colPart u v false),
      GeneralLinearGroup.det (leviProj k (colPart u v false) p false) = 1 := by
    intro p
    haveI : IsEmpty (Fin (sz u v false false)) := Fin.isEmpty'
    ext
    simp [Matrix.det_isEmpty]
  have hd1 : ∀ p : parab k (colPart u v false),
      GeneralLinearGroup.det (leviProj k (colPart u v false) p true) =
        GeneralLinearGroup.det (p : GL (Fin 1) k) := by
    intro p
    ext
    show Matrix.det (((show GL (Fin 1) k from leviProj k (colPart u v false) p true)) : Matrix (Fin 1) (Fin 1) k) =
      Matrix.det ((p : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k)
    rw [Matrix.det_unique, Matrix.det_unique]
    exact congrArg₂ (fun a b => ((p : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k) a b)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  let ψ : kˣ →* ℂˣ := χ₂ * absPow k (-(v : ℂ) / 2)
  have hsm : IsSmooth (detRep (Fin 1) ψ) :=
    (isSmooth_ofChar_iff _).2 (h₂.mul (GlobalTheory.LocGL.isSmoothChar_absPow _)).detChar
  let Ψ : ℂ ≃ₗ[ℂ] ℂ ⊗[ℂ] ℂ := (TensorProduct.lid ℂ ℂ).symm
  have hΨ : ∀ c, Ψ c = (1 : ℂ) ⊗ₜ c := fun c => rfl
  let τ := (twist (colRep χ₁ χ₂ u v false) (deltaHalf k (fun i => Fin (sz u v i false)))).comp
    (leviProj k (colPart u v false))
  have law : ∀ (p : parab k (colPart u v false)) c, τ p (Ψ c) = Ψ (detRep (Fin 1) ψ p c) := by
    intro p c
    rw [MonoidHom.comp_apply, twist_apply, hδ, hΨ, hΨ]
    simp only [Units.val_one, one_smul]
    show extTensor _ _ _ ((1 : ℂ) ⊗ₜ c) = _
    rw [extTensor_tmul]
    simp only [detRep, ofChar_apply, detChar_apply]
    change (((χ₁ (GeneralLinearGroup.det (leviProj k (colPart u v false) p false)) : ℂˣ) : ℂ) * 1) ⊗ₜ[ℂ]
      ((((colChar v χ₂ false) (GeneralLinearGroup.det (leviProj k (colPart u v false) p true)) : ℂˣ) : ℂ) * c) = _
    rw [hd0, hd1, map_one, Units.val_one, mul_one]
    rfl
  let F : (detRep (Fin 1) ψ).IntertwiningMap (parInd (colPart u v false) (colRep χ₁ χ₂ u v false)) :=
    { toFun := fun c => ⟨⟨fun x => Ψ (detRep (Fin 1) ψ x c), fun p x => by
          show Ψ (detRep (Fin 1) ψ (↑p * x) c) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm c).mem_nhds (by simp)) fun x hx => by
          have hx' : detRep (Fin 1) ψ x c = c := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ (detRep (Fin 1) ψ (y * x) c) = Ψ (detRep (Fin 1) ψ y c)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun c d => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun a c => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ (detRep (Fin 1) ψ x (a • c)) = a • Ψ (detRep (Fin 1) ψ x c)
        rw [map_smul, map_smul]))
      isIntertwining' := fun h => LinearMap.ext fun c => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ (detRep (Fin 1) ψ x (detRep (Fin 1) ψ h c)) = Ψ (detRep (Fin 1) ψ (x * h) c)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun c d hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ (detRep (Fin 1) ψ 1 c) = Ψ (detRep (Fin 1) ψ 1 d) := congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ (detRep (Fin 1) ψ x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

end GlobalTheory.SmGL.RowOneCell
