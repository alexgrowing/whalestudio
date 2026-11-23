import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Degree

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}

theorem basisMat_transpose_eq (W : Submodule E (Fin n → E)) :
    ((basisMat W)ᵀ : Fin (Module.finrank E W) → Fin n → E) =
      W.subtype ∘ (Module.finBasis E W) := by
  funext j i
  rfl

theorem basisMat_linearIndependent (W : Submodule E (Fin n → E)) :
    LinearIndependent E (basisMat W)ᵀ := by
  rw [basisMat_transpose_eq]
  exact (Module.finBasis E W).linearIndependent.map' W.subtype W.ker_subtype

theorem span_basisMat (W : Submodule E (Fin n → E)) :
    Submodule.span E (Set.range (basisMat W)ᵀ) = W := by
  rw [basisMat_transpose_eq, Set.range_comp, ← Submodule.map_span, (Module.finBasis E W).span_eq,
    Submodule.map_top, Submodule.range_subtype]

theorem mul_transpose_apply {κ : Type} [Fintype κ] (g : GL (Fin n) E) (M : Matrix (Fin n) κ E) (j : κ) :
    (g.val * M)ᵀ j = Matrix.toLin' g.val (Mᵀ j) := by
  funext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem ker_toLin'_eq_bot (g : GL (Fin n) E) : LinearMap.ker (Matrix.toLin' g.val) = ⊥ := by
  refine LinearMap.ker_eq_bot.2 fun a b hab => ?_
  have h := congrArg (Matrix.toLin' (g⁻¹ : GL (Fin n) E).val) hab
  simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using h

theorem frame_rat {κ : Type} [Fintype κ] (x : GA E n) (g : GL (Fin n) E) (M : Matrix (Fin n) κ E) :
    ((ratGL E n g * x)⁻¹ : GA E n).val * (g.val * M).map (algebraMap E (Ad E)) =
      (x⁻¹ : GA E n).val * M.map (algebraMap E (Ad E)) := by
  have hr : (g.val * M).map (algebraMap E (Ad E)) =
      (ratGL E n g).val * M.map (algebraMap E (Ad E)) := by
    rw [Matrix.map_mul]
    rfl
  rw [hr, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (ratGL E n g)⁻¹.val,
    Units.inv_mul, Matrix.one_mul]

theorem degG_rat {κ : Type} [Fintype κ] [DecidableEq κ] (x : GA E n) (g : GL (Fin n) E)
    (M : Matrix (Fin n) κ E) : degG (ratGL E n g * x) (g.val * M) = degG x M := by
  simp only [degG, frame_rat]

theorem degRat_of_degBasisG : DegBasisG → DegRat := by
  intro h E _ _ _ n x g W
  have hli : LinearIndependent E (g.val * basisMat W)ᵀ := by
    have e : (fun j => (g.val * basisMat W)ᵀ j) = Matrix.toLin' g.val ∘ fun j => (basisMat W)ᵀ j :=
      funext (mul_transpose_apply g (basisMat W))
    have l : LinearIndependent E (fun j => (g.val * basisMat W)ᵀ j) :=
      e ▸ (basisMat_linearIndependent W).map' _ (ker_toLin'_eq_bot g)
    exact l
  have hspan : Submodule.span E (Set.range (g.val * basisMat W)ᵀ) = img g W := by
    have e : Set.range (g.val * basisMat W)ᵀ = Matrix.toLin' g.val '' Set.range (basisMat W)ᵀ :=
      Set.ext fun y => ⟨fun ⟨j, hj⟩ => ⟨(basisMat W)ᵀ j, ⟨j, rfl⟩,
          (mul_transpose_apply g (basisMat W) j).symm.trans hj⟩,
        fun ⟨_, ⟨j, hj⟩, hy⟩ => ⟨j, (mul_transpose_apply g (basisMat W) j).trans (hj ▸ hy)⟩⟩
    rw [e, ← Submodule.map_span, span_basisMat]
    rfl
  have key := h E n (Fin (Module.finrank E W)) (ratGL E n g * x) (g.val * basisMat W) hli
  rw [hspan] at key
  rw [← key, degG_rat]
  rfl

end GlobalTheory.CompanionTheory.Degree

end
