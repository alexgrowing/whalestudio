import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.AdelicFunctionRightTranslateDiamond

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

def conjPt (S : StepLevel F E σ J T f bad) (δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U) :
    UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
  ⟨κ.1⁻¹ * δ.1 * κ.1, (UPts σ J _).mul_mem ((UPts σ J _).mul_mem ((UPts σ J _).inv_mem ((S.U_eq κ.1).1 κ.2).1) δ.2)
    ((S.U_eq κ.1).1 κ.2).1⟩

theorem conjPt_coe (S : StepLevel F E σ J T f bad) (δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U) :
    (conjPt S δ κ).1 = κ.1⁻¹ * δ.1 * κ.1 := rfl

set_option maxHeartbeats 4000000 in

theorem isDia_conj (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F))
    (hv : (T : 𝓞 F) ∈ v.asIdeal) {k : ℤ} {δ : UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    (h : IsDia S v hv k δ) (κ : S.U) : IsDia S v hv k (conjPt S δ κ) := by
  obtain ⟨h1, h2, hg, h3⟩ := h
  have hκ := (S.U_eq κ.1).1 κ.2
  have hk := hκ.2 v
  rw [S.UlocAlt v hv] at hk
  obtain ⟨hkL, hkF, hkf⟩ := hk
  have hgg : bc (prV (E := E) v) (conjPt S δ κ).1 ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v)
      (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) := by
    rw [conjPt_coe, map_mul, map_mul, map_inv]
    exact (stabGL _).mul_mem ((stabGL _).mul_mem ((stabGL _).inv_mem hkF) hg) hkF
  refine ⟨fun v' hv' => ?_, ?_, hgg, fun x => ?_⟩
  · rw [conjPt_coe, map_mul, map_mul, map_inv, h1 v' hv', mul_one, inv_mul_cancel]
  · rw [conjPt_coe, map_mul, map_mul, map_inv]
    exact (levelVL σ J v S.Lb).mul_mem ((levelVL σ J v S.Lb).mul_mem ((levelVL σ J v S.Lb).inv_mem hkL) h2) hkL
  · have hkFi := (stabGL _).inv_mem hkF
    have hy : (bc (prV (E := E) v) δ.1).1 *ᵥ ((bc (prV (E := E) v) κ.1).1 *ᵥ x.1) ∈
        latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) :=
      (hg _).1 ((hkF x.1).1 x.2)
    have e1 : (⟨(bc (prV (E := E) v) (conjPt S δ κ).1).1 *ᵥ x.1, (hgg x.1).1 x.2⟩ :
        latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) =
        ⟨((bc (prV (E := E) v) κ.1)⁻¹ : GL _ _).1 *ᵥ ((bc (prV (E := E) v) δ.1).1 *ᵥ ((bc (prV (E := E) v) κ.1).1 *ᵥ x.1)),
          (hkFi _).1 hy⟩ := by
      apply Subtype.ext
      simp only [conjPt_coe, map_mul, map_inv, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have e2 : S.fT v hv ⟨((bc (prV (E := E) v) κ.1)⁻¹ : GL _ _).1 *ᵥ
        ((bc (prV (E := E) v) δ.1).1 *ᵥ ((bc (prV (E := E) v) κ.1).1 *ᵥ x.1)), (hkFi _).1 hy⟩ =
        S.fT v hv ⟨_, hy⟩ := by
      rw [← hkf ⟨_, (hkFi _).1 hy⟩]
      congr 1
      apply Subtype.ext
      simp only [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]
    rw [e1, e2, h3 ⟨_, (hkF x.1).1 x.2⟩, hkf x]

end Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal

end
