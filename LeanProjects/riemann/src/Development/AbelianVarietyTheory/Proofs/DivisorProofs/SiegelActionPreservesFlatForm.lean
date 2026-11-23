import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSymplecticTransformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoordsSymplecticPullbackFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionIsMulActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPeriodMapSimplyConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodFlatMapRealAnalyticStatement

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.UnivAction

theorem tauU_symPart_of_isSymm {g : ℕ} {A : Matrix (Fin g) (Fin g) ℂ} (h : A.IsSymm) :
    tauU (symPart A) = A := by
  ext i j
  simp only [tauU, symPart, Matrix.of_apply]
  rw [h.apply i j]
  ring

theorem riem_vecMul_sp {g : ℕ} (A : Sp g) (x y : Fl g) :
    riem (x ᵥ* A.mat) (y ᵥ* A.mat) = riem x y := by
  have hA : A.mat * J (Fin g) ℝ * A.matᵀ = J (Fin g) ℝ := SymplecticGroup.mem_iff.1 A.2
  rw [riem_eq_J, riem_eq_J, ← Matrix.mulVec_transpose A.mat y, Matrix.mulVec_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hA]

def symPartL (g : ℕ) : (Fin g → Fin g → ℂ) →L[ℂ] symMat g :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => symPart A
      map_add' := fun A B => by
        apply Subtype.ext; funext i j; simp only [symPart, Submodule.coe_add, Pi.add_apply]; ring
      map_smul' := fun c A => by
        apply Subtype.ext; funext i j
        simp only [symPart, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

theorem univAct : ∀ g : ℕ, ∀ γ : Sp g, Set.BijOn (actU γ) (cov (siegel g) g) (cov (siegel g) g) ∧
    DifferentiableOn ℂ (actU γ) (cov (siegel g) g) ∧
    (∀ P ∈ cov (siegel g) g, IsUnit (den γ (tauU P.1)) ∧ tauU (actU γ P).1 = moeb γ (tauU P.1) ∧
      flat tauU (actU γ P) = flat tauU P ᵥ* (γ⁻¹).mat ∧ pull (actU γ) (om0 tauU) P = om0 tauU P ∧
      (P.2 = 0 → (actU γ P).2 = 0)) := by
  intro g γ
  have hU := (GlobalTheory.T.siegel_period_map_simply_connected g).1
  have hO : IsOpen (cov (siegel g) g) := hU.1.prod isOpen_univ
  have hb := fun δ : Sp g => GlobalTheory.T.period_map_symplectic_transform hU δ
  have hgrp := GlobalTheory.T.siegel_action_is_mul_action g
  have hsym : ∀ δ : Sp g, ∀ s ∈ siegel g, tauU (symPart (moeb δ (tauU s))) = moeb δ (tauU s) :=
    fun δ s hs => tauU_symPart_of_isSymm ((hb δ).1.2.2 s hs).1
  have hmaps : ∀ δ : Sp g, Set.MapsTo (actU δ) (cov (siegel g) g) (cov (siegel g) g) := by
    intro δ P hP
    refine ⟨?_, Set.mem_univ _⟩
    show IsSiegel (tauU (symPart (moeb δ (tauU P.1))))
    rw [hsym δ P.1 hP.1]
    exact (hb δ).1.2.2 _ hP.1
  have hinv : ∀ P ∈ cov (siegel g) g, actU γ⁻¹ (actU γ P) = P := fun P hP => by
    rw [← hgrp.2 _ _ P hP, inv_mul_cancel, hgrp.1 P hP]
  have hinv' : ∀ P ∈ cov (siegel g) g, actU γ (actU γ⁻¹ P) = P := fun P hP => by
    rw [← hgrp.2 _ _ P hP, mul_inv_cancel, hgrp.1 P hP]
  have hbij : Set.BijOn (actU γ) (cov (siegel g) g) (cov (siegel g) g) := by
    refine ⟨hmaps γ, fun P hP Q hQ h => ?_, fun P hP => ⟨actU γ⁻¹ P, hmaps γ⁻¹ hP, hinv' P hP⟩⟩
    calc P = actU γ⁻¹ (actU γ P) := (hinv P hP).symm
      _ = actU γ⁻¹ (actU γ Q) := by rw [h]
      _ = Q := hinv Q hQ
  have hdiff : DifferentiableOn ℂ (actU γ) (cov (siegel g) g) := by
    have h1 : DifferentiableOn ℂ (fun P : Pt (symMat g) g => fun i j => moeb γ (tauU P.1) i j)
        (cov (siegel g) g) :=
      differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j =>
        ((hb γ).1.2.1 i j).comp differentiableOn_fst fun P hP => hP.1
    have h2 := ((symPartL g).differentiable.comp_differentiableOn h1).prodMk
      (differentiable_snd.comp_differentiableOn (hb γ).2.2)
    refine h2.congr fun P _ => ?_
    rfl
  have hflat : ∀ P ∈ cov (siegel g) g, flat tauU (actU γ P) = flat tauU P ᵥ* (γ⁻¹).mat :=
    fun P hP => by
      rw [← (GlobalTheory.T.flat_coords_symplectic_pullback_form hU γ P hP).1]
      show flatOf (tauU (symPart (moeb γ (tauU P.1)))) (P.2 ᵥ* (den γ (tauU P.1))⁻¹) =
        flatOf (moeb γ (tauU P.1)) (P.2 ᵥ* (den γ (tauU P.1))⁻¹)
      rw [hsym γ P.1 hP.1]
  have hfd : ∀ Q ∈ cov (siegel g) g, DifferentiableAt ℝ (flat tauU) Q := fun Q hQ =>
    ((GlobalTheory.T.period_flat_map_real_analytic hU).1 Q hQ).differentiableAt
  have hAd : ∀ P ∈ cov (siegel g) g, DifferentiableAt ℝ (actU γ) P := fun P hP =>
    (hdiff.differentiableAt (hO.mem_nhds hP)).restrictScalars ℝ
  let L : Fl g →L[ℝ] Fl g := LinearMap.toContinuousLinearMap (Matrix.vecMulLinear (γ⁻¹).mat)
  have hpull : ∀ P ∈ cov (siegel g) g, pull (actU γ) (om0 tauU) P = om0 tauU P := by
    intro P hP
    have hc : fderiv ℝ (flat tauU ∘ actU γ) P =
        (fderiv ℝ (flat tauU) (actU γ P)).comp (fderiv ℝ (actU γ) P) :=
      fderiv_comp P (hfd _ (hmaps γ hP)) (hAd P hP)
    have he : flat tauU ∘ actU γ =ᶠ[nhds P] ⇑L ∘ flat tauU :=
      Filter.eventually_of_mem (hO.mem_nhds hP) fun Q hQ => by
        simp only [Function.comp_apply, L, LinearMap.coe_toContinuousLinearMap',
          Matrix.vecMulLinear_apply, hflat Q hQ]
    have hL : fderiv ℝ (⇑L ∘ flat tauU) P = L.comp (fderiv ℝ (flat tauU) P) :=
      (L.hasFDerivAt.comp P (hfd P hP).hasFDerivAt).fderiv
    have key : ∀ w, fderiv ℝ (flat tauU) (actU γ P) (fderiv ℝ (actU γ) P w) =
        fderiv ℝ (flat tauU) P w ᵥ* (γ⁻¹).mat := by
      intro w
      have := congrArg (fun T : Pt (symMat g) g →L[ℝ] Fl g => T w)
        (hc.symm.trans (he.fderiv_eq.trans hL))
      simpa [L] using this
    ext v
    simp only [pull, om0, dflat, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    show riem _ _ = riem _ _
    simp only [Function.comp_apply, key]
    exact riem_vecMul_sp γ⁻¹ _ _
  refine ⟨hbij, hdiff, fun P hP => ⟨(hb γ).2.1 P.1 hP.1, hsym γ P.1 hP.1, hflat P hP, hpull P hP,
    fun h => ?_⟩⟩
  simp [actU, h]

end GlobalTheory.UnivAction
