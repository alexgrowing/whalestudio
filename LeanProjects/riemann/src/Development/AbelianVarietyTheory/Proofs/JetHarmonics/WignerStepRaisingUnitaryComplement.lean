import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameExtension
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Jets.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OpNormSumSmulSqLe
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HypAndAdj
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PieriRaisingSubmoduleGlSuccStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsTypeOfIrreducibleStable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoefHasDerivAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTensorStandardRep
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.WigSh

theorem adjoint_eval_subspace {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {k : ℕ} (S : Submodule ℂ (PiLp 2 (fun _ : Fin k => V))) (c : Fin k) (v : V) :
    ContinuousLinearMap.adjoint
        ((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin k => V) c).comp S.subtypeL) v
      = S.orthogonalProjectionOnto (PiLp.single 2 c v) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right, Submodule.inner_orthogonalProjection_eq_of_mem_left,
    PiLp.inner_apply, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [PiLp.single_eq_of_ne, hb]
  · simp

theorem wigner_step_raise : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n r : ℕ) (z : (Fin (2 * r + (n + 1) + 1) → ℂ)) (π : Mx (n + 1) r → (V →L[ℂ] V)) (u : ℕ → ℝ) (β : ℂ) (L : Fin (n + 1) → ℤ) (B : Fin (n + 1) → (Fin (2 * r + (n + 1) + 1) → ℂ)) (l : Fin (n + 1)), inWb (n + 1) r z → 0 < Tz (n + 1) r z → IsType (n + 1) r z π u → StrictAnti L → (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) → IsFrameOf (n + 1) r [z] B → (∀ j, L j ≠ L l + 1) → ∃ (V₂ : Type) (_ : NormedAddCommGroup V₂) (_ : InnerProductSpace ℂ V₂) (_ : FiniteDimensional ℂ V₂) (π₂ : Mx (n + 1) r → (V₂ →L[ℂ] V₂)) (A : (Fin (2 * r + (n + 1) + 1) → ℂ) → (V₂ →L[ℂ] V)), IsType (n + 1) r z π₂ (Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + 1)) ∧ GlobalTheory.WigSh.WigMap (n + 1) r z π₂ π 1 A ∧ ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA (EB π B)) (shf β M) → A (B (Fin.last n)) (ContinuousLinearMap.adjoint (A (B (Fin.last n))) v) = ((GlobalTheory.WigSh.wP L M l : ℝ) : ℂ) • v := by
  intro V _ _ _ n r z π u β L B l hz hT hπ hL hu hB hl
  obtain ⟨hH, hadj⟩ := GlobalTheory.TypeGlModule.hyp_and_adj V n r z π u β L B hz hT hπ hL hu hB
  have hrep : IsRepW (n + 1) r z π := ⟨hπ.2.1, hπ.2.2.1⟩
  obtain ⟨πt, ht1, ht2, ht3⟩ :=
    GlobalTheory.exists_tensor_standard_rep V (n + 1) r z π B hz hT hrep hπ.2.2.2.1 hB
  have hE := GlobalTheory.TensorStd.EB_tensor_std V (n + 1) r z π B πt hz hT hrep ht1 hB ht3
  obtain ⟨S, hS1, hS2, hS3, hS4, hS5⟩ := GlobalTheory.T.pieri_raising_submodule_glSucc V n (EB π B) (EB πt B) β L l hH hadj hE hl
  have hq : ∀ (w : ℂ), ∀ y ∈ S, qdet (EB πt B) w y = (∏ i ∈ Finset.Icc 1 (n + 1),
      (w - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 +
        ((Function.update u ((l : ℕ) + 1) (u ((l : ℕ) + 1) + 1) i : ℝ) : ℂ))) • y := by
    intro w y hy
    have h1 := hS4 hy
    unfold CapSp at h1
    rw [Submodule.mem_iInf] at h1
    have h2 := h1 w
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply] at h2
    rw [h2, Formalism.FourierDecayAlt.P.FrameExtension.prod_Icc_fin]
    congr 1
    unfold cpol shf
    refine Finset.prod_congr rfl fun j _ => ?_
    have hj := hu j
    by_cases hjl : j = l
    · subst hjl
      simp only [Function.update_self]
      push_cast at hj ⊢
      linear_combination -hj
    · have hne : (j : ℕ) + 1 ≠ (l : ℕ) + 1 := fun h => hjl (Fin.ext (by omega))
      rw [Function.update_of_ne hjl, Function.update_of_ne hne]
      linear_combination -hj
  obtain ⟨πS, hπS, hπS2⟩ := GlobalTheory.isType_of_irreducible_stable _ (n + 1) r z πt B S _ hz hT ht1 ht2 hB
    hS1 hS2 hS3 hq
  let a : Fin (n + 1) → (S →L[ℂ] V) := fun c =>
    (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin (n + 1) => V) c).comp S.subtypeL
  have ha : ∀ c (y : S), a c y = (y : PiLp 2 (fun _ : Fin (n + 1) => V)) c := fun c y => rfl
  obtain ⟨hW, hA⟩ := GlobalTheory.WigSh.ContrPlus.contraction_wigMap V (n + 1) r z π B S πS a hz hT hB
    (by
      intro y
      simp only [ha]
      rw [← PiLp.norm_sq_eq_of_L2]
      rfl)
    (by
      intro h hh y c
      simp only [ha]
      rw [hπS2 h hh y, ht3 h hh])
  refine ⟨S, inferInstance, inferInstance, inferInstance, πS, _, hπS, hW, ?_⟩
  intro M v hv
  simp only [hA]
  rw [ha, ← hS5 M v hv]
  simp only [a]
  rw [adjoint_eval_subspace]
  rfl

end GlobalTheory.WigSh
