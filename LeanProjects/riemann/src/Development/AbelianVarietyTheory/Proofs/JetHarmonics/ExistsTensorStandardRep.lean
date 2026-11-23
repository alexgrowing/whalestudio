import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameExpansionUwGroup

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

noncomputable section

namespace GlobalTheory.TensorStd

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {k : ℕ}

def tenOp (C : Fin k → Fin k → ℂ) (A : V →L[ℂ] V) :
    PiLp 2 (fun _ : Fin k => V) →L[ℂ] PiLp 2 (fun _ : Fin k => V) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => V)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun c => ∑ d, C c d • (A ∘L PiLp.proj 2 (fun _ : Fin k => V) d)

theorem tenOp_apply (C : Fin k → Fin k → ℂ) (A : V →L[ℂ] V) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    tenOp C A y c = ∑ d, C c d • A (y d) := by
  simp [tenOp]

private lemma inner_map_of_norm_eq (A : V →L[ℂ] V) (hA : ∀ v, ‖A v‖ = ‖v‖) (u w : V) :
    inner ℂ (A u) (A w) = inner ℂ u w :=
  (⟨A.toLinearMap, hA⟩ : V →ₗᵢ[ℂ] V).inner_map_map u w

theorem tenOp_norm (C : Fin k → Fin k → ℂ) (A : V →L[ℂ] V)
    (hC : ∀ d e, ∑ c, C c e * star (C c d) = if e = d then 1 else 0) (hA : ∀ v, ‖A v‖ = ‖v‖)
    (y : PiLp 2 (fun _ : Fin k => V)) : ‖tenOp C A y‖ = ‖y‖ := by
  have key : inner ℂ (tenOp C A y) (tenOp C A y) = inner ℂ y y := by
    simp only [PiLp.inner_apply, tenOp_apply, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, inner_map_of_norm_eq A hA]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ e, ∑ c, C c d * ((starRingEnd ℂ) (C c e) * inner ℂ (y e) (y d)) =
        (if d = e then 1 else 0) * inner ℂ (y e) (y d) := by
      intro e
      rw [← hC e d, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [Complex.star_def]
      ring
    simp only [hterm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), key]

end GlobalTheory.TensorStd

namespace GlobalTheory

open TensorStd

private lemma herm_sum_smul_left' {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m → ℂ)
    (w : Fin m → Fin n → ℂ) (u : Fin n → ℂ) :
    herm H (∑ c, a c • w c) u = ∑ c, a c * herm H (w c) u := by
  simp [herm, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul]

private lemma herm_sum_smul_right' {n m : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (a : Fin m → ℂ)
    (w : Fin m → Fin n → ℂ) (v : Fin n → ℂ) :
    herm H v (∑ c, a c • w c) = ∑ c, star (a c) * herm H v (w c) := by
  simp [herm, star_sum, sum_dotProduct, star_smul, smul_dotProduct]

theorem exists_tensor_standard_rep :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → IsRepW k r z π → (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) → IsFrameOf k r [z] B → ∃ πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V))), IsRepW k r z πt ∧ (∀ h ∈ UWset k r z, ∀ v, ‖πt h v‖ = ‖v‖) ∧ (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d)) := by
  intro V _ _ _ k r z π B hz hT hπ hiso hB
  obtain ⟨hcomp, hgrp⟩ := GlobalTheory.FrameExpansion.frame_expansion_uw_group k r z B hz hT hB

  have hexp : ∀ h ∈ UWset k r z, ∀ d,
      h *ᵥ B d = ∑ e, herm (Hpk k r) (h *ᵥ B d) (B e) • B e := by
    intro h hh d
    obtain ⟨h1, h2⟩ := (hgrp h hh).1 (B d) (hB.1 d) (hB.2.2 d z (List.mem_singleton_self z))
    exact hcomp _ h1 h2
  refine ⟨fun h => tenOp (fun c d => herm (Hpk k r) (h *ᵥ B d) (B c)) (π h), ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun y => PiLp.ext fun c => ?_
    rw [tenOp_apply, hπ.1.1]
    simp [hB.2.1]
  · intro a ha b hb
    refine ContinuousLinearMap.ext fun y => PiLp.ext fun c => ?_
    simp only [ContinuousLinearMap.comp_apply, tenOp_apply, hπ.1.2 a ha b hb, map_sum, map_smul,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    conv_lhs => rw [← Matrix.mulVec_mulVec, hexp b hb d, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    rw [herm_sum_smul_left']
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _
  · rw [continuousOn_clm_apply]
    intro y
    have hrepr : ∀ h, tenOp (fun c d => herm (Hpk k r) (h *ᵥ B d) (B c)) (π h) y =
        (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin k => V)).symm
          (fun c => ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d)) := by
      intro h
      exact PiLp.ext fun c => by rw [tenOp_apply]; rfl
    simp only [hrepr]
    refine (PiLp.continuousLinearEquiv 2 ℂ _).symm.continuous.comp_continuousOn ?_
    refine continuousOn_pi.2 fun c => continuousOn_finsetSum _ fun d _ => ?_
    refine ContinuousOn.smul ?_ (hπ.2.clm_apply continuousOn_const)
    exact Continuous.continuousOn (by unfold herm; fun_prop)
  · intro h hh y
    refine tenOp_norm _ _ (fun d e => ?_) (hiso h hh) y
    have hpres := (hgrp h hh).2.1 (B e) (B d)
    rw [hB.2.1 e d] at hpres
    rw [← hpres]
    conv_rhs => rw [hexp h hh d, herm_sum_smul_right']
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  · intro h hh y c
    exact tenOp_apply _ _ _ _

end GlobalTheory
