import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def cay {k r : ℕ} (X : B.Mat k r) : B.Mat k r := (1 + X) * (1 - X)⁻¹

def cayInv {k r : ℕ} (g : B.Mat k r) : B.Mat k r := (g - 1) * (g + 1)⁻¹

def LieBasis : Prop :=
  ∀ k r : ℕ, ∃ (d : ℕ) (L : (Fin d → ℝ) →L[ℝ] B.Mat k r) (M : B.Mat k r →L[ℝ] (Fin d → ℝ)),
    (∀ x, B.inLie k r (L x)) ∧ (∀ x, M (L x) = x) ∧ ∀ X, B.inLie k r X → L (M X) = X

def CayAlg : Prop :=
  ∀ k r : ℕ,
    (∀ X : B.Mat k r, B.inLie k r X → IsUnit (1 - X) → cay X ∈ B.GV k r ∧ IsUnit (cay X + 1) ∧ cayInv (cay X) = X) ∧
    ∀ g ∈ B.GV k r, IsUnit (g + 1) → B.inLie k r (cayInv g) ∧ IsUnit (1 - cayInv g) ∧ cay (cayInv g) = g

def GVGrp : Prop :=
  ∀ k r : ℕ, IsUnit ((1 : B.Mat k r) + 1) ∧ ∀ g₀ ∈ B.GV k r, g₀⁻¹ * g₀ = 1 ∧
    ∀ h ∈ B.GV k r, g₀ * h ∈ B.GV k r ∧ g₀⁻¹ * h ∈ B.GV k r ∧ g₀ * (g₀⁻¹ * h) = h

def CaySmooth : Prop :=
  ∀ (k r : ℕ) (g₀ : B.Mat k r),
    IsOpen {X : B.Mat k r | IsUnit (1 - X)} ∧ IsOpen {m : B.Mat k r | IsUnit (g₀⁻¹ * m + 1)} ∧
    ContDiffOn ℝ ∞ (fun X : B.Mat k r => g₀ * cay X) {X | IsUnit (1 - X)} ∧
    ContDiffOn ℝ ∞ (fun m : B.Mat k r => cayInv (g₀⁻¹ * m)) {m | IsUnit (g₀⁻¹ * m + 1)}

theorem gChart_of (hB : LieBasis) (hA : CayAlg) (hG : GVGrp) (hS : CaySmooth) : GChart := by
  intro k r
  obtain ⟨d, L, M, hL, hML, hLM⟩ := hB k r
  refine ⟨d, fun g₀ hg₀ => ?_⟩
  obtain ⟨hA1, hA2⟩ := hA k r
  obtain ⟨hOne, hGg⟩ := hG k r
  obtain ⟨hinv, hmul⟩ := hGg g₀ hg₀
  obtain ⟨hO1, hU1, hκs, hΦs⟩ := hS k r g₀
  refine ⟨{x | IsUnit (1 - L x)}, {m | IsUnit (g₀⁻¹ * m + 1)}, fun x => g₀ * cay (L x),
    fun m => M (cayInv (g₀⁻¹ * m)), hO1.preimage L.continuous, hU1, ?_, ?_, ?_, ?_, ?_⟩
  · show IsUnit (g₀⁻¹ * g₀ + 1)
    rw [hinv]; exact hOne
  · exact hκs.comp L.contDiff.contDiffOn (fun x hx => hx)
  · exact M.contDiff.comp_contDiffOn hΦs
  · intro x hx
    obtain ⟨hc, hc1, hci⟩ := hA1 (L x) (hL x) hx
    have e : g₀⁻¹ * (g₀ * cay (L x)) = cay (L x) := by
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    refine ⟨(hmul _ hc).1, ?_, ?_⟩
    · show IsUnit (g₀⁻¹ * (g₀ * cay (L x)) + 1)
      rw [e]; exact hc1
    · show M (cayInv (g₀⁻¹ * (g₀ * cay (L x)))) = x
      rw [e, hci, hML]
  · intro g hg hgG
    obtain ⟨-, hh, hgh⟩ := hmul g hgG
    obtain ⟨hl, hu, hc⟩ := hA2 _ hh hg
    refine ⟨?_, ?_⟩
    · show IsUnit (1 - L (M (cayInv (g₀⁻¹ * g))))
      rw [hLM _ hl]; exact hu
    · show g₀ * cay (L (M (cayInv (g₀⁻¹ * g)))) = g
      rw [hLM _ hl, hc, hgh]

def IsDomOmPlus : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' →
    Q.IsDom k r z z' 0 (Q.OmPlus k r z z')

def RightTypeAction0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wq]
    (k r m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (mm : ℕ∞), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    IsCRepOn (UWset k r z') π' → ContinuousOn π' (UWset k r z') →
    ∀ J ∈ Gr.FFlM mm k r z z' π π' 0 D, ∀ g ∈ Q.Glev k r 0 ∩ D,
    ∀ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z'] Bs → ∀ (w : ℂ) (v : Wq),
      Q.capR k r Bs w J g v = J g (Q.capRep k r π' Bs w v)

def LeftTypeAction0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp]
    (k r m : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (mm : ℕ∞), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    IsCRepOn (UWset k r z) π → ContinuousOn π (UWset k r z) →
    ∀ J ∈ Gr.FFlM mm k r z z' π π' 0 D, ∀ g ∈ Q.Glev k r 0 ∩ D,
    ∀ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs → ∀ (w : ℂ) (v : Wq),
      Q.capLft k r Bs w J g v = Q.capRep k r π Bs w (J g v)

theorem uCap_of (h0 : IsDomOmPlus) (hR : RightTypeAction0) (hL : LeftTypeAction0) : UCap := by
  intro k r Wp Wq _ _ _ _ _ _ D u u' J hT hT' hF
  have hD := h0 k r D.z D.z' D.z_mem D.z'_mem
  have hg0 : ∀ g ∈ JF.Om k r D.z D.z', g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r D.z D.z' :=
    fun g hg => ⟨⟨hg.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hg.2⟩
  refine ⟨fun Bs hBs w => ⟨∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ)), fun g hg => ?_⟩,
    fun Bs hBs w => ⟨∏ i ∈ Finset.Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u' i : ℂ)), fun g hg => ?_⟩⟩
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [hL Wp Wq k r k D.z D.z' D.π D.π' _ _ D.z_mem D.z'_mem hD hT.2.1 hT.2.2.1 J hF g (hg0 g hg) Bs hBs w v,
      hT.2.2.2.2.2 Bs hBs w (J g v)]
    rfl
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [hR Wp Wq k r k D.z D.z' D.π D.π' _ _ D.z_mem D.z'_mem hD hT'.2.1 hT'.2.2.1 J hF g (hg0 g hg) Bs hBs w v,
      hT'.2.2.2.2.2 Bs hBs w v, map_smul]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
