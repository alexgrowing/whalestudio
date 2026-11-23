import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliVectorFrame
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorExpansion

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.TL

open TLC in
theorem capelli_vector_equivariance : TL.CapVEquiv := by
  intro Wq _ _ _ k r z' π' B0 ν ν' h hk hz hT hπ hB0 hν hh hνν' w
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨he, hez, hee⟩ := cap_vec hB0 hν
  set e := ∑ j, ν j • B0 j with hedef
  set g := h⁻¹ with hgdef
  have hg : g ∈ UWset (n + 1) r z' := LieBracketMultiplication.uw_inv hh
  have hgU : g ∈ UH (Hpk (n + 1) r) := hg.1
  have hgL : g ∈ Glev (n + 1) r (Fin.last r) := Qx8.uw_glev _ hg
  have hν' : C6.sq2 ν' = 1 := by
    have h1 : herm (Hpk (n + 1) r) (∑ j, ν' j • B0 j) (∑ j, ν' j • B0 j) = 1 := by
      rw [hνν', Qx2.herm_uh hgU, hee]
    rw [HermitianFormSums.herm_comb hB0] at h1
    have : ∀ a, ν' a * star (ν' a) = ((Complex.normSq (ν' a) : ℝ) : ℂ) := fun a => Complex.mul_conj (ν' a)
    simp only [this] at h1
    rw [← Complex.ofReal_sum] at h1
    exact_mod_cast h1
  obtain ⟨Bs, hBs⟩ := exists_frame_two n r z' e hz hT he hez hee
  set Bs' : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ := fun a => g *ᵥ Bs a with hBs'def
  have hBs' : IsFrameOf (n + 1) r [z', ∑ j, ν' j • B0 j] Bs' := by
    refine ⟨fun a => Qx8.inWb_mulVec hgL (hBs.1 a), fun a b => ?_, fun a v hv => ?_⟩
    · rw [hBs'def, Qx2.herm_uh hgU]; exact hBs.2.1 a b
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · have e1 := Qx2.herm_uh hgU (Bs a) v
        rw [hg.2.2] at e1
        rw [e1]; exact hBs.2.2 a _ (by simp)
      · rw [hνν', Qx2.herm_uh hgU]; exact hBs.2.2 a _ (by simp)
  have hF := capelli_vector_frame Wq (n + 1) r z' π' B0 Bs ν (by omega) hz hT hπ hB0 hν hBs w
  have hF' := capelli_vector_frame Wq (n + 1) r z' π' B0 Bs' ν' (by omega) hz hT hπ hB0 hν' hBs' w
  have hBs1 := HermitianFormSums.frame_sub hBs
  have hBs1' := HermitianFormSums.frame_sub hBs'
  have hq := (frame_general_linear Wq (n + 1) r n z' π' Bs hπ hBs1).2 w
  have hq' := (frame_general_linear Wq (n + 1) r n z' π' Bs' hπ hBs1').2 w
  have hgi : g⁻¹ = h := Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hh.1)
  have hgh : g * h = 1 := LeftDerivativeCurves.uh_inv_mul hh.1
  have hhg : h * g = 1 := LeftDerivativeCurves.uh_mul_inv hh.1
  have hUUi : (π' g).comp (π' h) = ContinuousLinearMap.id ℂ Wq := by
    rw [← hπ.1.2 _ hg _ hh, hgh, hπ.1.1]; rfl
  have hUiU : (π' h).comp (π' g) = ContinuousLinearMap.id ℂ Wq := by
    rw [← hπ.1.2 _ hh _ hg, hhg, hπ.1.1]; rfl
  set U : Module.End ℂ Wq := (π' g : Wq →ₗ[ℂ] Wq) with hU
  set Ui : Module.End ℂ Wq := (π' h : Wq →ₗ[ℂ] Wq) with hUi
  have hUUi' : U * Ui = 1 := by
    apply LinearMap.ext; intro v
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUUi
    simpa [hU, hUi] using this
  have hUiU' : Ui * U = 1 := by
    apply LinearMap.ext; intro v
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUiU
    simpa [hU, hUi] using this
  have hEB : ∀ a b, U * EB π' Bs a b * Ui = EB π' Bs' a b := by
    intro a b
    obtain ⟨hX1, hX2⟩ := QrD.frame_lie hBs1 a b
    obtain ⟨-, -, e1⟩ := differential_operator_adjoint Wq (n + 1) r z' π' hπ _ hX1 g hg
    obtain ⟨-, -, e2⟩ := differential_operator_adjoint Wq (n + 1) r z' π' hπ _ hX2 g hg
    obtain ⟨c1, c2⟩ := Qx8.hpart_conj Bs a b hgU
    unfold EB QrD.ecOp
    rw [c1, c2, e1, e2, hgi]
    apply LinearMap.ext; intro v
    simp [hU, hUi]
  let f : Module.End ℂ Wq →+* Module.End ℂ Wq :=
    { toFun := fun T => U * T * Ui
      map_one' := by simp only [mul_one, hUUi']
      map_mul' := fun S T => by
        show U * (S * T) * Ui = U * S * Ui * (U * T * Ui)
        calc U * (S * T) * Ui = U * S * (Ui * U) * T * Ui := by rw [hUiU']; noncomm_ring
          _ = U * S * Ui * (U * T * Ui) := by noncomm_ring
      map_zero' := by simp only [mul_zero, zero_mul]
      map_add' := fun S T => by noncomm_ring }
  have hf : ∀ v, f (algebraMap ℂ (Module.End ℂ Wq) v) = algebraMap ℂ (Module.End ℂ Wq) v := by
    intro v
    show U * algebraMap ℂ (Module.End ℂ Wq) v * Ui = _
    rw [← Algebra.commutes, mul_assoc, hUUi', mul_one]
  have hqd := QuantumMinorExpansion.map_qminor (EB π' Bs') f hf (EB π' Bs) (fun a b => hEB a b) id id w
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  rw [hF', hF, hq', hq]
  unfold qdet
  rw [← hqd]
  show U (qminor (EB π' Bs) id id w (Ui (π' h⁻¹ v))) = π' h⁻¹ (qminor (EB π' Bs) id id w v)
  have : Ui (π' h⁻¹ v) = v := by
    rw [← hgdef]
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUiU
    simpa [hUi] using this
  rw [this]
  rfl

end Formalism.FourierDecayAlt.P
