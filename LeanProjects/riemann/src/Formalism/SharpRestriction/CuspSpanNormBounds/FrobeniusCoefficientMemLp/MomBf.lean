import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomTw
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionElement

open Matrix

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.LeviCoordinates

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]

theorem twT_mul_block_mul {h m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : WeylGroupFacts.block k r h) :
    twT k r * (h * m) = h * (twT k r * m * twTi k r) * twT k r := by
  rw [← Matrix.mul_assoc, twT_comm_block hh]
  simp only [Matrix.mul_assoc, twTi_mul_twT, Matrix.mul_one]

theorem bessel_twist (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (hone : σ 1 = 1)
    (hmul : ∀ x ∈ UH (Hpk k r), ∀ y ∈ UH (Hpk k r), σ (x * y) = (σ x).comp (σ y))
    (hiso : ∀ x ∈ UH (Hpk k r), ∀ v, ‖σ x v‖ = ‖v‖)
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {c : ℂ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (hB : IsBesselMapSm z (psi k r z c) σ π B) :
    IsBesselMapSm z (psi k r z (c * -Complex.I)) σ π (fun v => B (σ (twT k r) v)) := by
  have hsm : ∀ v ∈ smoothVecs (k := k) (r := r) σ, σ (twT k r) v ∈ smoothVecs (k := k) (r := r) σ :=
    fun v hv => smooth_vectors_translate σ hmul twT_mem_UH hv
  refine ⟨fun v hv w hw => ?_, fun a v hv => ?_, fun h hh m hm v hv => ?_, ?_⟩
  · show B (σ (twT k r) (v + w)) = B (σ (twT k r) v) + B (σ (twT k r) w)
    rw [map_add]; exact hB.1 _ (hsm v hv) _ (hsm w hw)
  · show B (σ (twT k r) (a • v)) = a • B (σ (twT k r) v)
    rw [map_smul]; exact hB.2.1 a _ (hsm v hv)
  · show B (σ (twT k r) (σ (h * m) v)) = psi k r z (c * -Complex.I) m • π h (B (σ (twT k r) v))
    have hhU : h ∈ UH (Hpk k r) := hh.1
    have hmU : m ∈ UH (Hpk k r) := hm.1
    have hm' := twT_conj_N hm
    have e1 : σ (twT k r) (σ (h * m) v) = σ (h * (twT k r * m * twTi k r)) (σ (twT k r) v) := by
      have a1 : σ (twT k r) (σ (h * m) v) = σ (twT k r * (h * m)) v := by
        rw [hmul _ twT_mem_UH _ (WeylGroupFacts.uh_mul hhU hmU)]; rfl
      have a2 : σ (h * (twT k r * m * twTi k r)) (σ (twT k r) v) =
          σ (h * (twT k r * m * twTi k r) * twT k r) v := by
        rw [hmul _ (WeylGroupFacts.uh_mul hhU hm'.1) _ twT_mem_UH]; rfl
      rw [a1, a2, twT_mul_block_mul (WeylGroupFacts.uw_block hh)]
    rw [e1, hB.2.2.1 h hh _ hm' _ (hsm v hv), twT_psi hz]
  · obtain ⟨C, Ws, hWs, hbd⟩ := hB.2.2.2
    refine ⟨C, Ws.map (List.map fun X => twTi k r * X * twT k r), ?_, fun v hv => ?_⟩
    · intro w hw X hX
      obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
      obtain ⟨X0, hX0, rfl⟩ := List.mem_map.1 hX
      exact lie_algebra_conj_mem twTi_mem_UH twT_mem_UH twTi_mul_twT (hWs w0 hw0 X0 hX0)
    · have h1 := hbd _ (hsm v hv)
      have e : ∀ w ∈ Ws, ‖dsigW (k := k) (r := r) σ w (σ (twT k r) v)‖ =
          ‖dsigW (k := k) (r := r) σ (w.map fun X => twTi k r * X * twT k r) v‖ := by
        intro w hw
        rw [derivative_word_translate σ hmul hone twTi_mem_UH twT_mem_UH twTi_mul_twT w (hWs w hw) v, hiso _ twT_mem_UH]
      rw [List.map_map]
      calc ‖B (σ (twT k r) v)‖ ≤ C * (Ws.map fun w => ‖dsigW (k := k) (r := r) σ w (σ (twT k r) v)‖).sum := h1
        _ = C * (Ws.map ((fun w => ‖dsigW (k := k) (r := r) σ w v‖) ∘ List.map fun X => twTi k r * X * twT k r)).sum := by
          congr 2
          exact List.map_congr_left e

end Formalism.MainNotions.S.Pv.Mom
