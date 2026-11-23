import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbWords
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightAverageSmoothComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PartialBesselProperness

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem cutoff_exists {H : B.Mat k n → (Wq →L[ℂ] Wp)} (z z' : Fin (2 * n + k + 1) → ℂ) (i : ℕ) (hi : i ≤ n)
    (hL : ∀ g ∈ B.GV k n, Dmin k n z z' g ⟨i, by omega⟩ ≠ 0 → CapelliWordSumExpansion.Loc ⊤ H g) {Cs : Set (B.Mat k n)}
    (hS : ∀ g ∈ B.GV k n, g ∉ Cs → H g = 0) {c0 : ℂ} (hc0 : c0 ≠ 0) :
    ∃ Ht : B.Mat k n → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k n) Ht ∧ (∀ g ∈ B.GV k n, g ∉ Cs → Ht g = 0) ∧
      ∀ g ∈ B.GV k n, dist (Dmin k n z z' g ⟨i, by omega⟩) c0 < ‖c0‖ / 4 → Ht g = H g := by
  set l : Fin (n + 2) := ⟨i, by omega⟩ with hl
  have hc : 0 < ‖c0‖ := norm_pos_iff.mpr hc0
  obtain ⟨χD, ⟨hχs, -, -⟩, hχ1, hχsupp⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.bump_exists hc0
  have hDc : Continuous (fun g : B.Mat k n => Dmin k n z z' g l) :=
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' l).continuous
  refine ⟨fun g => χD (Dmin k n z z' g l) • H g, ?_, ?_, ?_⟩
  · intro g0 hg0
    by_cases hmem : Dmin k n z z' g0 l ∈ tsupport χD
    · have hne : Dmin k n z z' g0 l ≠ 0 := by
        intro h0
        have := (hχsupp _ hmem).1
        rw [h0, norm_zero] at this
        linarith
      obtain ⟨U, f', hU, hgU, hf', he⟩ := hL g0 hg0 hne
      refine ⟨U, fun g => χD (Dmin k n z z' g l) • f' g, hU, hgU, ?_, fun g hg hgG => ?_⟩
      · exact ((hχs.comp (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' l)).contDiffOn).smul hf'
      · show χD (Dmin k n z z' g l) • H g = χD (Dmin k n z z' g l) • f' g
        rw [he g hg hgG]
    · refine ⟨(fun g => Dmin k n z z' g l) ⁻¹' (tsupport χD)ᶜ, fun _ => 0,
        (isClosed_tsupport χD).isOpen_compl.preimage hDc, hmem, contDiffOn_const, fun g hg _ => ?_⟩
      show χD (Dmin k n z z' g l) • H g = 0
      rw [image_eq_zero_of_notMem_tsupport hg, zero_smul]
  · intro g hg hgC
    show χD (Dmin k n z z' g l) • H g = 0
    rw [hS g hg hgC, smul_zero]
  · intro g _ hd
    show χD (Dmin k n z z' g l) • H g = H g
    rw [hχ1 _ (le_of_lt hd), one_smul]

end Formalism.FourierDecayAlt.P.PartialBesselProperness
