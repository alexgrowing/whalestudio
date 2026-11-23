import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.IntDThmBGauss
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Kernel

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C

theorem IntDThmBGauss_of (hI : IntAtD) (hC : ShapeCong) : IntDThmBGauss := by
  intro p _ l linv ph hF hu h1 hSh h2 O _ _ τ hE hB hN hA n m _ _ _ w hw δ hδ Th G hG hT
    H _ _ N0 N1 A u th Q2 hAx hth hu1 hQ0 hQ hlin TT colN ht hht hht1 I nu1 nu2 size e1 e2 e3 nn
  have hp0 : ((p : ℕ) : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨J, hJ, hJe⟩ := hI ℂ_[p] l linv ph p hF hu h1 hSh O τ hE hB hN hA n m w hw δ hδ Th G hG hT
  obtain ⟨sg, hsg, hsge⟩ := hC ℂ_[p] n _ (jet l ph 2) th (fun j => τ (w j)) A (betaPair H N0 N1 u) Q2 h2
    (TwoKernelNormBounds.norm_mul_le_one_of_half _ _ _ (norm_pos_iff.mpr hp0) hSh.1 hth) hAx
    (TwoKernelNormBounds.constantCoeff_betaPair H N0 N1 u) hQ0 hQ hlin J hJ
  rw [hJe, hsge]
  exact Formalism.DworkPowerSeriesWeights.thmBGauss p H N0 N1 (jet l ph 2) u hSh.1 hu1 sg hsg TT colN ht hht hht1 I nu1 nu2
    size e1 e2 e3 nn

end Formalism.L2.Th1.G
