import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.IntDThmB
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Kernel

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C

theorem IntDThmB_of (hI : IntAtD) (hC : ShapeCong) : IntDThmB := by
  intro K _ _ _ l linv ph d hF hu h1 hSh hd0 hd1 h2 O _ _ τ hE hB hN hA n m _ _ _ w hw δ hδ Th G hG hT
    H _ _ N0 N1 A u th Q2 hAx hth hu1 hQ0 hQ hlin x hx hdet TT colN p hp hp1 I nu1 nu2 size e1 e2 e3
  obtain ⟨J, hJ, hJe⟩ := hI K l linv ph d hF hu h1 hSh O τ hE hB hN hA n m w hw δ hδ Th G hG hT
  obtain ⟨sg, hsg, hsge⟩ := hC K n _ (jet l ph 2) th (fun j => τ (w j)) A (betaPair H N0 N1 u) Q2 h2
    (TwoKernelNormBounds.norm_mul_le_one_of_half _ _ _ hd0 hSh.1 hth) hAx (TwoKernelNormBounds.constantCoeff_betaPair H N0 N1 u)
    hQ0 hQ hlin J hJ
  rw [hJe, hsge]
  exact Formalism.DworkPowerSeriesWeights.thmB K ‖(d : K)‖ hd0 hd1 H N0 N1 (jet l ph 2) u hSh.1 hu1 sg hsg x hx hdet TT colN p
    hp hp1 I nu1 nu2 size e1 e2 e3

end Formalism.L2.Th1.G
