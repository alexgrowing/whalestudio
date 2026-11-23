import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnFderiv

open Filter Topology

namespace GlobalTheory.HoloNormed

theorem contDiffAt_two_complex {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {W : Set E} {w : E}
    (hW : IsOpen W) (hw : w ∈ W) (hf : DifferentiableOn ℂ f W) : ContDiffAt ℂ 2 f w :=
  (contDiffOn_nat hW 2 hf).contDiffAt (hW.mem_nhds hw)

end GlobalTheory.HoloNormed
