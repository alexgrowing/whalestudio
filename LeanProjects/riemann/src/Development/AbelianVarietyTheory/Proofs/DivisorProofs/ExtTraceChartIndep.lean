import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn

set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm

theorem extTrace_midIn_indep {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n} (T : HermSeq A 1 1)
    (a b : T.κ) (i : A.ι) {v : V n} (hv : v ∈ chartSet T a i ∩ chartSet T b i) :
    extTrace (midIn T a i) v = extTrace (midIn T b i) v := by
  have hh := trans_eventually T a b i hv
  have e : midIn T b i =ᶠ[𝓝 v] fun w => chg (gIn T a b i w) (midIn T a i w) := hh.mono fun w hw => hw.2.2.1
  have hK : MContDiffAt 1 (midIn T a i) v := (isPosFrame_midIn T a i).isHermFrame.one hv.1
  have hp : ∀ᶠ x in 𝓝 v, (midIn T a i x).PosDef :=
    mem_of_superset ((isOpen_chartSet T a i).mem_nhds hv.1) fun x hx => (isPosFrame_midIn T a i).posDef x hx
  have hg := holo_gIn T a b i hv
  have hA : MContDiffAt 1 (gIn T a b i) v := hg.1.of_le (by norm_cast)
  have hA0 : ∀ η, mdbar (gIn T a b i) v η = 0 := hg.2.self_of_nhds
  have ht : ∀ᶠ x in 𝓝 v, (gIn T a b i x).toBlocks₂₁ = 0 := hh.mono fun w hw => hw.2.2.2.2
  have hu : IsUnit (gIn T a b i v).det := by
    have ha : (A.e i).symm v ∈ T.U a := hv.1.2
    have hb : (A.e i).symm v ∈ T.U b := hv.2.2
    have h1 : T.g a b ((A.e i).symm v) * T.g b a ((A.e i).symm v) = 1 := by
      rw [T.g_mul a b a _ ⟨⟨ha, hb⟩, ha⟩, T.g_self a _ ha]
    exact Matrix.isUnit_det_of_right_inverse h1
  rw [extTrace_congr e, extTrace_chg hK hp hA hu hA0 ht]

end GlobalTheory.SecForm
