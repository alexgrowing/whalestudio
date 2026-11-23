import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem goodPatch_image : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → IsOpen (e '' W) ∧ e '' (ptsIn X.str σ O ∩ W) = offHyp S (e '' W) ∧ ∀ K : Set (CxPts X.str σ), IsClosed K → K ⊆ W → IsCompact (e '' K) := by
  intro F _ σ X m E O H e S A W c h
  refine ⟨e.isOpen_image_of_subset_source h.isOpen h.sub, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨z, ⟨hO, hW⟩, rfl⟩
      exact ⟨⟨z, hW, rfl⟩, (h.mem z hW).1 hO⟩
    · rintro ⟨⟨z, hW, rfl⟩, hv⟩
      exact ⟨z, ⟨(h.mem z hW).2 hv, hW⟩, rfl⟩
  · intro K hK hKW
    haveI : CompactSpace (CxPts X.str σ) := CxPts.compactSpace σ X.isProjOver
    exact hK.isCompact.image_of_continuousOn (e.continuousOn.mono (hKW.trans h.sub))

end GlobalTheory.GoodTop
