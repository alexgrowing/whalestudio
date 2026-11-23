import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfDescentInvariantFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_of_descentInvariant_frames : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [QuasiCompact f] [Flat f] [Surjective f] (L : LB X), L.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ),
    (∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ s : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ,
      (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
        gm (𝟙 X) x _ (s i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (s j)) ∧
      ∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (pullback.fst f f) z _ (s i) * gm (𝟙 _) z _ (φ i j) = gm (pullback.snd f f) z _ (s j)) →
    ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  first | exact @GlobalTheory.LBDescent.exists_lb_of_invariant_frames | exact GlobalTheory.LBDescent.exists_lb_of_invariant_frames | (intros; apply GlobalTheory.LBDescent.exists_lb_of_invariant_frames <;> assumption)
