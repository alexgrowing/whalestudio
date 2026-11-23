import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularFramesOnSmoothCurves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntEmbCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriFrames
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_frames_on_smooth_curves : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) {A : Type}
    [CommRing A] (s : X ⟶ Sp A) (ε : 𝓞 E →+* A) (q : ℕ) [Fact q.Prime] {W Y : Scheme.{0}} (b : W ⟶ X) (a : W ⟶ Y)
    (n : ℕ) (L : ℕ → LB Y), (∀ m, (L m).IsLB) → GlobalTheory.TriFlag.TriFrames t s ε q b a n L →
    ∀ (k : Type) [Field k] [IsAlgClosed k] [CharP k q] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] [IsIntegral C],
      IsSmoothProjCurve k C → ∀ (g : C ⟶ W) (G : Over C) [GrpObj G] [IsSemiAbelian G] (i : OAct (𝓞 E) G)
      (φ : G.left ⟶ t.G.left), IsActPull i t.act (g ≫ b) φ → ∀ β : A →+* k, g ≫ b ≫ s = strHom k C ≫ spMap β →
      (∀ n' ≤ n, ∑ m ∈ Finset.range n', degLB k ((L m).pull (g ≫ a)) ∈ subDegs k (Lie G)) ∧
        deg k (lieSub i (scal C (β.comp ε))) = ∑ m ∈ Finset.range n, degLB k ((L m).pull (g ≫ a)) := by
  first | exact @GlobalTheory.TriFlag.deg_on_curve | exact GlobalTheory.TriFlag.deg_on_curve | (intros; apply GlobalTheory.TriFlag.deg_on_curve <;> assumption)
