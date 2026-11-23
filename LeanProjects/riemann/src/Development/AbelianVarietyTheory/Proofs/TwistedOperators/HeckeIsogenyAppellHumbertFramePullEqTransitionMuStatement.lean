import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyAppellHumbertFramePullEqTransitionMu
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyLiftsToLatticeMapScalingForms
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIsogeny_appellHumbertFrame_pull_eq_transition_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (yx zx : Sp ℂ ⟶ Xo.X) (p : ℕ)
  (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ)
  (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk zx ⟶ Xo.univ.t.G))
  (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
  Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
  IsHolTo Set.univ (fun w => (e w).left) → IsHolTo Set.univ (fun w => (e' w).left) →
  (∀ w w', e (w + w') = e w * e w') → (∀ a ∈ Λ, e a = 1) → (∀ w, e' (h w) = ψp (e w)) →
  (∀ a ∈ Λ, h a ∈ Λ') →
  (∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) →
  (∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
    ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
    b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
      valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) →
  (∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
    ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
      b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
  (∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
    {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    Hm.IsHermitian →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (e z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (e 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ, ∀ j z, ‖χl a‖ = 1 ∧ (⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl a * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * fr j (z + a))) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j j' z, ⊤ ≤ (e' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (e' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (e' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ', ∀ j z, ‖χl' a‖ = 1 ∧ (⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' a * Complex.exp (Real.pi * hermForm Hm' z a + Real.pi / 2 * hermForm Hm' a a) * fr' j (z + a))) →
  ∀ w i j, ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    fr' i (h w) = b i j (e w) * fr j ((p : ℂ) • w) := by
  first | exact @GlobalTheory.HeckeEx.frame_pull_eq_transition_mul | exact GlobalTheory.HeckeEx.frame_pull_eq_transition_mul | (intros; apply GlobalTheory.HeckeEx.frame_pull_eq_transition_mul <;> assumption)
