import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsGeneratorRatioEqOneOfUnitFrameMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyLiftsToLatticeMapScalingForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaValueIdentityUnitFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaTraceValuesAtComplexPoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSimilitudeTriangularPeriodsOfHeckePoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfFlagOfHermFormPreserving
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
noncomputable section

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeLiftScalar

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.MoveValues GlobalTheory.HeckeValues

set_option maxHeartbeats 1000000 in

theorem hkPtC_values_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (p : ℕ) (y z : FrPt Xo c (CAt σ)) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)),
  HkPtC p y C z →
  ∃ (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk y.x ⟶ Xo.univ.t.G) →* (Over.mk z.x ⟶ Xo.univ.t.G)) (n : ℕ)
    (cr : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk y.x ⟶ Xo.univ.t.G) → ℂ),
    @IsHkIsog E _ _ _ H Dw l Xo (CAt σ) (fieldCAt σ) (algClosedCAt σ) p y.x z.x C ψ ψp ∧
    (∀ τ j, @IsLieImageH E _ _ _ H Dw l Xo (CAt σ) (fieldCAt σ) p y.x z.x ψ (y.u τ j) (z.u τ j)) ∧ GlobalTheory.ThetaTrace.IsRepsModTors C p cr ∧
    (∀ i j (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) ∧
    (∀ i j i' j' (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
      ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
        valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) ∧
    (∀ i j, ⊤ ≤ (1 : Over.mk z.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      ⊤ ≤ (1 : Over.mk y.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' z.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
        b i j 1 * valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    (∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y.x ⟶ Xo.univ.t.G)), IsHolTo Set.univ (fun w => (e w).left) →
      ∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
        {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ (a : Over.mk y.x ⟶ Xo.univ.t.G) i (jm : Fin n → Xo.univ.t.PP.L.ι), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      (∀ m, ⊤ ≤ ((cr m * a) ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U (jm m)) →
      valAt' (lift (𝟙 (Over.mk z.x)) (ψp a)).left ((PPx z.x).U (fun _ => i)) (z.s.f (fun _ => i)) =
        ∑ m, b i (jm m) (cr m * a) *
          valAt' (lift (𝟙 (Over.mk y.x)) ((cr m * a) ^ p)).left ((PPx y.x).U (fun _ => jm m)) (y.s.f (fun _ => jm m))) := by
  intro E _ _ _ H Dw l Xo c σ p y z C hk
  letI := fieldCAt σ
  haveI := algClosedCAt σ
  obtain ⟨ψ, ψp, hiso, hL, htr⟩ := hk
  obtain ⟨β, s₁, n, cr, hβ, hs, hr, hv⟩ := isThetaTrace_iff.1 htr
  obtain ⟨β₀, hβ₀, hc₀⟩ := hs.exists_isRigIso
  have hK := transKer_of_isHkIsog hiso
  have hΨ : ∀ a, rpt a ≫ conj y.x z.x ψ = rpt (ψp a) := fun a => (sends_conj_iff ψ _ _).2 (hiso.2.2.1 a)
  refine ⟨ψ, ψp, n, cr, fun i j a => bv Xo.univ.t.PP β β₀ i j a, hiso, hL, hK ▸ hr, fun i j a _ _ => bv_ne i j a,
    fun i j i' j' a hi hj => ?_, fun i j hi hj => ?_, fun g e he i j => ?_, fun a i jm hi hj => ?_⟩
  · have mi := (mem_iff _ _).2 hi
    have mj := (mem_iff _ _).2 hj
    exact bv_trans hβ.2.1 hβ₀.2.1 a (ψp a) (hΨ a) mi.1 mi.2 mj.1 mj.2
  · have h1 : rpt (1 : Over.mk y.x ⟶ Xo.univ.t.G) ≫ conj y.x z.x ψ = rpt (1 : Over.mk z.x ⟶ Xo.univ.t.G) := by
      exact (hΨ 1).trans (congrArg (fun q => rpt q) (map_one ψp))
    exact bv_rig hβ hβ₀ h1 i j ((mem_iff _ _).2 hi) ((mem_iff _ _).2 hj)
  · have hfun : (fun w => rpt (e w)) = fun w => fibPt Xo.univ.t.G (e w) ≫ (swap y.x).inv :=
      funext fun w => (Iso.eq_comp_inv _).2 (fibPt_swap (e w))
    have hh : IsHolTo Set.univ (fun w => rpt (e w)) := by
      rw [hfun]
      exact (GlobalTheory.HolFibre.isHolTo_fibPt_and_comp _ Xo.univ.t.G y.x g e he).2 _ (swap y.x).inv
    exact bv_hol hβ.2.1 hβ₀.2.1 ψp hΨ e hh i j
  · exact bv_values hβ.2.1 hβ₀.2.1 hc₀ cr (fun m => hr.1 m) hv a (ψp a) (hΨ a) i jm ((mem_iff _ _).2 hi)
      (fun m => (mem_iff _ _).2 (hj m))

end GlobalTheory.HeckeLiftScalar
