import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordsBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.CechPic

namespace GlobalTheory.Mix

variable {k K : Type} [CommRing k] [CommRing K] {X G : Scheme.{0}} {p : X ⟶ Sp k} {q : G ⟶ Sp K} {j : G ⟶ X} {ρ : k →+* K}

def bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (z : CxPts q τ) : CxPts p (τ.comp ρ) := CxPts.bcMap w τ z

theorem bcPt_val (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (z : CxPts q τ) : (bcPt w τ z).1 = z.1 ≫ j := rfl

theorem continuous_bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) : Continuous (bcPt w τ) :=
  CxPts.continuous_of_comp (bcPt_val w τ)

theorem cInfAt_bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) {f : CxPts p (τ.comp ρ) → ℝ} {z : CxPts q τ}
    (h : CInfAt f (bcPt w τ z)) : CInfAt (fun y => f (bcPt w τ y)) z := by
  have hm : ∀ y, (bcPt w τ y).1 = y.1 ≫ j := bcPt_val w τ
  unfold CInfAt at h ⊢
  obtain ⟨W, ι, hι, g, F, O, hW, hO, hmem, hF, he⟩ := h
  refine ⟨j ⁻¹ᵁ W, ι, hι, fun a => j.app W (g a), F, O, (CxPts.mem_ptsIn_preimage hm).2 hW, hO, ?_, hF, ?_⟩
  · simpa only [CxPts.ev_of_comp hm] using hmem
  · filter_upwards [(continuous_bcPt w τ).continuousAt.tendsto.eventually he] with y hy
    simpa only [CxPts.ev_of_comp hm] using hy

def MLine.bc (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)) : MLine q τ where
  B := A.B.pull j
  φ := A.φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => bcPt w τ) fun _ _ => rfl
  cInf i z hz := (cInfAt_bcPt w τ (A.cInf _ _ (mem_of_mem_linComb (m := fun _ => bcPt w τ z)
    (fun _ => rfl) hz PUnit.unit))).congr (.of_forall fun y => by simp [Weight.linComb])

end GlobalTheory.Mix
