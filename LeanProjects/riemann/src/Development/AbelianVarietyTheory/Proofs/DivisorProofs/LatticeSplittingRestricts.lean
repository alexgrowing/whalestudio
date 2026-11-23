import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsTop
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BplusDescent

theorem splits_restrict : ∀ (X : Scheme.{0}) [IsIntegral X] (U V : AffOp X) (hle : V.1 ≤ U.1) (h n : ℕ) (L : Submodule U.Bp (Fin h → U.Bp)) (L' : Submodule V.Bp (Fin h → V.Bp)) (g : Fin n → Fin h → U.Bp) (S : Fin n → Fin h → Kbar X), L' = Submodule.span V.Bp (piMap (AffOp.res hle) (Fin h) '' (L : Set (Fin h → U.Bp))) → Splits U L g S → Splits V L' (fun k => piMap (AffOp.res hle) (Fin h) (g k)) S := by
  intro X _ U V hle h n L L' g S hL' hS
  obtain ⟨hg, hGS, hSL⟩ := hS
  refine ⟨fun k => ?_, fun i i' => ?_, fun v hv => ?_⟩
  · rw [hL']
    exact Submodule.subset_span ⟨g k, hg k, rfl⟩
  · exact hGS i i'
  · rw [hL'] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      intro k
      obtain ⟨r, hr⟩ := hSL w hw k
      exact ⟨AffOp.res hle r, hr⟩
    | zero =>
      intro k
      exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro k
      obtain ⟨a, ha⟩ := hx k
      obtain ⟨b, hb⟩ := hy k
      refine ⟨a + b, ?_⟩
      simp only [Pi.add_apply, AddMemClass.coe_add, mul_add, Finset.sum_add_distrib, ha, hb]
    | smul c x _ hx =>
      intro k
      obtain ⟨a, ha⟩ := hx k
      refine ⟨c * a, ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, MulMemClass.coe_mul, ha, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring

end GlobalTheory.BplusDescent
