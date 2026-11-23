import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.weLoc :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F) (w : P E), Gd D.δ v → Inert D v w →
      ∃ χ : Kv w → ℂ, Good χ ∧ ∀ x, ∃ u t, sg w x = D.mkE u t ∧ ψ (-(2 * u)) = χ x := by
  intro F E _ _ _ _ _ D v w hG hI
  obtain ⟨e, h1, h2, h3, -⟩ := hI.coord
  obtain ⟨sa, sm, sc, -⟩ := sgLaws F v
  obtain ⟨-, tm, tc, -⟩ := sgLaws E w
  obtain ⟨ga, gi, gm⟩ := hG.psi
  have hs : ∀ u, -(2 * sg v u) = sg v (-(2 * u)) := fun u => by
    rw [← neg_mul, sm, map_neg, map_ofNat, neg_mul]
  have s0 : sg v (0 : Kv v) = 0 := by simpa using (sm 0 0).symm
  have h4 : ∀ c u t, e (0, c) * e (u, t) = e (algebraMap F (Kv v) D.δ * (c * t), c * u) := fun c u t => by
    have a1 : ∀ x y, sg v (x * y) = sg v x * sg v y := fun x y => by rw [sm, sc]
    have a2 : ∀ x, sg v (algebraMap F (Kv v) D.δ * x) = rt D.δ * sg v x := fun x => (sm (rt D.δ) x).symm
    have a3 : (rt D.θ : A E) ^ 2 = AdeleBaseChange.adeleMap F E (rt D.δ) := by
      rw [← map_pow, D.sq]
      exact (AdeleBaseChange.adeleMap_algebraMap _).symm
    have : sg w (e (0, c) * e (u, t)) = sg w (e (algebraMap F (Kv v) D.δ * (c * t), c * u)) := by
      rw [← tc (e (0, c)), ← tm, h1, h1, h1, s0, a2, a1, a1]
      simp only [Dat.mkE, map_mul, map_zero, ← a3]
      ring
    simpa only [tc] using congrArg (cp w) this
  have key : ∀ y : Kv v, (∀ c, IsInt c → ψ (sg v (-(2 * (c * y)))) = 1) → IsInt y := fun y hy => by
    have : Valued.v (-(2 * y)) ≤ 1 := gm _ fun c hc => by
      have := hy c hc
      rwa [show -(2 * (c * y)) = c * -(2 * y) by ring] at this
    rwa [Valuation.map_neg, map_mul, hG.two, one_mul] at this
  refine ⟨fun x => ψ (sg v (-(2 * (e.symm x).1))), ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩, fun x => ?_⟩
  · beta_reduce
    rw [map_add, Prod.fst_add, mul_add, neg_add]
    exact ga _ _
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have hu : Valued.v u ≤ 1 := (le_max_left _ _).trans ((h2 u t).symm.le.trans hx)
    beta_reduce
    rw [e.symm_apply_apply]
    refine gi _ ?_
    show Valued.v _ ≤ 1
    rwa [Valuation.map_neg, map_mul, hG.two, one_mul]
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have hu : IsInt u := key u fun c hc => by
      have := hx (e (c, 0)) ((h2 c 0).le.trans (max_le hc (by simp)))
      beta_reduce at this
      rwa [h3, e.symm_apply_apply] at this
    have ht : Valued.v (algebraMap F (Kv v) D.δ * t) ≤ 1 := key _ fun c hc => by
      have := hx (e (0, c)) ((h2 0 c).le.trans (max_le (by simp) hc))
      beta_reduce at this
      rwa [h4, e.symm_apply_apply, mul_left_comm _ c t] at this
    rw [map_mul, hG.del, one_mul] at ht
    exact (h2 u t).le.trans (max_le hu ht)
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    exact ⟨_, _, h1 u t, by beta_reduce; rw [hs, e.symm_apply_apply]⟩
