import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.GenV
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.stdOm :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (v : P F), Gd D.δ v → ∀ (k : G1 F), IntAt v k → ∀ φ : S4 F, Std v φ.1 → Std v (W.Om k φ).1 := by
  intro F E _ _ _ _ _ _ _ D W v hG k hk
  obtain ⟨sa, sm, sc, -⟩ := sgLaws F v
  obtain ⟨ga, gi, gm⟩ := hG.psi
  have s0 : sg v (0 : Kv v) = 0 := by simpa using (sm 0 0).symm
  have pa : ∀ x y : A F, ψ (x + y) = ψ x * ψ y := fun x y => by simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]
  have im : ∀ {x y : Kv v}, IsInt x → IsInt y → IsInt (x * y) := fun hx hy => by
    show Valued.v _ ≤ 1
    rw [map_mul]
    exact mul_le_one' hx hy
  have ia : ∀ {x y : Kv v}, IsInt x → IsInt y → IsInt (x + y) := fun hx hy => Valuation.map_add_le _ hx hy
  have ineg : ∀ {x : Kv v}, IsInt x → IsInt (-x) := fun hx => (Valuation.map_neg _ _).le.trans hx
  have i2 : IsInt (2 : Kv v) := hG.two.le
  have iδ : IsInt (cp v (rt D.δ)) := hG.del.le
  have k1 : ∀ (a : A F) y, IsInt (cp v a) → IsInt y → ψ (a * sg v y) = 1 := fun a y ha hy => by
    rw [sm]
    exact gi _ (im ha hy)
  have k2 : ∀ a : A F, (∀ c, IsInt c → ψ (a * sg v c) = 1) → IsInt (cp v a) := fun a h => gm _ fun c hc => by
    have := h c hc
    rwa [sm, mul_comm] at this
  have hn : ∀ b, IsInt (cp v b) → ∀ φ : S4 F, Std v φ.1 → Std v (W.Om (nU b) φ).1 := fun b hb φ hφ => by
    refine ⟨fun x hx => hφ.1 x fun e => hx (by rw [W.Om_n, e, mul_zero]), fun x y hy => ?_⟩
    rw [W.Om_n, W.Om_n, hφ.2 x y hy]
    by_cases h0 : φ.1 x = 0
    · rw [h0, mul_zero, mul_zero]
    have hx := hφ.1 x h0
    have e : b * q4 D.δ (fun i => x i + sg v (y i)) = b * q4 D.δ x + b * (2 * x 2 + sg v (y 2)) * sg v (y 2) +
        -(b * (rt D.δ * (2 * x 3 + sg v (y 3)))) * sg v (y 3) + -(b * x 1) * sg v (y 0) + -(b * (x 0 + sg v (y 0))) * sg v (y 1) := by
      simp only [q4]
      ring
    rw [e, pa, pa, pa, pa, k1 _ _ _ (hy 2), k1 _ _ _ (hy 3), k1 _ _ _ (hy 0), k1 _ _ _ (hy 1), mul_one, mul_one, mul_one, mul_one]
    all_goals simp only [map_neg, map_mul, map_add, map_ofNat, sc]
    · exact ineg (im hb (ia (hx 0) (hy 0)))
    · exact ineg (im hb (hx 1))
    · exact ineg (im hb (im iδ (ia (im i2 (hx 3)) (hy 3))))
    · exact im hb (ia (im i2 (hx 2)) (hy 2))
  have hw : ∀ φ : S4 F, Std v φ.1 → Std v (W.Om (wW F) φ).1 := fun φ hφ => by
    refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
    · rw [W.Om_w] at hx
      have h1 : ∀ y : Fin 4 → Kv v, (∀ i, IsInt (y i)) → ψ (B4 D.δ (fun i => sg v (y i)) x) = 1 := fun y hy => by
        have h2 := integral_add_right_eq_self (μ := adeleMeasurePi F) (fun z : V4 F => φ.1 z * ψ (B4 D.δ z x)) (fun i => sg v (y i))
        have h3 : ∀ z : V4 F, φ.1 (z + fun i => sg v (y i)) * ψ (B4 D.δ (z + fun i => sg v (y i)) x) =
            ψ (B4 D.δ (fun i => sg v (y i)) x) * (φ.1 z * ψ (B4 D.δ z x)) := fun z => by
          have e : B4 D.δ (z + fun i => sg v (y i)) x = B4 D.δ z x + B4 D.δ (fun i => sg v (y i)) x := by
            simp only [B4, Pi.add_apply]
            ring
          rw [e, pa, show φ.1 (z + fun i => sg v (y i)) = φ.1 z from hφ.2 z y hy]
          ring
        simp only [h3, integral_const_mul] at h2
        exact mul_right_cancel₀ hx (h2.trans (one_mul _).symm)
      have h4 : ∀ (i : Fin 4) c, IsInt c → ψ (B4 D.δ (fun j => sg v ((Pi.single i c : Fin 4 → Kv v) j)) x) = 1 := fun i c hc =>
        h1 _ fun j => by
          by_cases e : j = i
          · subst e; simpa using hc
          · simp [Pi.single_eq_of_ne e, IsInt]
      have a0 := k2 (-x 0) fun c hc => by rw [← h4 1 c hc]; congr 1; simp [B4, s0, mul_comm]
      have a1 := k2 (-x 1) fun c hc => by rw [← h4 0 c hc]; congr 1; simp [B4, s0, mul_comm]
      have a2 := k2 (2 * x 2) fun c hc => by rw [← h4 2 c hc]; congr 1; simp [B4, s0]; ring
      have a3 := k2 (-(2 * (rt D.δ * x 3))) fun c hc => by rw [← h4 3 c hc]; congr 1; simp [B4, s0]; ring
      have d1 : Valued.v (cp v (rt D.δ)) = 1 := hG.del
      simp only [IsInt, map_neg, Valuation.map_neg, map_mul, map_ofNat, hG.two, d1, one_mul] at a0 a1 a2 a3
      intro i
      fin_cases i
      exacts [a0, a1, a2, a3]
    · rw [W.Om_w, W.Om_w]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      beta_reduce
      by_cases h0 : φ.1 z = 0
      · rw [h0, zero_mul, zero_mul]
      have hz := hφ.1 z h0
      have e : B4 D.δ z (fun i => x i + sg v (y i)) = B4 D.δ z x + 2 * z 2 * sg v (y 2) + -(2 * (rt D.δ * z 3)) * sg v (y 3) +
          -z 1 * sg v (y 0) + -z 0 * sg v (y 1) := by
        simp only [B4]
        ring
      rw [e, pa, pa, pa, pa, k1 _ _ _ (hy 2), k1 _ _ _ (hy 3), k1 _ _ _ (hy 0), k1 _ _ _ (hy 1), mul_one, mul_one, mul_one, mul_one]
      all_goals simp only [map_neg, map_mul, map_ofNat]
      · exact ineg (hz 0)
      · exact ineg (hz 1)
      · exact ineg (im i2 (im iδ (hz 3)))
      · exact im i2 (hz 2)
  have ml : ∀ (x y : G1 F) (i k : Fin 2), (x * y).1 i k = x.1 i 0 * y.1 0 k + x.1 i 1 * y.1 1 k := fun x y i k => by
    show (x.1 * y.1) i k = _
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  have hk' := genV F v k hk
  clear hk
  induction hk' using Subgroup.closure_induction'' with
  | one => intro φ hφ; simpa using hφ
  | mem x hx =>
    rcases hx with ⟨b, hb, rfl⟩ | rfl
    exacts [hn b hb, hw]
  | inv_mem x hx =>
    rcases hx with ⟨b, hb, rfl⟩ | rfl
    · have e : (nU b)⁻¹ = nU (-b) := inv_eq_of_mul_eq_one_right (by
        ext i k : 1
        rw [ml]
        fin_cases i <;> fin_cases k <;> simp [nU])
      rw [e]
      exact hn _ (by rw [map_neg]; exact ineg hb)
    · have e : (wW F)⁻¹ = wW F * (wW F * wW F) := inv_eq_of_mul_eq_one_right (by
        ext i k : 1
        simp only [ml]
        fin_cases i <;> fin_cases k <;> simp [wW])
      rw [e, map_mul, map_mul]
      exact fun φ hφ => hw _ (hw _ (hw _ hφ))
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact fun φ hφ => hx _ (hy _ hφ)
