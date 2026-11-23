import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SgLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I

section

variable {F : Type} [Field F] [NumberField F] (v : P F)

private theorem cp_cont : Continuous (cp v) := by
  have h1 : Continuous (pLoc F v) :=
    RestrictedProduct.continuous_eval (R := fun v : P F => v.adicCompletion F) v
  have h2 : Continuous (pFin F) := continuous_snd
  exact h1.comp h2

private theorem cp_rt (c : F) : cp v (rt c) = algebraMap F (Kv v) c := rfl

private theorem cp_sg (x : Kv v) : cp v (sg v x) = x := (UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).2.2.1 x

private theorem sg_cp (a : A F) : sg v (cp v a) = a * sg v 1 := by
  rw [(UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).2.1 a 1, mul_one]

private theorem e_idem : sg v 1 * sg v 1 = sg v 1 := by
  rw [← sg_cp v (sg v 1), cp_sg]

private theorem away_eq (X : V4 F) (i : Fin 4) : away v X i = (1 - sg v 1) * X i := by
  change X i - sg v (cp v (X i)) = _
  rw [sg_cp]; ring

private theorem cp_away (X : V4 F) (i : Fin 4) : cp v (away v X i) = 0 := by
  change cp v (X i - sg v (cp v (X i))) = 0
  rw [map_sub, cp_sg, sub_self]

private theorem sg_add' (x y : Kv v) : sg v (x + y) = sg v x + sg v y :=
  (UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).1 x y

private theorem two_ne : (2 : Kv v) ≠ 0 := by
  intro h
  have h' : algebraMap F (Kv v) 2 = algebraMap F (Kv v) 0 := by
    rw [map_ofNat, map_zero]; exact h
  exact two_ne_zero ((algebraMap F (Kv v)).injective h')

end

end UpperTheory.ConvolutionTheory.R2.I

theorem UpperTheory.ConvolutionTheory.R2.I.matLaws :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F) (δ : F) (θ : Kv v), θ ^ 2 = algebraMap F (Kv v) δ → θ ≠ 0 →
      (∀ m : M2 v, ∃ y : V4 F, ∀ X, mat v θ (X + y) = mat v θ X + m ∧ away v (X + y) = away v X) ∧
      (∀ X Y, B4 δ Y X = B4 δ (away v Y) (away v X) + sg v (BM (mat v θ Y) (mat v θ X))) ∧
      (∀ b X, sg v b * q4 δ X = sg v (-(b * (mat v θ X).det))) ∧
      Continuous (mat v θ) ∧ Continuous (away v) ∧ (∀ X, away v (away v X) = away v X) ∧
      ∀ X, mat v θ (away v X) = 0 := by
  intro F _ _ v δ θ hθ hθ0
  have h2 := two_ne v
  have hc := cp_cont v
  have hs : Continuous (sg v) := (UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    refine ⟨![sg v (m 1 1), sg v (m 0 0), sg v ((m 0 1 + m 1 0) / 2), sg v ((m 0 1 - m 1 0) / (2 * θ))],
      fun X => ⟨?_, ?_⟩⟩
    · have e1 : (m 0 1 + m 1 0) / 2 + (m 0 1 - m 1 0) / (2 * θ) * θ = m 0 1 := by
        field_simp
        ring
      have e2 : (m 0 1 + m 1 0) / 2 - (m 0 1 - m 1 0) / (2 * θ) * θ = m 1 0 := by
        field_simp
        ring
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j
      · change cp v (X 1 + sg v (m 0 0)) = cp v (X 1) + m 0 0
        rw [map_add, cp_sg]
      · change cp v (X 2 + sg v ((m 0 1 + m 1 0) / 2)) +
            cp v (X 3 + sg v ((m 0 1 - m 1 0) / (2 * θ))) * θ = cp v (X 2) + cp v (X 3) * θ + m 0 1
        rw [map_add, map_add, cp_sg, cp_sg]
        linear_combination e1
      · change cp v (X 2 + sg v ((m 0 1 + m 1 0) / 2)) -
            cp v (X 3 + sg v ((m 0 1 - m 1 0) / (2 * θ))) * θ = cp v (X 2) - cp v (X 3) * θ + m 1 0
        rw [map_add, map_add, cp_sg, cp_sg]
        linear_combination e2
      · change cp v (X 0 + sg v (m 1 1)) = cp v (X 0) + m 1 1
        rw [map_add, cp_sg]
    · funext i
      change (X i + _) - sg v (cp v (X i + _)) = X i - sg v (cp v (X i))
      rw [map_add, sg_add']
      fin_cases i <;> simp [cp_sg] <;> ring
  · intro X Y
    have hB : BM (mat v θ Y) (mat v θ X) = cp v (B4 δ Y X) := by
      simp only [BM, mat, B4, map_sub, map_add, map_mul, cp_rt, ← hθ, map_ofNat]
      simp
      ring
    rw [hB, sg_cp]
    have he := e_idem v
    simp only [B4, away_eq]
    generalize sg v 1 = e at he
    generalize rt δ = d
    linear_combination (-(2 * (Y 2 * X 2 - d * (Y 3 * X 3)) - Y 1 * X 0 - Y 0 * X 1)) * he
  · intro b X
    have hq : -(b * (mat v θ X).det) = cp v (q4 δ X) * b := by
      simp only [mat, q4, Matrix.det_fin_two_of, map_sub, map_mul, map_pow, cp_rt, ← hθ]
      ring
    rw [hq, mul_comm, (UpperTheory.ConvolutionTheory.R2.H.sgLaws F v).2.1]
  · refine continuous_matrix fun i j => ?_
    have h : ∀ k : Fin 4, Continuous fun X : V4 F => cp v (X k) := fun k => hc.comp (continuous_apply k)
    fin_cases i <;> fin_cases j <;> simp [mat]
    · exact h 1
    · exact (h 2).add ((h 3).mul continuous_const)
    · exact (h 2).sub ((h 3).mul continuous_const)
    · exact h 0
  · refine continuous_pi fun i => ?_
    exact (continuous_apply i).sub (hs.comp (hc.comp (continuous_apply i)))
  · intro X
    funext i
    change away v X i - sg v (cp v (away v X i)) = _
    rw [cp_away]
    have : sg v 0 = 0 := by
      have := sg_add' v 0 0
      simpa using this
    rw [this, sub_zero]
  · intro X
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mat, cp_away]
