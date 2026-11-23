import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.WhTorus
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.HeckeExpl
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.FixTr
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma dL_mul {K : Type} [Field K] [NumberField K] {v : H.P K} (a d a' d' : (H.Kv v)ˣ) :
    H.dL a d * H.dL a' d' = H.dL (a * a') (d * d') := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H.dL, Matrix.mul_apply, Fin.sum_univ_two]

private lemma dL_one {K : Type} [Field K] [NumberField K] {v : H.P K} : (H.dL (1 : (H.Kv v)ˣ) 1) = 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H.dL]

private lemma dL_nL {K : Type} [Field K] [NumberField K] {v : H.P K} (a : (H.Kv v)ˣ) (b : H.Kv v) :
    H.dL a 1 * H.nL b = H.nL ((a : H.Kv v) * b) * H.dL a 1 := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H.dL, H.nL, Matrix.mul_apply, Fin.sum_univ_two]

private lemma hs_succ (a b : ℂ) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1 + 1), a ^ i * b ^ (k + 1 - i) =
      b * ∑ i ∈ Finset.range (k + 1), a ^ i * b ^ (k - i) + a ^ (k + 1) := by
  rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have : k + 1 - i = (k - i) + 1 := by
    have := Finset.mem_range.1 hi
    omega
  rw [this]
  ring

private lemma tor_loc (K : Type) [Field K] [NumberField K] (v : H.P K) (ϖ : (H.Kv v)ˣ) (hϖ : H.IsU ϖ)
    (χ : H.Kv v → ℂ) (hχ : H.Good χ) (α β : ℂˣ) (W : GL (Fin 2) (H.Kv v) → ℂ)
    (hW : UpperTheory.V.Af.Smo.Eig v {α, β} W) (hn : ∀ b y, W (H.nL b * y) = χ b * W y) (k : ℕ) :
    (H.q v ^ (1 / 2 : ℂ)) ^ k * W (H.dL (ϖ ^ k) 1) =
      (∑ i ∈ Finset.range (k + 1), ((α : ℂ)) ^ i * ((β : ℂ)) ^ (k - i)) * W 1 := by
  obtain ⟨R, hcard, hRint, hR⟩ := UpperTheory.ConvolutionTheory.R2.H.heckeExpl K v ϖ hϖ
  have hsum := fun g => (hR α β W hW g).1
  have hcen := fun g => (hR α β W hW g).2
  obtain ⟨t1, -⟩ := UpperTheory.ConvolutionTheory.R2.H.whTorus K v ϖ hϖ χ hχ α β W hW hn
  have hint : ∀ c : H.Kv v, H.IsInt c → ∀ y, W (H.nL c * y) = W y := fun c hc y => by
    rw [hn, hχ.2.1 c hc, one_mul]
  have hϖint : H.IsInt (ϖ : H.Kv v) := by
    have h' : Valued.v (ϖ : H.Kv v) = _ := hϖ
    show Valued.v (ϖ : H.Kv v) ≤ 1
    rw [h']
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) ≤ 1)
  have hq0 : H.q v ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    exact Nat.cast_ne_zero.2 this
  set s : ℂ := H.q v ^ (1 / 2 : ℂ) with hs
  have hss : s * s = H.q v := by
    rw [hs, ← Complex.cpow_add _ _ hq0]
    norm_num
  have hs0 : s ≠ 0 := fun h => hq0 (by rw [← hss, h, zero_mul])
  have hconst : ∀ x : ℂ, ∑ _b ∈ R, x = H.q v * x := fun x => by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    rfl
  have hrec : ∀ k : ℕ, s * ((α : ℂ) + β) * W (H.dL (ϖ ^ (k + 1)) 1) =
      H.q v * W (H.dL (ϖ ^ (k + 1 + 1)) 1) + (α : ℂ) * β * W (H.dL (ϖ ^ k) 1) := fun k => by
    have h2 := hsum (H.dL (ϖ ^ (k + 1)) 1)
    have t3 : ∀ b ∈ R, W (H.dL (ϖ ^ (k + 1)) 1 * H.nL b * H.dL ϖ 1) = W (H.dL (ϖ ^ (k + 1 + 1)) 1) := fun b hb => by
      rw [dL_nL, mul_assoc, hint _ ?_, dL_mul, mul_one, ← pow_succ]
      have hb' : ((ϖ : H.Kv v) ^ (k + 1)) * b ∈ v.adicCompletionIntegers K :=
        mul_mem (pow_mem (show (ϖ : H.Kv v) ∈ v.adicCompletionIntegers K from hϖint) _)
          (show b ∈ v.adicCompletionIntegers K from hRint b hb)
      rw [Units.val_pow_eq_pow_val]
      exact hb'
    rw [Finset.sum_congr rfl t3, hconst] at h2
    have t4 : W (H.dL (ϖ ^ (k + 1)) 1 * H.dL 1 ϖ) = (α : ℂ) * β * W (H.dL (ϖ ^ k) 1) := by
      have := hcen (H.dL (ϖ ^ k) 1)
      rw [dL_mul, one_mul, ← pow_succ] at this
      rw [dL_mul, mul_one, one_mul]
      exact this
    rw [t4] at h2
    exact h2
  have h3 : s * W (H.dL ϖ 1) = ((α : ℂ) + β) * W 1 := by
    refine mul_left_cancel₀ hs0 ?_
    rw [← mul_assoc, hss, ← mul_assoc]
    exact t1
  have key : ∀ k : ℕ, s ^ (k + 1) * W (H.dL (ϖ ^ (k + 1)) 1) =
      β * (s ^ k * W (H.dL (ϖ ^ k) 1)) + (α : ℂ) ^ (k + 1) * W 1 := by
    intro k
    induction k with
    | zero =>
      simp only [zero_add, pow_one, pow_zero, one_mul, dL_one]
      rw [h3]
      ring
    | succ k ih =>
      have h := hrec k
      rw [← hss] at h
      linear_combination (α : ℂ) * ih - s ^ k * h
  induction k with
  | zero => simp [dL_one]
  | succ k ih =>
    rw [key, ih, hs_succ]
    ring

theorem UpperTheory.eigenform_shintani_formula_at_place :
    ∀ (K : Type) [Field K] [NumberField K] (v : H.P K) (ϖ : (H.Kv v)ˣ), H.IsU ϖ → ∀ (χ : H.Kv v → ℂ), H.Good χ → ∀ (α β : ℂˣ) (f : GL (Fin 2) (A K) → ℂ),
          EigAt v {α, β} f → (∀ b h, f (H.lc v (H.nL b) * h) = χ b * f h) → ∀ g, H.KAt v g → ∀ k : ℕ,
          (H.q v ^ (1 / 2 : ℂ)) ^ k * f (aE (H.idl v ϖ ^ k) * g) = (∑ i ∈ Finset.range (k + 1), ((α : ℂ)) ^ i * ((β : ℂ)) ^ (k - i)) * f g := by
  intro K _ _ v ϖ hϖ χ hχ α β f hB hn g hg k
  have hE1 : UpperTheory.V.Af.Smo.Eig v {α, β} fun x => f (H.lc v x * g) := by
    have := (H.fixTr K v f g hg).2 _ hB 1
    simpa [H.lc] using this
  have hnl : ∀ b x, f (H.lc v (H.nL b * x) * g) = χ b * f (H.lc v x * g) := fun b x => by
    rw [map_mul, mul_assoc, hn]
  have h := tor_loc K v ϖ hϖ χ hχ α β _ hE1 hnl k
  have e : H.idl v (ϖ ^ k) = H.idl v ϖ ^ k := map_pow _ _ _
  beta_reduce at h
  rw [(H.lcLaws K v).2.2.2.1, e, map_one, one_mul] at h
  exact h
