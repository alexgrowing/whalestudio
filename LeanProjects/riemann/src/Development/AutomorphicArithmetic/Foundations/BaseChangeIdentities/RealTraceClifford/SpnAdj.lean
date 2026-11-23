import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.SpnRel

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {J : Type} [Fintype J] [DecidableEq J]

private theorem mt_ap (M : Matrix J J ℂ) (x : Ten J V) (j : J) :
    (UpperTheory.RealTr.mt V M x).ofLp j = ∑ k, M j k • x.ofLp k := rfl

private theorem lf_ap (T : Module.End ℂ V) (x : Ten J V) (j : J) :
    (lf J T x).ofLp j = T (x.ofLp j) := rfl

private theorem mt_mul (M N : Matrix J J ℂ) : UpperTheory.RealTr.mt V (M * N) = UpperTheory.RealTr.mt V M * UpperTheory.RealTr.mt V N := by
  refine LinearMap.ext fun x => PiLp.ext fun j => ?_
  simp only [Module.End.mul_apply, mt_ap, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

private theorem mt_one : UpperTheory.RealTr.mt V (1 : Matrix J J ℂ) = 1 := by
  ext x j
  simp [mt_ap, Matrix.one_apply]

private theorem mt_add (M N : Matrix J J ℂ) : UpperTheory.RealTr.mt V (M + N) = UpperTheory.RealTr.mt V M + UpperTheory.RealTr.mt V N := by
  ext x j
  simp [mt_ap, add_smul, Finset.sum_add_distrib]

private theorem mt_smul (r : ℂ) (M : Matrix J J ℂ) : UpperTheory.RealTr.mt V (r • M) = r • UpperTheory.RealTr.mt V M := by
  ext x j
  simp [mt_ap, smul_smul, Finset.smul_sum]

private theorem lf_mt (M : Matrix J J ℂ) (T : Module.End ℂ V) :
    lf J T * UpperTheory.RealTr.mt V M = UpperTheory.RealTr.mt V M * lf J T := by
  ext x j
  simp [mt_ap, lf_ap, map_sum]

private theorem mt_adj (M : Matrix J J ℂ) (x y : Ten J V) :
    ⟪UpperTheory.RealTr.mt V M x, y⟫_ℂ = ⟪x, UpperTheory.RealTr.mt V Mᴴ y⟫_ℂ := by
  simp only [PiLp.inner_apply, mt_ap, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Matrix.conjTranspose_apply, Complex.star_def]
  exact Finset.sum_comm

private theorem lf_adj (T T' : Module.End ℂ V) (h : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T' y⟫_ℂ) (x y : Ten J V) :
    ⟪lf J T x, y⟫_ℂ = ⟪x, lf J T' y⟫_ℂ := by
  simp only [PiLp.inner_apply, lf_ap, h]

private theorem spn_adj {n : ℕ} (c : Fin n → Fin n → Matrix J J ℂ) (hc : ∀ a b, (c a b)ᴴ = c b a) (a b : Fin n) :
    (spn c a b)ᴴ = spn c b a := by
  simp only [spn, Matrix.conjTranspose_sub, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, hc,
    Algebra.algebraMap_eq_smul_one]
  congr 1
  split_ifs with h1 h2 h2
  · simp [Matrix.conjTranspose_smul, Complex.star_def]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

private theorem real_trace_matrix_sub {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {J : Type} [Fintype J]
    (M N : Matrix J J ℂ) : UpperTheory.RealTr.mt V (M - N) = UpperTheory.RealTr.mt V M - UpperTheory.RealTr.mt V N := by
  refine LinearMap.ext fun x => PiLp.ext fun j => ?_
  simp [mt_ap, sub_smul, Finset.sum_sub_distrib]

private theorem real_trace_matrix_zero {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {J : Type} [Fintype J] :
    UpperTheory.RealTr.mt V (0 : Matrix J J ℂ) = 0 := by
  refine LinearMap.ext fun x => PiLp.ext fun j => ?_
  simp [mt_ap]

private theorem gl_dg {n : ℕ} (K : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix J J ℂ)
    (hK : GlRel K) (hs : GlRel (spn c)) : GlRel (dg K c) := by
  intro a b e d
  have h1 : lf J (K a b) * lf J (K e d) - lf J (K e d) * lf J (K a b) =
      lf J ((if b = e then K a d else 0) - if d = a then K e b else 0) := by
    rw [← hK a b e d, map_sub, map_mul, map_mul]
  have h2 : UpperTheory.RealTr.mt V (spn c a b) * UpperTheory.RealTr.mt V (spn c e d) -
      UpperTheory.RealTr.mt V (spn c e d) * UpperTheory.RealTr.mt V (spn c a b) =
      UpperTheory.RealTr.mt V ((if b = e then spn c a d else 0) - if d = a then spn c e b else 0) := by
    rw [← hs a b e d, real_trace_matrix_sub, mt_mul, mt_mul]
  have h3 := lf_mt (V := V) (spn c e d) (K a b)
  have h4 := lf_mt (V := V) (spn c a b) (K e d)
  have key : dg K c a b * dg K c e d - dg K c e d * dg K c a b =
      lf J ((if b = e then K a d else 0) - if d = a then K e b else 0) +
      UpperTheory.RealTr.mt V ((if b = e then spn c a d else 0) - if d = a then spn c e b else 0) := by
    rw [← h1, ← h2]
    simp only [dg, add_mul, mul_add]
    rw [h3, h4]
    abel
  rw [key]
  split_ifs <;> simp only [dg, map_sub, map_zero, real_trace_matrix_sub, real_trace_matrix_zero, sub_zero] <;> abel
end

theorem UpperTheory.RealTr.tenF :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (J : Type) [Fintype J] [DecidableEq J],
      (∃ φ : Matrix J J ℂ →ₐ[ℂ] Module.End ℂ (Ten J V), ∀ M, φ M = mt V M) ∧ (∀ M (T : Module.End ℂ V), lf J T * mt V M = mt V M * lf J T) ∧
      (∀ M (x y : Ten J V), ⟪mt V M x, y⟫_ℂ = ⟪x, mt V Mᴴ y⟫_ℂ) ∧
      (∀ T T' : Module.End ℂ V, (∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T' y⟫_ℂ) → ∀ x y : Ten J V, ⟪lf J T x, y⟫_ℂ = ⟪x, lf J T' y⟫_ℂ) ∧
      ∀ (K : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix J J ℂ) (η : J → Wt n), UF K → ClifMod c η → UF (dg K c) := by
  intro n V _ _ J _ _
  refine ⟨⟨AlgHom.ofLinearMap ⟨⟨UpperTheory.RealTr.mt V, fun M N => mt_add M N⟩, fun r M => mt_smul r M⟩
      mt_one (fun M N => mt_mul M N), fun M => rfl⟩,
    fun M T => lf_mt M T, fun M x y => mt_adj M x y, fun T T' h x y => lf_adj T T' h x y, ?_⟩
  intro K c η hK hc
  refine ⟨gl_dg K c hK.gl (spnRel n _ c hc.rel).1, ?_⟩
  intro a b x y
  simp only [dg, LinearMap.add_apply, inner_add_left, inner_add_right]
  rw [lf_adj _ _ (hK.unit a b), mt_adj, spn_adj c hc.adj]
