import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiablePolyDeriv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ColPoly

section Deriv

variable {σ κ W W' : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup W']
  [NormedSpace ℂ W']

theorem polyDeriv_comp_linear {F : W' → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (A : W →L[ℂ] W')
    (P : MvPolynomial σ ℂ) (u : σ → W) (x : W) :
    I2.polyDeriv P u (fun z => F (A z)) x = I2.polyDeriv P (fun l => A (u l)) F (A x) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  have hcomp := A.iteratedFDeriv_comp_right hF x
    (i := Multiset.card (Finsupp.toMultiset m)) (by exact_mod_cast le_top)
  rw [show (fun z => F (A z)) = F ∘ A from rfl, hcomp]
  rfl

private theorem polyDeriv_C_indep (a : ℂ) (u v : σ → W) (F : W → ℂ) (x : W) :
    I2.polyDeriv (MvPolynomial.C a : MvPolynomial σ ℂ) u F x =
      I2.polyDeriv (MvPolynomial.C a : MvPolynomial σ ℂ) v F x := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : m = 0 := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_C, if_neg (Ne.symm hne)])
  subst hm0
  congr 1

theorem polyDeriv_subst [Fintype κ] {F : W → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (s : σ → κ → ℂ)
    (j : σ → κ → σ) (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (hΦ : ∀ l, Φ (MvPolynomial.X l) = ∑ k, MvPolynomial.C (s l k) * MvPolynomial.X (j l k))
    (u : σ → W) (P : MvPolynomial σ ℂ) (x : W) :
    I2.polyDeriv (Φ P) u F x = I2.polyDeriv P (fun l => ∑ k, s l k • u (j l k)) F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a =>
    rw [MvPolynomial.algHom_C]
    exact polyDeriv_C_indep a _ _ F x
  | add p q hp hq => rw [map_add, I2.polyDeriv_add, I2.polyDeriv_add, hp, hq]
  | mul_X p l hp =>
    have e1 : (fun y => I2.polyDeriv (Φ p) u F y) =
        fun y => I2.polyDeriv p (fun l => ∑ k, s l k • u (j l k)) F y := funext hp
    rw [polyDeriv_mul_X hF p _ l x, map_mul, hΦ l, Finset.mul_sum, I2.jof_polyDeriv_sum]
    simp_rw [MvPolynomial.C_mul', mul_smul_comm, I2.polyDeriv_smul, polyDeriv_mul_X hF (Φ p) u _ x, e1]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]

end Deriv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

noncomputable def hActL (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (h : Matrix (Fin n) (Fin n) E) :
    (Fin n → Fin g → ℂ) →L[ℂ] (Fin n → Fin g → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := hAct X idx h
      map_add' := fun x y => by funext k i; simp [hAct, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by funext k i; simp [hAct, Finset.mul_sum, mul_left_comm] }

end GlobalTheory.Dict.ColPoly

open GlobalTheory.Dict.ColPoly in

theorem GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ P ∈ Harm.rowHighest ℂ k k', ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ F : (Fin n → Fin g → ℂ) → ℂ, AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv P (letterDir X hr idx) (fun z => F (hAct X idx h z)) 0 = I2.polyDeriv P' (letterDir X hr idx) F 0 := by
  intro E _ _ _ r X g q0 hr bas idx n _hs _hn h hh k k' P hP
  classical
  let A : X.Ψ → Matrix (Fin n) (Fin n) ℂ := fun t => (h.map (t.1 : E →+* ℂ))ᵀ
  let B : X.Ψ → Matrix (Fin n) (Fin n) ℂ :=
    fun t => h.map (ComplexEmbedding.conjugate (t.1 : E →+* ℂ))
  have hAB : ∀ t, A t * B t = 1 := by
    intro t
    have h1 := congrArg (fun M => M.map (t.1 : E →+* ℂ)) hh
    simp only [Matrix.map_mul, GlobalTheory.SW.Base.ccT_map, Matrix.map_one _ (map_zero _) (map_one _)] at h1
    ext i j
    have h2 := congrFun (congrFun h1 j) i
    simp only [A, B, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.conjTranspose_apply, ComplexEmbedding.conjugate_coe_eq, Matrix.one_apply] at h2 ⊢
    convert h2 using 1
    · exact Finset.sum_congr rfl fun l _ => by rw [mul_comm]; rfl
    · by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
  let s : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → ℂ :=
    fun l k₁ => rowType X (rowOf X hr (l.1, l.2.1)) (h k₁ l.2.2)
  let j : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → Harm.Var X.Ψ q0 X.p0 (Fin n) :=
    fun l k₁ => (l.1, l.2.1, k₁)
  have hΦ : ∀ l, GlobalTheory.Harm.colSubst A B (MvPolynomial.X l) =
      ∑ k₁, MvPolynomial.C (s l k₁) * MvPolynomial.X (j l k₁) := by
    rintro ⟨t, (a | b), k₀⟩
    · have e : rowType X (t, rowIdx hr (Sum.inl a)) = t.1 := by
        simpa using rowType_rowOf_inl X hr t a
      simp [GlobalTheory.Harm.xForm, GlobalTheory.Harm.rowForm_apply, A, s, j, e]
    · have e : rowType X (t, rowIdx hr (Sum.inr b)) = ComplexEmbedding.conjugate t.1 := by
        simpa using rowType_rowOf_inr X hr t b
      simp [GlobalTheory.Harm.yForm, GlobalTheory.Harm.rowForm_apply, B, s, j, e, ComplexEmbedding.conjugate_coe_eq]
  have hdir : (fun l => hActL X idx h (letterDir X hr idx l)) =
      fun l => ∑ k₁, s l k₁ • letterDir X hr idx (j l k₁) := by
    funext l k₁ i
    show hAct X idx h (letterDir X hr idx l) k₁ i = _
    by_cases hi : i = idx.symm (rowOf X hr (l.1, l.2.1))
    · subst hi
      simp [hAct, letterDir, Pi.single_apply, Finset.sum_apply, s, j, ite_apply, mul_ite,
        Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp only [rowOf_apply] at hi
      simp [hAct, letterDir, Pi.single_apply, Finset.sum_apply, s, j, hi, ite_apply, mul_ite]
  refine ⟨GlobalTheory.Harm.colSubst A B P, GlobalTheory.Harm.colSubst_mem_rowHighest hAB hP, fun F hF => ?_⟩
  have hF' : ContDiff ℂ (⊤ : ℕ∞) F := contDiffOn_univ.1 (hF.contDiffOn uniqueDiffOn_univ)
  have e0 := polyDeriv_comp_linear hF' (hActL X idx h) P (letterDir X hr idx) 0
  rw [map_zero, hdir] at e0
  rw [show (fun z => F (hAct X idx h z)) = fun z => F (hActL X idx h z) from rfl, e0]
  exact (polyDeriv_subst hF' s j (GlobalTheory.Harm.colSubst A B) hΦ (letterDir X hr idx) P 0).symm
