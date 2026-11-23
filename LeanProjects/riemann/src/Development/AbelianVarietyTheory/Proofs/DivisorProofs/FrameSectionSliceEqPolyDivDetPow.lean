import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.SemistableReduction.LatAll
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem differentiable_det_of {r : ℕ} :
    Differentiable ℂ (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det) := by
  have : (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det) =
      fun y => ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : ℂ) * ∏ i, y (σ i) i := by
    funext y
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    simp [Matrix.of_apply]
  rw [this]
  fun_prop

theorem differentiable_update_frame {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {r : ℕ}
    (x : Ψ → Fin r → Fin r → ℂ) (τ : Ψ) :
    Differentiable ℂ (fun y : Fin r → Fin r → ℂ => Function.update x τ y) := by
  intro y
  exact (hasFDerivAt_update x y).differentiableAt

end GlobalTheory

namespace GlobalTheory

theorem section_slice_eq_poly_div_det_pow :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) [DecidableEq X.Ψ],
      (∀ x : Frame X.Ψ r, x ∈ X.dom ↔ ∀ τ, (mat x τ).det ≠ 0) →
      ∀ (la : Wt X.Ψ r) (N : ℕ), (∀ τ i, 0 ≤ la τ i + N) →
      ∀ P : Frame X.Ψ r → ℂ, X.IsSec la P → ∀ x ∈ X.dom, ∀ τ : X.Ψ,
        ∃ F : MvPolynomial (Fin r × Fin r) ℂ, F.IsHomogeneous (∑ i, (la τ i + N).toNat) ∧
          ∀ y : Fin r → Fin r → ℂ, (Matrix.of y).det ≠ 0 →
            P (Function.update x τ y) =
              MvPolynomial.eval (fun ij => y ij.1 ij.2) F * ((Matrix.of y).det)⁻¹ ^ N := by
  intro E _ _ _ r X _ hdom la N hN P hP x hx τ
  classical

  have hupd : ∀ y : Fin r → Fin r → ℂ,
      Function.update x τ y ∈ X.dom ↔ (Matrix.of y).det ≠ 0 := by
    intro y
    rw [hdom]
    have hx' := (hdom x).1 hx
    constructor
    · intro h
      have := h τ
      simpa [mat] using this
    · intro h σ
      by_cases hσ : σ = τ
      · subst hσ
        simpa [mat] using h
      · simpa [mat, Function.update_of_ne hσ] using hx' σ
  let a : Fin r → ℕ := fun i => (la τ i + N).toNat
  let h : Matrix (Fin r) (Fin r) ℂ → ℂ := fun y =>
    P (Function.update x τ (fun i j => y i j)) * y.det ^ N

  have hholo : ReciprocityTheory.MultiplicativeHeights.IsHoloGL h := by
    unfold ReciprocityTheory.MultiplicativeHeights.IsHoloGL
    have h1 : DifferentiableOn ℂ (fun y : Fin r → Fin r → ℂ => P (Function.update x τ y))
        {y | (Matrix.of y).det ≠ 0} :=
      hP.1.comp (differentiable_update_frame x τ).differentiableOn
        (fun y hy => (hupd y).2 hy)
    have h2 : DifferentiableOn ℂ (fun y : Fin r → Fin r → ℂ => (Matrix.of y).det ^ N)
        {y | (Matrix.of y).det ≠ 0} :=
      (differentiable_det_of.pow N).differentiableOn
    exact h1.mul h2

  have htri : ReciprocityTheory.MultiplicativeHeights.IsTriEquivariant a h := by
    intro y b hy hb hbt
    let b' : Frame X.Ψ r := fun σ => if σ = τ then b else (1 : Matrix (Fin r) (Fin r) ℂ)
    have hbτ : b' τ = b := by exact if_pos rfl
    have hbσ : ∀ σ, σ ≠ τ → b' σ = (1 : Matrix (Fin r) (Fin r) ℂ) := fun σ hσ => by exact if_neg hσ
    have hb'B : b' ∈ Bor X.Ψ r := by
      intro σ
      by_cases hσ : σ = τ
      · subst hσ
        refine ⟨?_, fun c d hcd => ?_⟩
        · change (Matrix.of (b' σ)).det ≠ 0
          rw [hbτ]; exact hb
        · rw [hbτ]; exact hbt hcd
      · refine ⟨?_, fun c d hcd => ?_⟩
        · change (Matrix.of (b' σ)).det ≠ 0
          rw [hbσ σ hσ]; change (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0; simp
        · rw [hbσ σ hσ, Matrix.one_apply, if_neg (ne_of_lt hcd).symm]
    have hrm : rmul (Function.update x τ (fun i j => y i j)) b' =
        Function.update x τ (fun i j => (y * b) i j) := by
      funext σ
      by_cases hσ : σ = τ
      · subst hσ
        change (Matrix.of (Function.update x σ (fun i j => y i j) σ) * Matrix.of (b' σ) :
          Matrix (Fin r) (Fin r) ℂ) = Function.update x σ (fun i j => (y * b) i j) σ
        rw [hbτ, Function.update_self, Function.update_self]
        rfl
      · change (Matrix.of (Function.update x τ (fun i j => y i j) σ) * Matrix.of (b' σ) :
          Matrix (Fin r) (Fin r) ℂ) = Function.update x τ (fun i j => (y * b) i j) σ
        rw [hbσ σ hσ, Function.update_of_ne hσ, Function.update_of_ne hσ]
        exact Matrix.mul_one _
    have hbc : bchar la b' = ∏ i, b i i ^ la τ i := by
      unfold bchar
      rw [Finset.prod_eq_single τ]
      · rw [hbτ]
      · intro σ _ hσ
        rw [hbσ σ hσ]
        exact Finset.prod_eq_one fun i _ => by simp
      · intro h'; exact absurd (Finset.mem_univ τ) h'
    have hmem : Function.update x τ (fun i j => y i j) ∈ X.dom := (hupd _).2 hy
    have hP2 := hP.2.1 _ hmem b' hb'B
    rw [hrm, hbc] at hP2
    have hdb : b.det = ∏ i, b i i := Matrix.det_of_upperTriangular hbt
    have hbii : ∀ i, b i i ≠ 0 := by
      intro i
      rw [hdb] at hb
      exact Finset.prod_ne_zero_iff.mp hb i (Finset.mem_univ i)
    have hchar : (∏ i, b i i ^ la τ i) * b.det ^ N = ReciprocityTheory.MultiplicativeHeights.triChar a b := by
      rw [hdb, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      unfold ReciprocityTheory.MultiplicativeHeights.triChar
      refine Finset.prod_congr rfl fun i _ => ?_
      have e : ((la τ i + N).toNat : ℤ) = la τ i + N := Int.toNat_of_nonneg (hN τ i)
      rw [← zpow_natCast (b i i) N, ← zpow_add₀ (hbii i), ← zpow_natCast, e]
    show P (Function.update x τ (fun i j => (y * b) i j)) * (y * b).det ^ N =
      ReciprocityTheory.MultiplicativeHeights.triChar a b * (P (Function.update x τ (fun i j => y i j)) * y.det ^ N)
    rw [hP2, Matrix.det_mul, mul_pow, ← hchar]
    ring
  obtain ⟨F, hF, hFe⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.bwPoly r a h hholo htri
  refine ⟨F, hF, fun y hy => ?_⟩
  have e := hFe (Matrix.of y) hy
  have e' : P (Function.update x τ y) * (Matrix.of y).det ^ N =
      MvPolynomial.eval (fun ij => y ij.1 ij.2) F := e
  rw [← e', inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hy), mul_one]

end GlobalTheory
