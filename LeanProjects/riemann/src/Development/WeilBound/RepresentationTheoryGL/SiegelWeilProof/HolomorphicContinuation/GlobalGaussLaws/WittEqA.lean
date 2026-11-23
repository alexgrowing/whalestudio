import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SigOKOf
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AtPlaceIffEqAtTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLagrangianDecompositionInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOfLevelClass

noncomputable section

open scoped Matrix ComplexConjugate nonZeroDivisors
open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.WEq

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

local notation "hermF" => ReciprocityTheory.ChartRestriction.G.FD.herm
local notation "ccF" => ReciprocityTheory.ChartRestriction.G.FD.cc

def dSgn (r k : ℕ) : Matrix (Fin r) (Fin r) E := Matrix.diagonal fun a => if (a : ℕ) < k then 1 else -1

theorem dSgn_hermF (r k : ℕ) (a b : Fin r) : ccF (dSgn (E := E) r k a b) = dSgn r k b a := by
  by_cases h : a = b
  · subst h
    simp only [dSgn, Matrix.diagonal_apply_eq, ReciprocityTheory.ChartRestriction.G.FD.cc]
    split_ifs <;> simp
  · simp [dSgn, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), ReciprocityTheory.ChartRestriction.G.FD.cc]

theorem dSgn_det (k : ℕ) : (dSgn (E := E) r k).det ≠ 0 := by
  rw [dSgn, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
  intro a _
  split_ifs <;> norm_num

theorem mem_one_iff_isIntegral (z : E) : z ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ IsIntegral ℤ z := by
  rw [FractionalIdeal.mem_one_iff, IsIntegralClosure.isIntegral_iff (A := 𝓞 E)]

theorem cc_isIntegral {z : E} (h : IsIntegral ℤ z) : IsIntegral ℤ (cc z) :=
  h.map (IsCMField.complexConj E : E →+* E).toIntAlgHom

theorem herm_diag (d : Fin r → E) (x y : Fin r → E) :
    hermF (Matrix.diagonal d) x y = ∑ a, x a * d a * ccF (y a) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem mem_stdLat_iff_forall_isIntegral (n : ℕ) (x : Fin n → E) :
    x ∈ GlobalTheory.InertWitt.stdLat E n ↔ ∀ i, IsIntegral ℤ (x i) := by
  constructor
  · rintro ⟨w, rfl⟩ i
    exact (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mpr ⟨w i, rfl⟩
  · intro h
    choose w hw using fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (h i)
    exact ⟨w, funext fun i => hw i⟩

private theorem isIntegral_ite_one_neg_one (k : ℕ) (a : Fin r) : IsIntegral ℤ (if (a : ℕ) < k then (1 : E) else -1) := by
  split_ifs
  · exact isIntegral_one
  · exact isIntegral_one.neg

theorem mod_std (k : ℕ) (x : Fin r → E) : x ∈ GlobalTheory.InertWitt.stdLat E r ↔
    ∀ y ∈ GlobalTheory.InertWitt.stdLat E r, hermF (dSgn r k) x y ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [mem_stdLat_iff_forall_isIntegral]
  constructor
  · intro hx y hy
    rw [mem_stdLat_iff_forall_isIntegral] at hy
    rw [mem_one_iff_isIntegral, dSgn, herm_diag]
    exact IsIntegral.sum _ fun a _ => ((hx a).mul (isIntegral_ite_one_neg_one k a)).mul (cc_isIntegral (hy a))
  · intro h i
    have hy : (Pi.single i 1 : Fin r → E) ∈ GlobalTheory.InertWitt.stdLat E r := by
      rw [mem_stdLat_iff_forall_isIntegral]
      intro j
      by_cases hj : j = i
      · subst hj; simpa using isIntegral_one
      · simpa [Pi.single_apply, hj] using isIntegral_zero
    have h1 := h _ hy
    rw [mem_one_iff_isIntegral, dSgn, herm_diag] at h1
    have h2 : IsIntegral ℤ (x i * (if (i : ℕ) < k then (1 : E) else -1)) := by
      convert h1 using 1
      rw [Finset.sum_eq_single i]
      · simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · simp
    have h3 := h2.mul (isIntegral_ite_one_neg_one k i)
    have h4 : x i * (if (i : ℕ) < k then (1 : E) else -1) * (if (i : ℕ) < k then (1 : E) else -1) = x i := by
      split_ifs <;> ring
    rwa [h4] at h3

def ext {k : ℕ} (hr : 2 * k = r) (u : Fin k → E) : Fin r → E := fun a =>
  if h : (a : ℕ) < k then u ⟨a, h⟩ else u ⟨a - k, by have := a.isLt; omega⟩

def extL {k : ℕ} (hr : 2 * k = r) : (Fin k → E) →ₗ[E] (Fin r → E) where
  toFun := ext hr
  map_add' u v := by funext a; simp only [ext, Pi.add_apply]; split_ifs <;> rfl
  map_smul' c u := by funext a; simp only [ext, Pi.smul_apply, RingHom.id_apply]; split_ifs <;> rfl

theorem extL_injective {k : ℕ} (hr : 2 * k = r) : Function.Injective (extL (E := E) hr) := by
  intro u v h
  funext i
  have := congrFun h ⟨i, by omega⟩
  simpa [extL, ext, i.isLt] using this

theorem herm_ext {k : ℕ} (hr : 2 * k = r) (u v : Fin k → E) :
    hermF (dSgn r k) (ext hr u) (ext hr v) = 0 := by
  rw [dSgn, herm_diag]
  subst hr
  rw [← Equiv.sum_comp (finCongr (two_mul k).symm), Fin.sum_univ_add]
  simp [ext, Matrix.diagonal_apply_eq]

end Gen

end PositivityTheory.Rg.Sw.Glob.WEq
