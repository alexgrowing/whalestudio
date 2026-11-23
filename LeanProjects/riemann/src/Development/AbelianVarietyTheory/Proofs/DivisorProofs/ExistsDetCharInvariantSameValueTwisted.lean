import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSFockColumnSubstitutionUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MinorFrame

open MvPolynomial

theorem colSub_totalDegree_le {ι : Type} [Fintype ι] {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    (colSub g P).totalDegree ≤ P.totalDegree := by
  classical
  unfold colSub
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [aeval_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  refine le_trans ?_ (le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (totalDegree_pow _ _).trans ?_
  have h1 : (∑ j' : Fin a, C (g i.1 j' i.2.2) * (X (i.1, i.2.1, j') : Pol ι d a)).totalDegree ≤ 1 :=
    totalDegree_finsetSum_le fun j _ => (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X])
  calc s i * _ ≤ s i * 1 := Nat.mul_le_mul_left _ h1
    _ = s i := mul_one _

theorem star_detChar_mul_detChar {ι : Type} [Fintype ι] {a : ℕ} (n : ι → ℕ) (g : ι → Matrix.unitaryGroup (Fin a) ℂ) :
    starRingEnd ℂ (detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ))) *
      detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) = 1 := by
  unfold detChar
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [map_pow, ← mul_pow]
  have h : starRingEnd ℂ (g τ : Matrix (Fin a) (Fin a) ℂ).det * (g τ : Matrix (Fin a) (Fin a) ℂ).det = 1 := by
    rw [starRingEnd_apply, ← Matrix.det_conjTranspose, ← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.1 (g τ).2,
      Matrix.det_one]
  rw [h, one_pow]

@[reducible] def fockCore {σ : Type} (S : Submodule ℂ (MvPolynomial σ ℂ)) : InnerProductSpace.Core ℂ S where
  inner x y := Formalism.L2.DIV.fockS x.1 y.1
  conj_inner_symm x y := (fockS_conj x.1 y.1).symm
  re_inner_nonneg x := by
    by_cases hx : x.1 = 0
    · simp [hx, Formalism.L2.DIV.fockS]
    · exact (fockS_self_re_pos hx).le
  add_left x y z := by
    show Formalism.L2.DIV.fockS (x.1 + y.1) z.1 = _
    rw [← Formalism.L2.DIV.fockL_apply, LinearMap.map_add₂]
    rfl
  smul_left x y r := by
    show Formalism.L2.DIV.fockS (r • x.1) y.1 = _
    rw [← Formalism.L2.DIV.fockL_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    rfl
  definite x hx := by
    by_contra h
    have h' : x.1 ≠ 0 := fun e => h (Subtype.ext e)
    have := fockS_self_re_pos h'
    rw [show Formalism.L2.DIV.fockS x.1 x.1 = 0 from hx] at this
    simp at this

theorem exists_mem_inv_eq_of_twisted : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (Pr : Type) [AddCommGroup Pr] [Module ℂ Pr]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Pr),
    (∀ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (P : GlobalTheory.MinorFrame.Pol ι d a),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) P) = GlobalTheory.MinorFrame.detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • q P) →
    ∀ P : GlobalTheory.MinorFrame.Pol ι d a, ∃ P₀ ∈ GlobalTheory.MinorFrame.inv (ι := ι) a d n, q P = q P₀ := by
  intro ι _ a d n Pr _ _ q hq P
  classical
  let S : Submodule ℂ (Pol ι d a) := restrictTotalDegree (Var ι d a) ℂ P.totalDegree
  haveI : FiniteDimensional ℂ S :=
    inferInstanceAs (Module.Finite ℂ (restrictTotalDegree (Var ι d a) ℂ P.totalDegree))
  letI : InnerProductSpace.Core ℂ S := fockCore S
  letI : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore _
  have hmemS : ∀ (g : ι → Matrix (Fin a) (Fin a) ℂ) (x : Pol ι d a), x ∈ S → colSub g x ∈ S := fun g x hx =>
    (mem_restrictTotalDegree _ _ _).2 ((colSub_totalDegree_le g x).trans ((mem_restrictTotalDegree _ _ _).1 hx))
  let gen : Set S := {w | ∃ (g : ι → Matrix.unitaryGroup (Fin a) ℂ) (x : S),
      (w : Pol ι d a) = colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) x.1 -
        detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) • x.1}
  let K : Submodule ℂ S := Submodule.span ℂ gen
  have hK : ∀ w ∈ K, q (w : Pol ι d a) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, y, hy⟩ := hx
      rw [hy, map_sub, map_smul, hq, sub_self]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  have hPS : P ∈ S := (mem_restrictTotalDegree _ _ _).2 le_rfl
  obtain ⟨y, hy, z, hz, hyz⟩ := K.exists_add_mem_mem_orthogonal (⟨P, hPS⟩ : S)
  refine ⟨z.1, ?_, ?_⟩
  · intro g
    set G := colSub (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) z.1 with hG
    set c := detChar n (fun τ => (g τ : Matrix (Fin a) (Fin a) ℂ)) with hc
    let w : S := ⟨G - c • z.1, S.sub_mem (hmemS _ _ z.2) (S.smul_mem c z.2)⟩
    have hw : w ∈ K := Submodule.subset_span ⟨g, z, rfl⟩
    have h1 : Formalism.L2.DIV.fockL z.1 (G - c • z.1) = 0 := Submodule.inner_left_of_mem_orthogonal hw hz
    have h2 : Formalism.L2.DIV.fockL (G - c • z.1) z.1 = 0 := Submodule.inner_right_of_mem_orthogonal hw hz
    have hinv : Formalism.L2.DIV.fockL G G = Formalism.L2.DIV.fockL z.1 z.1 := by
      rw [Formalism.L2.DIV.fockL_apply, Formalism.L2.DIV.fockL_apply, hG, fockS_colSub_unitary]
    have hcc := star_detChar_mul_detChar n g
    rw [← hc] at hcc
    have e1 : Formalism.L2.DIV.fockL (G - c • z.1) (G - c • z.1) =
        Formalism.L2.DIV.fockL (G - c • z.1) G - c * Formalism.L2.DIV.fockL (G - c • z.1) z.1 := by
      rw [map_sub, map_smul, smul_eq_mul]
    have e2 : Formalism.L2.DIV.fockL (G - c • z.1) G =
        Formalism.L2.DIV.fockL G G - starRingEnd ℂ c * Formalism.L2.DIV.fockL z.1 G := by
      rw [LinearMap.map_sub₂, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    have h1' : Formalism.L2.DIV.fockL z.1 G - c * Formalism.L2.DIV.fockL z.1 z.1 = 0 := by
      rw [← h1, map_sub, map_smul, smul_eq_mul]
    have hWW : Formalism.L2.DIV.fockL (G - c • z.1) (G - c • z.1) = 0 := by
      linear_combination e1 + e2 - c * h2 + hinv - starRingEnd ℂ c * h1' - Formalism.L2.DIV.fockL z.1 z.1 * hcc
    by_contra hne
    have hne' : G - c • z.1 ≠ 0 := sub_ne_zero.2 hne
    have := fockS_self_re_pos hne'
    rw [← Formalism.L2.DIV.fockL_apply, hWW] at this
    simp at this
  · have hP : P = y.1 + z.1 := congrArg Subtype.val hyz
    rw [hP, map_add, hK y hy, zero_add]

end GlobalTheory.MinorFrame
