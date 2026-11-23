import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
import Formalism.HarderNarasimhan.ShiftInvariance
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

noncomputable section

namespace GlobalTheory.FrameDeg

theorem form_eq_of_re_diag {K V : Type} [Field K] [AddCommGroup V] [Module K V] (σ : K →+* ℂ)
    (F G : V → V → ℂ)
    (hFa : ∀ x y z, F x (y + z) = F x y + F x z) (hGa : ∀ x y z, G x (y + z) = G x y + G x z)
    (hFs : ∀ (a : K) x y, F x (a • y) = σ a * F x y) (hGs : ∀ (a : K) x y, G x (a • y) = σ a * G x y)
    (hFc : ∀ x y, starRingEnd ℂ (F x y) = F y x) (hGc : ∀ x y, starRingEnd ℂ (G x y) = G y x)
    (hd : ∀ x, (F x x).re = (G x x).re) (ha : ∃ a : K, (σ a).im ≠ 0) (x y : V) : F x y = G x y := by
  have hFl : ∀ x x' y, F (x + x') y = F x y + F x' y := by
    intro x x' y
    rw [← hFc y (x + x'), hFa, map_add, hFc, hFc]
  have hGl : ∀ x x' y, G (x + x') y = G x y + G x' y := by
    intro x x' y
    rw [← hGc y (x + x'), hGa, map_add, hGc, hGc]
  have hre : ∀ x y, (F x y).re = (G x y).re := by
    intro x y
    have h1 := hd (x + y)
    rw [hFl, hFa, hFa, hGl, hGa, hGa, ← hFc x y, ← hGc x y] at h1
    simp only [Complex.add_re, Complex.conj_re] at h1
    linarith [hd x, hd y]
  obtain ⟨a, ha⟩ := ha
  have h2 := hre x (a • y)
  rw [hFs, hGs, Complex.mul_re, Complex.mul_re, hre x y] at h2
  have him : (F x y).im = (G x y).im := by
    have : (σ a).im * (F x y).im = (σ a).im * (G x y).im := by linarith
    exact mul_left_cancel₀ ha this
  exact Complex.ext (hre x y) him

section Maj

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

theorem majAt_add_right (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y z : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (y + z) = Formalism.HermitianLatticesTheory.majAt b X v x y + Formalism.HermitianLatticesTheory.majAt b X v x z := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem majAt_smul_right (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (a • y) = v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  have hv : Formalism.HermitianLatticesTheory.vecAt b v (a • y) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v y := by
    funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, hv, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem majAt_conj (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x y : V) :
    starRingEnd ℂ (Formalism.HermitianLatticesTheory.majAt b X v x y) = Formalism.HermitianLatticesTheory.majAt b X v y x := by
  simp only [Formalism.HermitianLatticesTheory.majAt, map_sum, map_mul, Complex.star_def, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem majAt_self_re (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (x : V) :
    (Formalism.HermitianLatticesTheory.majAt b X v x x).re = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
  rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (by positivity)]
  simp only [Formalism.HermitianLatticesTheory.majAt, Complex.re_sum, Complex.star_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm, Complex.normSq_apply]
  ring

end Maj

theorem form_self_re_nonneg {K V : Type} [Field K] [AddCommGroup V] [Module K V] (nm : HermFam K V)
    (σ : K →+* ℂ) (x : V) : 0 ≤ (nm.form σ x x).re := by
  by_cases hx : x = 0
  · subst hx
    have h0 : nm.form σ 0 0 = 0 := by
      have := nm.add_right σ 0 0 0
      simp only [add_zero] at this
      linear_combination -this
    simp [h0]
  · have hli : LinearIndependent K ![x] := by
      rw [linearIndependent_unique_iff]; simpa using hx
    have hp := (nm.posDef σ 1 ![x] hli).det_pos
    rw [Matrix.det_unique] at hp
    simpa using (Complex.pos_iff.1 hp).1.le

theorem finrank_eq_two_mul_nPl' {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] :
    Module.finrank ℚ K = 2 * Formalism.HN.nPl K := by
  rw [IsTotallyComplex.finrank, Formalism.HN.nPl, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

end GlobalTheory.FrameDeg

namespace GlobalTheory.FrameDeg

theorem deg_eq_neg_log_ht : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [StarRing K] [IsTotallyComplex K] [FiniteDimensional K V] (nm : HermFam K V), nm.IsConjInv → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) → (∀ v x, Formalism.HermitianLatticesTheory.normAt b X v x = nm.nrm v.embedding x) → ∀ L : Submodule (𝓞 K) V, L.FG → deg nm L = -Real.log (Formalism.HN.ht b X L) / (2 * (Formalism.HN.nPl K : ℝ)) := by
  intro K V _ _ _ _ _ _ _ _ _ nm hinv ι _ _ b X hX hnorm L hL
  classical

  have hform : ∀ (v : InfinitePlace K) (x y : V),
      Formalism.HermitianLatticesTheory.majAt b X v x y = nm.form v.embedding x y := by
    intro v
    refine form_eq_of_re_diag v.embedding _ _ (majAt_add_right b X v) (nm.add_right _)
      (majAt_smul_right b X v) (nm.smul_right _) (majAt_conj b X v) (nm.conj_symm _) ?_ ?_
    · intro x
      rw [majAt_self_re, hnorm, HermFam.nrm, Real.sq_sqrt (form_self_re_nonneg nm _ x)]
    · have hc : v.IsComplex := IsTotallyComplex.isComplex v
      rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff] at hc
      by_contra hall
      push_neg at hall
      apply hc
      ext a
      rw [ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_eq_iff_im.mpr (hall a)
  obtain ⟨e, he⟩ := exists_isFrame L hL
  have hdeg := arakelovDegree_eq_degreeOfFamily nm hL he
  obtain ⟨hS, hSL⟩ := Formalism.HN.htGram K V ι b X hX _ e he.2.1
  have hle : Submodule.span (𝓞 K) (Set.range e) ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact he.1 i)
  have hidx := hSL L hL hle rfl
  have hne := he.relIndex_ne_zero hL
  have hgram : ∀ v, Formalism.HN.gramPl b X v e = nm.gram v.embedding e := by
    intro v; ext a c; simp [Formalism.HN.gramPl, HermFam.gram, hform]
  have hpos : ∀ σ, 0 < (nm.gram σ e).det.re := fun σ =>
    (Complex.pos_iff.1 (Matrix.PosDef.det_pos (nm.posDef σ _ e he.2.1))).1
  have hsum : ∑ σ : K →+* ℂ, Real.log (nm.gram σ e).det.re =
      2 * ∑ w : InfinitePlace K, Real.log (nm.gram w.embedding e).det.re := by
    rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have hc : ∀ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => InfinitePlace.mk σ = w),
        Real.log (nm.gram σ e).det.re = Real.log (nm.gram w.embedding e).det.re := by
      intro σ hσ
      rw [Finset.mem_filter] at hσ
      rcases InfinitePlace.mk_eq_iff.mp (hσ.2.trans (InfinitePlace.mk_embedding w).symm) with h | h
      · rw [h]
      · rw [← h, det_gram_conj_re nm hinv]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
      (IsTotallyComplex.isComplex w).mult_eq_two, nsmul_eq_mul]
    push_cast; ring
  have hprod : 0 < ∏ w : InfinitePlace K, (nm.gram w.embedding e).det.re :=
    Finset.prod_pos fun w _ => hpos _
  have hidx' : (0 : ℝ) < ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex
      L.toAddSubgroup : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hne
  have hht : Formalism.HN.ht b X L = (∏ w : InfinitePlace K, (nm.gram w.embedding e).det.re) /
      ((Submodule.span (𝓞 K) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := by
    rw [eq_div_iff hidx'.ne', hidx, hS]
    exact Finset.prod_congr rfl fun w _ => by rw [hgram]
  rw [hdeg, degreeOfFamily, hsum, finrank_eq_two_mul_nPl', hht, Real.log_div hprod.ne' hidx'.ne',
    Real.log_prod (fun w _ => (hpos _).ne')]
  push_cast
  ring

end GlobalTheory.FrameDeg
