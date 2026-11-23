import Mathlib
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPartLevelFormInfinitePlaceEqClassSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIdempotentMulLevelProjMulGoodPartEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumMetricEqGramAtInfinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumPrincipalLevelEqCardMulClassSumStatement
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

theorem GlobalTheory.ClassSumLevel.normAt_sq_of_frame {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (X0 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K)
    (F : Fin n → K) (h2 : ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = H.map v.embedding) :
    ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X0 v F ^ 2 : ℝ) : ℂ) =
      star (fun i => v.embedding (F i)) ⬝ᵥ (H.map v.embedding *ᵥ fun i => v.embedding (F i)) := by
  have hw : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v F = fun i => v.embedding (F i) := by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  rw [← h2, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, Formalism.HermitianLatticesTheory.normAt,
    Formalism.HermitianLatticesTheory.fcoord, hw, Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  rfl

theorem GlobalTheory.ClassSumLevel.dot_smul_sandwich {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (M : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (x : Fin n → ℂ) : star x ⬝ᵥ ((c • (A.conjTranspose * M * A)) *ᵥ x) = c * (star (A *ᵥ x) ⬝ᵥ (M *ᵥ (A *ᵥ x))) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem GlobalTheory.ClassSumLevel.classSum_le_normAt_sq : ∀ (X : Fields) [IsTotallyComplex X.K] (Pr : Primes X) (R : Ranks) (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (hX : X.Ok) (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S)) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (trIv : Fin R.m → (LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) (P : LevFam X.E X.K R.r Pr.vGs) (Zs : DefSub (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.amb3) (t : TupF TU) (hP : (mtildeGSD W Ch sel t.1 P).Ok), (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3.Ok3 1 → ∀ (F : Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t) → X.K) (F' : (mtildeKGSD W Ch sel t.1).EqFun), F'.1 ∈ (mtildeGSD W Ch sel t.1 P).EqFun → HEq ((mtildeKGSD W Ch sel t.1).res (mtildeKOk W Ch sel t.1 hX) F') (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.basis.equivFun.symm ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.cutE ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r (lvlIdem ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).P ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).ψ)).mulVec ((((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).S.lvlPr ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).r ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).P ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr).ψ * ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.R t).vE ((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.fam.lvl P.grp P.chr)).mulVec F))) → ∀ (v : InfinitePlace X.K) (X0 : InfinitePlace X.K → Matrix (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t)) (Fin (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).nV t)) ℂ), IsUnit (X0 v).det → ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = (((colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs).HV t).map v.embedding → ((mtildeGSD W Ch sel t.1 P).ipAt hP v F'.1 F'.1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K _) X0 v F ^ 2 := by
  intro X _ Pr R W Ch sel S hX v0 TU Xg S0 xiVal trIv P Zs t hP hOk F F' hF' hEq v X0 hdet hframe
  set A := colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv with hA
  have hBH : BlockHyp (A.A.fam.R t) (A.A.fam.lvl P.grp P.chr) A.A.fam.v0 1 := ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ t⟩
  have hC := GlobalTheory.T.levelIdempotent_mul_levelProj_mul_goodPart_eq _ _ _ _ hBH
  have hres : (mtildeKGSD W Ch sel t.1).res (mtildeKOk W Ch sel t.1 hX) F' =
      (A.A.fam.R t).S.basis.equivFun.symm ((A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr) *ᵥ F) := by
    have h1 := eq_of_heq hEq
    have h2 : (A.A.fam.R t).S.lvlE (A.A.fam.R t).r (A.A.fam.lvl P.grp P.chr).P (A.A.fam.lvl P.grp P.chr).ψ *ᵥ
        (((A.A.fam.R t).S.lvlPr (A.A.fam.R t).r (A.A.fam.lvl P.grp P.chr).P (A.A.fam.lvl P.grp P.chr).ψ *
          (A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr)) *ᵥ F) = (A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr) *ᵥ F := by
      refine (Matrix.mulVec_mulVec _ _ _).trans ?_
      rw [← Matrix.mul_assoc]
      exact congrArg (· *ᵥ F) hC
    rw [h1]
    exact congrArg _ h2
  have hD := GlobalTheory.T.classSumMetric_eq_gram_at_infinitePlace (mtildeKGSD W Ch sel t.1) (mtildeKOk W Ch sel t.1 hX)
    (mtildeK_rat W Ch sel t.1 hX) v F'
  have hE := GlobalTheory.T.classSum_principalLevel_eq_card_mul_classSum W Ch sel t.1 P hX v F' hF'
  have hN := GlobalTheory.ClassSumLevel.normAt_sq_of_frame _ X0 v F hframe
  have hV := GlobalTheory.T.goodPart_levelForm_infinitePlace_eq_classSum _ _ _ _ hBH v
  have hcard : (Nat.card (A.A.fam.lvl P.grp P.chr).P : ℂ) = (Nat.card P.grp : ℂ) := rfl
  have hne : (Nat.card P.grp : ℂ) ≠ 0 := by
    rw [← hcard]
    exact_mod_cast (Nat.card_pos (α := (A.A.fam.lvl P.grp P.chr).P)).ne'
  have hy0 : ((mtildeKGSD W Ch sel t.1).toCSD (mtildeKOk W Ch sel t.1 hX)).basis.equivFun
      ((A.A.fam.R t).S.basis.equivFun.symm ((A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr) *ᵥ F)) =
      (A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr) *ᵥ F := LinearEquiv.apply_symm_apply _ _
  rw [hres, hy0] at hD
  have hN' : ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K _) X0 v F ^ 2 : ℝ) : ℂ) =
      star (fun i => v.embedding (F i)) ⬝ᵥ (((A.A.fam.R t).HV (A.A.fam.lvl P.grp P.chr)).map v.embedding *ᵥ
        fun i => v.embedding (F i)) := hN
  rw [hV, hcard] at hN'
  have hy : (fun i => v.embedding (((A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr) *ᵥ F) i)) =
      ((A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr)).map v.embedding *ᵥ fun i => v.embedding (F i) := by
    funext i
    exact RingHom.map_mulVec v.embedding _ _ i
  have hD1 : (mtildeKGSD W Ch sel t.1).ipAt (mtildeKOk W Ch sel t.1 hX) v F'.1 F'.1 =
      star (fun i => v.embedding (((A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr) *ᵥ F) i)) ⬝ᵥ
        ((A.A.fam.R t).S.H.map v.embedding *ᵥ
          fun i => v.embedding (((A.A.fam.R t).vE (A.A.fam.lvl P.grp P.chr) *ᵥ F) i)) := hD
  rw [hy] at hD1
  have key : ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K _) X0 v F ^ 2 : ℝ) : ℂ) =
      (Nat.card P.grp : ℂ)⁻¹ * (mtildeKGSD W Ch sel t.1).ipAt (mtildeKOk W Ch sel t.1 hX) v F'.1 F'.1 := by
    refine hN'.trans ((GlobalTheory.ClassSumLevel.dot_smul_sandwich _ _ _ _).trans ?_)
    exact congrArg _ hD1.symm
  have hP' : (mtildeGSD W Ch sel t.1 P).ipAt hP v F'.1 F'.1 =
      (Nat.card P.grp : ℂ)⁻¹ * (mtildeKGSD W Ch sel t.1).ipAt (mtildeKOk W Ch sel t.1 hX) v F'.1 F'.1 := by
    rw [hE, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hfin : ((mtildeGSD W Ch sel t.1 P).ipAt hP v F'.1 F'.1).re =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K _) X0 v F ^ 2 := by
    rw [hP', ← key]
    exact Complex.ofReal_re _
  exact hfin.le
