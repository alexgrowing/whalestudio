import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqOrConjOfPlaceOf
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
namespace GlobalTheory.WittLevi

variable {D : D7}

theorem exists_hypDec (S : HSp D) {r : ℕ} (e e' : Matrix (Fin S.rank) (Fin r) D.host.E)
    (hee : eᴴ * S.gram * e = 0) (he'e' : e'ᴴ * S.gram * e' = 0) (he'e : e'ᴴ * S.gram * e = 1) :
    ∃ (S₀ : HSp D) (d : GlobalTheory.MixModel.HypDec S S₀ r), d.e = e ∧ d.e' = e' := by
  obtain ⟨ev, hev⟩ := GlobalTheory.BesselCompare.eMat_surj S e
  obtain ⟨ev', hev'⟩ := GlobalTheory.BesselCompare.eMat_surj S e'
  have hG : (HSpace.gram S)ᴴ = HSpace.gram S := GlobalTheory.MixModel.gram_conjTranspose S
  have hpair : ∀ i j, S.hT (ev' i) (ev j) = if i = j then 1 else 0 := fun i j => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hev, hev']
    exact congrFun (congrFun he'e i) j
  have hli : LinearIndependent D.host.E ev := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h := congrArg (S.hT (ev' i)) hc
    rw [map_sum, map_zero] at h
    simp only [map_smul, hpair, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true] at h
    exact h
  have hiso : ∀ a b, S.hT (ev a) (ev b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hev]
    exact congrFun (congrFun hee a) b
  obtain ⟨V', ι, hrk, hι, horth⟩ :=
    GlobalTheory.WittLow.exists_lower Formalism.BasicNotions.Examples₂.star_isIntegral S ev hli hiso
  set B := frameMat S V' ι with hB
  have hBB : Bᴴ * S.gram * B = V'.gram := GlobalTheory.AutFunCounterexample.gram_pull S V' ι hι
  have hBe : Bᴴ * S.gram * e = 0 := by
    refine Matrix.ext fun i a => ?_
    have h := GlobalTheory.BesselCompare.cT_mul S (fun i => ι (V'.frame i)) ev i a
    rw [← GlobalTheory.BesselCompare.frameMat_eq, hev] at h
    rw [hB]
    exact h.trans (horth _ _)
  set K := e'ᴴ * S.gram * B with hK
  have hKh : Kᴴ = Bᴴ * (S.gram * e') := by
    rw [hK, conjTranspose_mul, conjTranspose_mul, hG, conjTranspose_conjTranspose]
  have f1 : Bᴴ * (S.gram * e) = 0 := by rw [← Matrix.mul_assoc]; exact hBe
  have f2 : eᴴ * (S.gram * B) = 0 := by
    have := congrArg conjTranspose hBe
    rw [conjTranspose_mul, conjTranspose_mul, hG, conjTranspose_conjTranspose, conjTranspose_zero] at this
    exact this
  have f3 : eᴴ * (S.gram * e) = 0 := by rw [← Matrix.mul_assoc]; exact hee
  have f4 : eᴴ * (S.gram * e') = 1 := by
    have := congrArg conjTranspose he'e
    rw [conjTranspose_mul, conjTranspose_mul, hG, conjTranspose_conjTranspose, conjTranspose_one] at this
    exact this
  have g1 : ∀ {k : ℕ} (X : Matrix (Fin r) (Fin k) D.host.E), Bᴴ * (S.gram * (e * X)) = 0 := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBe, Matrix.zero_mul]
  have g3 : ∀ {k : ℕ} (X : Matrix (Fin r) (Fin k) D.host.E), eᴴ * (S.gram * (e * X)) = 0 := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hee, Matrix.zero_mul]
  refine ⟨V', GlobalTheory.MixModel.HypDec.mk e e' (B - e * K) hee he'e' he'e ?_ ?_ ?_ hrk, rfl, rfl⟩
  · rw [conjTranspose_sub, conjTranspose_mul, hKh]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, f1, f2, f3, g1, g3, Matrix.mul_zero, sub_zero]
    rw [← Matrix.mul_assoc, hBB]
  · rw [conjTranspose_sub, conjTranspose_mul, hKh]
    simp only [Matrix.sub_mul, Matrix.mul_assoc, f1, f3, Matrix.mul_zero, sub_zero]
  · rw [conjTranspose_sub, conjTranspose_mul, hKh]
    simp only [Matrix.sub_mul, Matrix.mul_assoc, f4, Matrix.mul_one, sub_self]

end GlobalTheory.WittLevi

noncomputable section

namespace GlobalTheory.WittLevi

open GlobalTheory.AdelicU

variable {D : D7}

def realAd (D : D7) : ℝ →* AF D.host.F where
  toFun x := ((fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm x :
      Ainf D.host.F), (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F))
  map_one' := Prod.ext (funext fun w => map_one _) rfl
  map_mul' x y := Prod.ext (funext fun w => map_mul _ _ _) (mul_one _).symm

def realE (D : D7) : ℝ →* AE D :=
  ((Algebra.TensorProduct.includeLeftRingHom : AF D.host.F →+* AF D.host.F ⊗[D.host.F] D.host.E) :
    AF D.host.F →* AF D.host.F ⊗[D.host.F] D.host.E).comp (realAd D)

theorem finPart_realE (x : ℝ) : finPart D (realE D x) = 1 := rfl

theorem cA_realE (x : ℝ) : cA D (realE D x) = realE D x := by
  change (realAd D x) ⊗ₜ[D.host.F] (D.sp.cm.sig (1 : D.host.E)) = (realAd D x) ⊗ₜ[D.host.F] (1 : D.host.E)
  rw [map_one]

theorem infEmb_realE {w : InfinitePlace D.host.F} (τ : EmbOver D.host.E w) (x : ℝ) :
    infEmb τ (compInf D.host.F D.host.E w (realE D x)) = x := by
  change infEmb τ ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm x ⊗ₜ[D.host.F] 1) = _
  rw [infEmb_tmul, map_one, mul_one,
    ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
  exact congrArg _ ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply x)

theorem infEmb_incA {w : InfinitePlace D.host.F} (τ : EmbOver D.host.E w) (x : D.host.E) :
    infEmb τ (compInf D.host.F D.host.E w (incA D x)) = τ.1 x := by
  change infEmb τ (evInf D.host.F w 1 ⊗ₜ[D.host.F] x) = _
  simp

theorem theta_realE {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (x : ℝ) :
    θ ρ (infPart D (realE D x)) = x := by
  rw [eq_infProj hθ (embOverOf D ρ) rfl]
  exact infEmb_realE (embOverOf D ρ) x

theorem mat_ext {m k : ℕ} {P Q : Matrix (Fin m) (Fin k) (AE D)} (hf : P.map (finPart D) = Q.map (finPart D))
    (hi : ∀ (w : InfinitePlace D.host.F) (τ : EmbOver D.host.E w),
      P.map ((infEmb τ).comp (compInf D.host.F D.host.E w)) = Q.map ((infEmb τ).comp (compInf D.host.F D.host.E w))) :
    P = Q := by
  refine Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext ?_ (congrFun (congrFun hf i) j)
  refine GlobalTheory.AutFunCompare.infTens_ext fun w => ?_
  obtain ⟨ρ, rfl⟩ := (placeOf_bijective D).2 w
  apply (infEmb_bijective (isCMExt_host D) (embOverOf D ρ)).1
  exact (GlobalTheory.Doubling.infProj_fst (embOverOf D ρ) (P i j)).trans
    ((congrFun (congrFun (hi _ (embOverOf D ρ)) i) j).trans (GlobalTheory.Doubling.infProj_fst (embOverOf D ρ) (Q i j)).symm)

end GlobalTheory.WittLevi

end

noncomputable section

namespace GlobalTheory.WittLevi

open GlobalTheory.AdelicU

variable {D : D7}

def torusMat {r : ℕ} (t : Fin r → ℝ) (ht : ∀ i, t i ≠ 0) : GL (Fin r) (AE D) :=
  ⟨diagonal fun i => realE D (t i), diagonal fun i => realE D (t i)⁻¹,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; exact congrArg diagonal (funext fun i => by
      rw [← map_mul, mul_inv_cancel₀ (ht i), map_one]),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; exact congrArg diagonal (funext fun i => by
      rw [← map_mul, inv_mul_cancel₀ (ht i), map_one])⟩

theorem torusMat_val {r : ℕ} (t : Fin r → ℝ) (ht : ∀ i, t i ≠ 0) :
    (torusMat (D := D) t ht).1 = diagonal fun i => realE D (t i) := rfl

theorem adj_torusMat_inv {r : ℕ} (t : Fin r → ℝ) (ht : ∀ i, t i ≠ 0) :
    GlobalTheory.MixModel.adj ((torusMat (D := D) t ht)⁻¹).1 = diagonal fun i => realE D (t i)⁻¹ := by
  change (Matrix.map (diagonal fun i => realE D (t i)⁻¹) (cA D))ᵀ = _
  rw [diagonal_map (RingHom.map_zero _), diagonal_transpose]
  exact congrArg diagonal (funext fun i => cA_realE _)

theorem map_diag_fin {r : ℕ} (x : Fin r → ℝ) :
    (diagonal fun i => realE D (x i)).map (finPart D) = 1 := by
  rw [diagonal_map (RingHom.map_zero _), ← diagonal_one]
  exact congrArg diagonal (funext fun i => finPart_realE _)

theorem map_diag_inf {r : ℕ} {w : InfinitePlace D.host.F} (τ : EmbOver D.host.E w) (x : Fin r → ℝ) :
    (diagonal fun i => realE D (x i)).map ((infEmb τ).comp (compInf D.host.F D.host.E w)) =
      diagonal fun i => (x i : ℂ) := by
  rw [diagonal_map (RingHom.map_zero _)]
  exact congrArg diagonal (funext fun i => infEmb_realE τ _)

theorem map_rat_inf {m k : ℕ} {w : InfinitePlace D.host.F} (τ : EmbOver D.host.E w)
    (Z : Matrix (Fin m) (Fin k) D.host.E) :
    (Z.map (incA D)).map ((infEmb τ).comp (compInf D.host.F D.host.E w)) = Z.map τ.1 :=
  Matrix.ext fun _ _ => infEmb_incA τ _

theorem mt_mul_rat (M : HSp D) (a : GA D M) (ha : a ∈ infPts D.sp.cm.sig M.gram) {k : ℕ}
    (Z : Matrix (Fin M.rank) (Fin k) D.host.E) (P : Matrix (Fin k) (Fin k) (AE D)) (hP : P.map (finPart D) = 1)
    (h : ∀ (w : InfinitePlace D.host.F) (τ : EmbOver D.host.E w),
      GlobalTheory.Orb.archMat D.sp.cm.sig M.gram τ (projArch D.sp.cm.sig M.gram w a) * Z.map τ.1 =
        Z.map τ.1 * P.map ((infEmb τ).comp (compInf D.host.F D.host.E w))) :
    HMul.hMul (Formalism.L2.Theta.mt M a) (Z.map (incA D) : Mx D M.rank k) = HMul.hMul (Z.map (incA D) : Mx D M.rank k) P := by
  have hfin : (Formalism.L2.Theta.mt M a).map (finPart D) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 ha)
  refine mat_ext ?_ fun w τ => ?_
  · rw [Matrix.map_mul, Matrix.map_mul, hfin, hP, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.map_mul, Matrix.map_mul, map_rat_inf]
    exact h w τ

theorem witt_levi : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (M : HSp D) (r : ℕ)
    (Xf Yf : Matrix (Fin M.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig M.gram Xf Yf →
    ∃ (S₀ : HSp D) (d : GlobalTheory.MixModel.HypDec (sgn ε M) S₀ r), ∀ t : Fin r → ℝ, (∀ i, 0 < t i) →
      ∀ a, GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig M.gram Xf Yf t a →
        ∃ α : GL (Fin r) (Formalism.L2.Theta.AE D), α.1.map (finPart D) = 1 ∧
          (∀ τ, compAt θ τ α.1 = diagonal (fun i => (t i : ℂ))) ∧ (ofSgn ε M).symm a = d.levi α := by
  intro D θ hθ ε M r Xf Yf hW
  set s : D.host.E := bif ε then -1 else 1 with hs
  have hgram : HSpace.gram (sgn ε M) = s • HSpace.gram M := by
    cases ε <;> refine Matrix.ext fun i j => ?_ <;> simp [HSpace.gram, sgn, hs]
  have hss : star s * s = 1 := by cases ε <;> simp [hs]
  have hs0 : s ≠ 0 := by cases ε <;> simp [hs]
  have hG : (HSpace.gram M)ᴴ = HSpace.gram M := GlobalTheory.MixModel.gram_conjTranspose M
  have hxx : Xfᴴ * M.gram * Xf = 0 := hW.xx
  have hyy : Yfᴴ * M.gram * Yf = 0 := hW.yy
  have hxy : Xfᴴ * M.gram * Yf = 1 := hW.xy
  have hyx : Yfᴴ * M.gram * Xf = 1 := by
    have := congrArg conjTranspose hxy
    rw [conjTranspose_mul, conjTranspose_mul, hG, conjTranspose_conjTranspose, conjTranspose_one,
      ← Matrix.mul_assoc] at this
    exact this
  obtain ⟨S₀, d, hde, hde'⟩ := exists_hypDec (sgn ε M) Xf (s • Yf)
    (by rw [hgram, Matrix.mul_smul, Matrix.smul_mul, hxx, smul_zero])
    (by rw [hgram, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, hyy, smul_zero, smul_zero, smul_zero])
    (by
      have hss' : s * star s = 1 := by rw [mul_comm]; exact hss
      simp only [hgram, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hyx, hss, hss', one_smul])
  refine ⟨S₀, d, fun t ht a ha => ?_⟩
  have ht0 : ∀ i, t i ≠ 0 := fun i => (ht i).ne'

  have hG' : (HSpace.gram (sgn ε M))ᴴ = HSpace.gram (sgn ε M) := GlobalTheory.MixModel.gram_conjTranspose _
  have h0X : Xfᴴ * M.gram * d.i₀ = 0 := by
    have := congrArg conjTranspose d.i₀e
    rw [conjTranspose_mul, conjTranspose_mul, hG', conjTranspose_conjTranspose, conjTranspose_zero, hde, hgram,
      Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc] at this
    exact (smul_eq_zero.1 this).resolve_left hs0
  have h0Y : Yfᴴ * M.gram * d.i₀ = 0 := by
    have := congrArg conjTranspose d.i₀e'
    rw [conjTranspose_mul, conjTranspose_mul, hG', conjTranspose_conjTranspose, conjTranspose_zero, hde', hgram,
      conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, one_smul,
      ← Matrix.mul_assoc] at this
    exact this
  have hmt : Formalism.L2.Theta.mt (sgn ε M) ((ofSgn ε M).symm a) = Formalism.L2.Theta.mt M a := by
    rw [← mt_ofSgn, MulEquiv.apply_symm_apply]
  refine ⟨torusMat t ht0, map_diag_fin t, fun τ => ?_, ?_⟩
  · change (diagonal fun i => realE D (t i)).map (fun x => θ τ (infPart D x)) = _
    rw [diagonal_map (by simp)]
    exact congrArg diagonal (funext fun i => theta_realE hθ τ _)
  apply d.ga_ext
  · rw [hmt, d.levi_jX]
    simp only [GlobalTheory.MixModel.HypDec.jX, GlobalTheory.MixModel.rat, hde, torusMat_val]
    exact mt_mul_rat M a ha.1 Xf _ (map_diag_fin t) fun w τ => by
      rw [map_diag_inf]; exact (ha.2 w τ).1
  · rw [hmt, d.wittDecomp_levi_inclAnisotropic]
    obtain ⟨I, hI⟩ : ∃ I : Matrix (Fin M.rank) (Fin S₀.rank) D.host.E, I = d.i₀ := ⟨d.i₀, rfl⟩
    rw [← hI] at h0X h0Y
    have key := mt_mul_rat M a ha.1 I (1 : Matrix (Fin S₀.rank) (Fin S₀.rank) (AE D)) (Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)) fun w τ => by
      rw [Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.mul_one]
      refine Matrix.ext fun l j => ?_
      have hz := (ha.2 w τ).2.2 (fun k => I k j) (funext fun l => congrFun (congrFun h0X l) j)
        (funext fun l => congrFun (congrFun h0Y l) j)
      exact congrFun hz l
    rw [Matrix.mul_one] at key
    simp only [GlobalTheory.MixModel.HypDec.j0, GlobalTheory.MixModel.rat, ← hI]
    exact key
  · rw [hmt, d.levi_jY, adj_torusMat_inv]
    simp only [GlobalTheory.MixModel.HypDec.jY, GlobalTheory.MixModel.rat, hde']
    exact mt_mul_rat M a ha.1 (s • Yf) _ (map_diag_fin _) fun w τ => by
      rw [map_diag_inf]
      have hsY : (s • Yf).map τ.1 = τ.1 s • Yf.map τ.1 := Matrix.ext fun _ _ => by simp
      rw [hsY, Matrix.mul_smul, Matrix.smul_mul, (ha.2 w τ).2.1]
      congr 2
      exact congrArg diagonal (funext fun i => (Complex.ofReal_inv _).symm)

end GlobalTheory.WittLevi

end
