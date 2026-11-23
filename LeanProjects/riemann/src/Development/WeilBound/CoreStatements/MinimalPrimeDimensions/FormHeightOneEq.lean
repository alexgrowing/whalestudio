import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TotalDegreeLinSubstLe
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.FormHeightGen
import Development.WeilBound.CoreStatements.NefModelVolumes.ChowFormOfIntegralVersion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SphereMeanEqMahler
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSphereMeanEqOfFrameNormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
import ReciprocityTheory.SemistableReduction.SJCoreD

set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField Matrix GlobalTheory.ChowHt GroundTheory.Heights₂.Heights

namespace ChowFormHeightComparison₂.CF.D

theorem gaussAbs_eq {K : Type} [Field K] [NumberField K] {ι : Type} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (f : MvPolynomial ι K) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs (FinitePlace.equivHeightOneSpectrum.symm v) f = gaussNorm v f := by
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs gaussNorm
  congr 2
  funext s
  apply NNReal.eq
  rw [FinitePlace.equivHeightOneSpectrum_symm_apply]
  show ((‖(FinitePlace.embedding v) (coeff s f)‖).toNNReal : ℝ) = HeightOneSpectrum.adicAbv K v (coeff s f)
  rw [FinitePlace.norm_embedding]
  exact Real.coe_toNNReal _ (AbsoluteValue.nonneg _ _)

theorem mean_eq_mahler {m k : ℕ} (hm : 1 ≤ m) (h : HermNorm m) {f : MvPolynomial (Fin k × Fin m) ℂ} (hf : f ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.blockSphereMean k m (linSubst h.mat⁻¹ f) = mahler h k f := by
  have hB : (h.mat * h.mat⁻¹)ᴴ * (h.mat * h.mat⁻¹) = 1 := by
    rw [Matrix.mul_nonsing_inv _ h.isUnit_det]
    simp
  rw [← GlobalTheory.CompanionTheory.Ar.HS.SphereMean.sphere_mean_eq_mahler m k h h.mat⁻¹ f hm hf hB]
  have hP : ∀ n, ReciprocityTheory.MultiplicativeHeights.sphereProb n = GlobalTheory.CompanionTheory.Ar.HS.Tuple.sphP n := by
    intro n
    unfold ReciprocityTheory.MultiplicativeHeights.sphereProb GlobalTheory.CompanionTheory.Ar.HS.Tuple.sphP
    rw [ProbabilityTheory.cond, MeasureTheory.Measure.restrict_univ]
  have hE : ∀ z : ReciprocityTheory.MultiplicativeHeights.BlockSphere k m,
      eval (ReciprocityTheory.MultiplicativeHeights.blockPoint z) (linSubst h.mat⁻¹ f) =
        eval (fun p : Fin k × Fin m => (h.mat⁻¹ *ᵥ fun a => (↑(z p.1) : EuclideanSpace ℂ (Fin m)).ofLp a) p.2) f := by
    intro z
    unfold linSubst
    rw [MvPolynomial.aeval_eq_bind₁, ← MvPolynomial.coe_aeval_eq_eval, ← MvPolynomial.coe_aeval_eq_eval]
    erw [MvPolynomial.aeval_bind₁]
    refine congrArg (fun g => MvPolynomial.aeval g f) ?_
    funext p
    simp [ReciprocityTheory.MultiplicativeHeights.blockPoint, ReciprocityTheory.MultiplicativeHeights.spherePoint, Matrix.mulVec, dotProduct, mul_comm]
  unfold ReciprocityTheory.MultiplicativeHeights.blockSphereMean ReciprocityTheory.MultiplicativeHeights.blockSphereProb
  simp only [hP, hE]

theorem formHeight_one_eq {K : Type} [Field K] [NumberField K] {m k : ℕ} (hm : 1 ≤ m) (H : ArchData K m) (δ : ℕ)
    {f : MvPolynomial (Fin k × Fin m) K} (hf : f ≠ 0) :
    formHeight δ (1 : Matrix (Fin m) (Fin m) K) (fun σ => (H.normAt σ).mat⁻¹) f = chowHt H k δ f := by
  unfold formHeight chowHt
  rw [GlobalTheory.HeightUnique.linSubst_one, ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K)).symm]
  have e (σ : K →+* ℂ) : ReciprocityTheory.MultiplicativeHeights.blockSphereMean k m (linSubst (H.normAt σ).mat⁻¹ (MvPolynomial.map σ f)) =
      mahler (H.normAt σ) k (MvPolynomial.map σ f) :=
    mean_eq_mahler hm _ fun h0 => hf (MvPolynomial.map_injective σ σ.injective (by rw [h0, map_zero]))
  simp only [gaussAbs_eq, e]
  ring

end ChowFormHeightComparison₂.CF.D

private theorem coneMap_comp_coordSubst {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N N' : ℕ}
    (M : Matrix (Fin N) (Fin N') K) (y : Fin N → Ω) :
    (GlobalTheory.CompHt.coneMap K y).comp (GlobalTheory.CompHt.coordSubst M) =
      GlobalTheory.CompHt.coneMap K (fun k => ∑ j, algebraMap K Ω (M j k) * y j) := by
  apply MvPolynomial.algHom_ext
  intro k
  simp only [AlgHom.comp_apply, GlobalTheory.CompHt.coordSubst, GlobalTheory.CompHt.coneMap, MvPolynomial.aeval_X, map_sum,
    map_mul, MvPolynomial.aeval_C, Polynomial.algebraMap_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem aeval_linSubst {K L : Type} [Field K] [CommRing L] [Algebra K L] {B N n : ℕ}
    (M : Matrix (Fin N) (Fin n) K) (f : MvPolynomial (Fin B × Fin N) K) (u : Fin B × Fin n → L) :
    MvPolynomial.aeval u (linSubst M f) =
      MvPolynomial.aeval (fun p : Fin B × Fin N => ∑ k, algebraMap K L (M p.2 k) * u (p.1, k)) f := by
  unfold linSubst
  rw [MvPolynomial.aeval_eq_bind₁]
  erw [MvPolynomial.aeval_bind₁]
  refine congrArg (fun g => MvPolynomial.aeval g f) ?_
  funext p
  simp [MvPolynomial.aeval_X, MvPolynomial.aeval_C]

private theorem isChowForm_of_isChowFormInt {k : Type} [Field k] {N : ℕ} {I : Ideal (MvPolynomial (Fin N) k)} {e dl : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin N) k} (hf : IsChowFormInt I e dl f) :
    GroundTheory.Heights₂.Heights.IsChowForm I (e + 1) f := by
  refine ⟨hf.ne_zero, fun p => ⟨fun hp => hf.dvd_of_forall_aeval_eq_zero
    (fun u hu => hp u ((hf.zero_iff u).1 hu)), ?_⟩⟩
  rintro ⟨q, rfl⟩ u hu
  rw [map_mul, (hf.zero_iff u).2 hu, zero_mul]

private theorem sum_algebraMap_mul_sum_eq_matrix_mul {K L : Type} [Field K] [CommRing L] [Algebra K L] {a b c : ℕ}
    (M : Matrix (Fin a) (Fin b) K) (P : Matrix (Fin b) (Fin c) K) (z : Fin a → L) (k : Fin c) :
    ∑ j : Fin b, algebraMap K L (P j k) * ∑ i : Fin a, algebraMap K L (M i j) * z i =
      ∑ i, algebraMap K L ((M * P) i k) * z i := by
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem sum_sum_algebraMap_mul_comm {K L : Type} [Field K] [CommRing L] [Algebra K L] {a b : ℕ}
    (g : Matrix (Fin a) (Fin b) K) (v : Fin b → L) (z : Fin a → L) :
    ∑ j, (∑ k, algebraMap K L (g j k) * v k) * z j = ∑ k, v k * ∑ j, algebraMap K L (g j k) * z j := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

private theorem exists_right_inverse_of_span_col_eq_top {K : Type} [Field K] {N m : ℕ} (g : Matrix (Fin N) (Fin m) K)
    (hg : Submodule.span K (Set.range g.col) = ⊤) : ∃ P : Matrix (Fin m) (Fin N) K, g * P = 1 := by
  obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective g.mulVecLin
    (by rw [Matrix.range_mulVecLin, hg])
  refine ⟨LinearMap.toMatrix' r, ?_⟩
  have h1 := congrArg LinearMap.toMatrix' hr
  have h2 : LinearMap.toMatrix' g.mulVecLin = g := LinearMap.toMatrix'_toLin' g
  rw [LinearMap.toMatrix'_comp, h2, LinearMap.toMatrix'_id] at h1
  exact h1

private theorem isMultiHomog_of_isMultiHomogeneous_const {K : Type} [Field K] {B n δ : ℕ} (f : MvPolynomial (Fin B × Fin n) K)
    (hf : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => δ) f) : GroundTheory.Heights₂.Heights.IsMultiHomog δ f := by
  intro s hs
  funext b
  have hb : ∑ j : Fin n, s (b, j) = δ := hf s (MvPolynomial.mem_support_iff.2 hs) b
  rw [← hb, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp [GroundTheory.Heights₂.Heights.groupWeight, Pi.single_apply]

open ChowFormHeightComparison₂.CF.D in

theorem ChowFormHeightComparison₂.CF.stForm : ChowFormHeightComparison₂.CF.StForm := by
  intro K Ω _ _ _ _ d N m δ g A hspan hA y Φ hΦ H hH
  obtain ⟨P, hgP⟩ := exists_right_inverse_of_span_col_eq_top g hspan
  have hne : Φ ≠ 0 := hΦ.ne_zero
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      exfalso
      have hirr := hΦ.irred
      have hC := MvPolynomial.eq_C_of_isEmpty Φ
      have hc : MvPolynomial.coeff 0 Φ ≠ 0 := fun h => hne (by rw [hC, h, map_zero])
      rw [hC] at hirr
      exact hirr.not_isUnit ((isUnit_iff_ne_zero.2 hc).map MvPolynomial.C)
    · exact h0
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      exfalso
      have := congrFun (congrFun hgP ⟨0, hN⟩) ⟨0, hN⟩
      simp [Matrix.mul_apply] at this
    · exact h0
  refine ⟨isChowForm_of_isChowFormInt (dl := δ) ?_, isMultiHomog_of_isMultiHomogeneous_const _ (GlobalTheory.HeightUnique.linSubst_homog g hΦ.homog), ?_⟩
  · refine ⟨GlobalTheory.HeightUnique.linSubst_homog g hΦ.homog, PositivityTheory.UnitarySelfGeneration.UnitProductCombination.irreducible_linSubst hgP hΦ.irred, ?_⟩
    intro u
    rw [aeval_linSubst, hΦ.zero_iff]
    constructor
    · rintro ⟨z, hz0, hzI, hzu⟩
      refine ⟨fun k => ∑ j, algebraMap K (AlgebraicClosure K) (g j k) * z j, ?_, ?_, ?_⟩
      · intro hx
        apply hz0
        have hx' : ∀ k, ∑ j, algebraMap K (AlgebraicClosure K) (g j k) * z j = 0 := fun k => congrFun hx k
        funext i
        have h2 := sum_algebraMap_mul_sum_eq_matrix_mul g P z i
        simp only [hx', mul_zero, Finset.sum_const_zero, hgP, Matrix.one_apply] at h2
        simpa using h2.symm
      · intro h hh
        rw [← GlobalTheory.CompHt.aeval_coordSubst]
        apply hzI
        show GlobalTheory.CompHt.coneMap K y (GlobalTheory.CompHt.coordSubst g h) = 0
        rw [← AlgHom.comp_apply, coneMap_comp_coordSubst]
        exact hh
      · intro i
        exact (sum_sum_algebraMap_mul_comm g (fun k => u (i, k)) z).symm.trans (hzu i)
    · rintro ⟨x, hx0, hxI, hxu⟩
      have hxz : ∀ k, x k = ∑ j, algebraMap K (AlgebraicClosure K) (g j k) *
          ∑ k', algebraMap K (AlgebraicClosure K) (P k' j) * x k' := by
        intro k
        have hl : (MvPolynomial.X k - GlobalTheory.CompHt.coordSubst (P * g) (MvPolynomial.X k)) ∈
            GlobalTheory.CompHt.coneIdeal K (fun k => ∑ j, algebraMap K Ω (g j k) * y j) := by
          show GlobalTheory.CompHt.coneMap K _ _ = 0
          have e : (fun k => ∑ j, algebraMap K Ω ((P * g) j k) * ∑ i, algebraMap K Ω (g i j) * y i) =
              fun k => ∑ i, algebraMap K Ω (g i k) * y i := by
            funext k
            rw [sum_algebraMap_mul_sum_eq_matrix_mul, ← Matrix.mul_assoc, hgP, Matrix.one_mul]
          rw [map_sub, ← AlgHom.comp_apply, coneMap_comp_coordSubst, e, sub_self]
        have h3 := hxI _ hl
        rw [map_sub, GlobalTheory.CompHt.aeval_coordSubst, MvPolynomial.aeval_X, MvPolynomial.aeval_X, sub_eq_zero] at h3
        rw [h3]
        exact (sum_algebraMap_mul_sum_eq_matrix_mul P g x k).symm
      refine ⟨fun j => ∑ k', algebraMap K (AlgebraicClosure K) (P k' j) * x k', ?_, ?_, ?_⟩
      · intro hz
        apply hx0
        have hz' : ∀ j, ∑ k', algebraMap K (AlgebraicClosure K) (P k' j) * x k' = 0 := fun j => congrFun hz j
        funext k
        rw [hxz k]
        simp [hz']
      · intro h hh
        rw [← GlobalTheory.CompHt.aeval_coordSubst]
        apply hxI
        show GlobalTheory.CompHt.coneMap K _ (GlobalTheory.CompHt.coordSubst P h) = 0
        have e : (fun k => ∑ j, algebraMap K Ω (P j k) * ∑ i, algebraMap K Ω (g i j) * y i) = y := by
          funext k
          rw [sum_algebraMap_mul_sum_eq_matrix_mul, hgP]
          simp [Matrix.one_apply]
        rw [← AlgHom.comp_apply, coneMap_comp_coordSubst, e]
        exact hh
      · intro i
        refine (sum_sum_algebraMap_mul_comm g (fun k => u (i, k)) _).trans ?_
        simp only [← hxz]
        exact hxu i
  · rw [← PositivityTheory.UnitarySelfGeneration.UnitProductCombination.formHeight_gen hN g hspan A hA (fun σ => (H.normAt σ).mat⁻¹) ?_ hne hΦ.homog,
      formHeight_one_eq hm H δ (GlobalTheory.HeightUnique.linSubst_ne_zero hgP hne)]
    intro σ x
    have h1 := hH σ x
    unfold GroundTheory.Heights₂.Heights.HermNorm.dualNorm at h1
    rw [← h1, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp [Matrix.mulVec, dotProduct, ← Matrix.transpose_nonsing_inv]
