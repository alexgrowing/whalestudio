import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqScaledThetaJets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHermitianFormScaledCoordinateEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntireStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockMonomialAtOriginGaussianEntireOrthonormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVacuumConjOfNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UnitaryDatumNumbersForSupBounds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergRootSmulFiniteRationalLatticeDecompStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DeltaOrthonormalCoordsMemLatticeOfFiniteRationalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntireEqOfMonomialDerivationsAtZeroEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateFiniteRationalRealGaussianStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualImageOrthonormalFrameLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.HeisTrans
open GlobalTheory.FockPos

variable {D : D7}

theorem latO_negSp_le (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem applyAt0_scale {N N' : ℕ} (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ) (hG : Differentiable ℂ G) (c a : ℂ)
    (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) (fun z => c * G (a • z)) =
      c * a ^ (k.sum fun _ n => n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G := by
  have hc : ContDiff ℂ (Multiset.card (Finsupp.toMultiset k)) (fun z : Formalism.MainNotions.TaylorLogMetric.VC D N N' => G (a • z)) :=
    ((ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff hG).comp (contDiff_const_smul a)).of_le (by exact_mod_cast le_top)
  have h1 : Formalism.MainNotions.TaylorLogMetric.taylor D (fun z => c * G (a • z)) k = c * Formalism.MainNotions.TaylorLogMetric.taylor D (fun z => G (a • z)) k := by
    unfold Formalism.MainNotions.TaylorLogMetric.taylor
    have e : (fun z : Formalism.MainNotions.TaylorLogMetric.VC D N N' => c * G (a • z)) = c • (fun z => G (a • z)) := rfl
    rw [e, iteratedFDeriv_const_smul_apply (hc.contDiffAt)]
    simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]
  rw [applyAt0_monomial', applyAt0_monomial', h1, taylor_comp_smul' D G hG a k]
  ring

end GlobalTheory.HeisTrans

namespace GlobalTheory.HeisTrans
open GlobalTheory.FockPos

variable {D : D7}

theorem core (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1)
    (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hLs : SD D Ls) (hLt : SD D Lt) (δ : ℂ) (hδ : δ ≠ 0)
    (Θ₀ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ) (hΘ : Differentiable ℂ Θ₀) (c : ℂ) (F : WO S T → ℂ)
    (hF : IsVacO ψ θ S T sS sT (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) F)
    (hj : ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) F
      (MvPolynomial.monomial k 1) 0 =
        c * ((k.prod fun v e => GlobalTheory.FunObj.period δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ₀))
    (n : ℕ) (hn : 0 < n) (w : WO S T)
    (hw : n • w ∈ latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True)) :
    ∃ (ζ : ℂ) (s : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      n • s ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt ∧
      ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT)
        (heisO ψ S T w F) (MvPolynomial.monomial k 1) 0 =
        c * ((k.prod fun v e => GlobalTheory.FunObj.period δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1)
          (fun z => ζ * Formalism.MainNotions.TaylorLogMetric.U D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) s Θ₀ z)) := by
  obtain rfl := cart_one frS hS hcS
  obtain rfl := cart_one frT hT hcT
  have hψ : IsStdChar D ψ (-1) := hF.1
  have hθ : IsInfFam θ := hF.2.inf
  obtain ⟨ΛS, hΛSe, hΛS⟩ := GlobalTheory.T.isSelfDual_image_orthonormalFrame_lattice S frS hS Ls hLs
  obtain ⟨ΛT, hΛTe, hΛT⟩ := GlobalTheory.T.isSelfDual_image_orthonormalFrame_lattice T frT hT Lt hLt
  rw [← hΛSe, ← hΛTe] at hF hw
  obtain ⟨M, ζ, hζ, hnM, heq⟩ := GlobalTheory.T.heisenberg_root_smul_finiteRational_latticeDecomp ψ S T ΛS ΛT hψ hΛS hΛT F hF.2.lat n hn w hw
  rw [hΛSe, hΛTe] at hnM
  obtain ⟨Φ, hΦd, hΦ⟩ := GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire ψ θ S T frS frT _ _ hS hT F hF
  set sc : ℂ := (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) with hsc
  have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ = δ * sc := fun τ => by
    rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
  have hprod : ∀ k : FVar D T.rank S.rank →₀ ℕ,
      (k.prod fun v e => GlobalTheory.FunObj.period δ v.1 ^ e) = (δ * sc) ^ (k.sum fun _ n => n) := fun k => by
    simp only [hper, Finsupp.prod, Finsupp.sum]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  have hsc0 : sc ≠ 0 := by
    rw [hsc]
    refine inv_ne_zero ?_
    have hx : 0 < Formalism.L2.Pj.xiR D := GlobalTheory.SupDict.xiR_pos D
    exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
  have hΦeq : Φ = fun z => c * Θ₀ (δ • z) := by
    refine GlobalTheory.T.entire_eq_of_monomial_derivations_at_zero_eq Φ _ hΦd ((hΘ.comp (differentiable_id.const_smul δ)).const_mul c) fun k => ?_
    have h1 := GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal ψ θ S T frS frT hψ hθ hS hT F Φ hΦd hΦ k
    have h2 := hj k
    rw [applyAt0_scale Θ₀ hΘ c δ k]
    refine mul_left_cancel₀ (pow_ne_zero (k.sum fun _ n => n) hsc0) ?_
    rw [← h1, h2, hprod, mul_pow]
    ring
  set X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := fun τ a b =>
    -(((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T M τ) * GlobalTheory.FockPos.frAt frS τ) a b) with hX
  have hR := GlobalTheory.T.heisenbergTranslate_finiteRational_realGaussian ψ θ S T frS frT hS hT hψ hθ F hF.2.theta Φ hΦ M X hX
  set Φ₁ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ := fun Z => ζ * (Φ (Z + X) *
    Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
      (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2)) with hΦ₁
  have hR' : ∀ w' : WO S T, w'.map (finPart D) = 0 →
      heisO ψ S T w F w' = GlobalTheory.FockPos.gaussO θ frS frT w' * Φ₁ (GlobalTheory.FockPos.zCo θ frS frT w') := by
    intro w' hw'
    rw [heq, Pi.smul_apply, smul_eq_mul, hR w' hw', hΦ₁]
    ring
  set G : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ := fun z => ζ * Formalism.MainNotions.TaylorLogMetric.U D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X) Θ₀ z
    with hGdef
  have hGd : Differentiable ℂ G := by
    have h : Differentiable ℂ (fun z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank =>
        Formalism.MainNotions.TaylorLogMetric.Hf D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) z (δ • X)) := by
      unfold Formalism.MainNotions.TaylorLogMetric.Hf
      fun_prop
    have h2 : Differentiable ℂ (Formalism.MainNotions.TaylorLogMetric.U D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X) Θ₀) := by
      unfold Formalism.MainNotions.TaylorLogMetric.U
      fun_prop
    exact h2.const_mul ζ
  have hΦ₁eq : Φ₁ = fun Z => c * G (δ • Z) := by
    funext Z
    simp only [hΦ₁, hGdef, hΦeq, Formalism.MainNotions.TaylorLogMetric.U]
    rw [GlobalTheory.ThetaLawOF.torusHermitianForm_scaled_coordinate_eq hδ, GlobalTheory.ThetaLawOF.torusHermitianForm_scaled_coordinate_eq hδ, smul_add]
    ring
  have hΦ₁d : Differentiable ℂ Φ₁ := by
    rw [hΦ₁eq]
    exact (hGd.comp (differentiable_id.const_smul δ)).const_mul c
  refine ⟨ζ, δ • X, hζ, ?_, fun k => ?_⟩
  · have hv : GlobalTheory.VacUnique.finRat S T (-(n • M)) ∈
        latO S T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True) := by
      rw [map_neg]; exact neg_mem hnM
    have := GlobalTheory.T.delta_orthonormalCoords_mem_lattice_of_finiteRational S T frS frT hS hT Ls Lt hLs hLt δ (-(n • M)) hv
    convert this using 1
    have e : ∀ τ, Matrix.of (GlobalTheory.VacUnique.infRat S T (-(n • M)) τ) =
        -((n : ℂ) • Matrix.of (GlobalTheory.VacUnique.infRat S T M τ)) := by
      intro τ; ext i j; simp [map_neg, map_nsmul, nsmul_eq_mul]
    funext τ a b
    simp only [e, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.neg_apply, Matrix.smul_apply,
      smul_eq_mul, Pi.smul_apply, hX, nsmul_eq_mul]
    ring
  · rw [GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal ψ θ S T frS frT hψ hθ hS hT _ Φ₁ hΦ₁d hR' k, hΦ₁eq, applyAt0_scale G hGd c δ k, hprod, mul_pow]
    ring

end GlobalTheory.HeisTrans

namespace GlobalTheory.HeisTrans
open GlobalTheory.FockPos

variable {D : D7}

theorem coreNeg (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (hT : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1)
    (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hLs : SD D Ls) (hLt : SD D Lt) (δ : ℂ) (hδ : δ ≠ 0)
    (Θ₀ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ) (hΘ : Differentiable ℂ Θ₀) (c : ℂ) (F : WO (negSp S) T → ℂ)
    (hF : IsVacO ψ θ (negSp S) T (fun τ => -sS τ) sT (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) F)
    (hj : ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT (GlobalTheory.FockPos.frAt frS)
      (GlobalTheory.FockPos.frAt frT) F (MvPolynomial.monomial k 1) 0 =
        c * starRingEnd ℂ ((k.prod fun v e => GlobalTheory.FunObj.period δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ₀))
    (n : ℕ) (hn : 0 < n) (w : WO S T)
    (hw : n • w ∈ latO (negSp S) T (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) (fun _ => True)) :
    ∃ (ζ : ℂ) (s : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      n • s ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt ∧
      ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT (GlobalTheory.FockPos.frAt frS)
        (GlobalTheory.FockPos.frAt frT) (heisO ψ (negSp S) T w F) (MvPolynomial.monomial k 1) 0 =
        c * starRingEnd ℂ ((k.prod fun v e => GlobalTheory.FunObj.period δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1)
          (fun z => ζ * Formalism.MainNotions.TaylorLogMetric.U D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) s Θ₀ z)) := by
  have hvac' := GlobalTheory.VacConj.isVacO_conj_negSp ψ θ S T sS sT _ _ F hF
  have hψn : ∀ a, ‖ψ a‖ = 1 := hF.1.1.2.1
  have hθ : IsInfFam θ := hF.2.inf
  have hj2 : ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (GlobalTheory.FockPos.frAt frS)
      (GlobalTheory.FockPos.frAt frT) (fun w => starRingEnd ℂ (F w)) (MvPolynomial.monomial k 1) 0 =
        starRingEnd ℂ c * ((k.prod fun v e => GlobalTheory.FunObj.period δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ₀) := by
    intro k
    have h3 := hj k
    rw [GlobalTheory.FockConj.pureTensorO_negSp_monomial ψ θ S T sS sT _ _ F hF.1 hθ k 0] at h3
    have h4 := congrArg (starRingEnd ℂ) h3
    rw [Complex.conj_conj, map_mul, Complex.conj_conj] at h4
    exact h4
  obtain ⟨ζ, s, hζ, hs, hk⟩ := core ψ θ S T sS sT frS frT hS hT hcS hcT Ls Lt hLs hLt δ hδ Θ₀ hΘ _ _ hvac' hj2 n hn w
    (latO_negSp_le S T _ _ _ hw)
  refine ⟨ζ, s, hζ, hs, fun k => ?_⟩
  rw [GlobalTheory.FockConj.pureTensorO_negSp_monomial ψ θ S T sS sT _ _ _ hF.1 hθ k 0, ← GlobalTheory.VacConj.heisO_conj ψ hψn S T w F,
    hk k, map_mul, Complex.conj_conj]

end GlobalTheory.HeisTrans

namespace GlobalTheory.HeisTrans

theorem qbar_of_root {ζ : ℂ} (h : ∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) :
    ∃ ζ' : Qbar, (ζ' : ℂ) = ζ ∧ ∃ m : ℕ, 0 < m ∧ ζ' ^ m = 1 := by
  obtain ⟨m, hm, hζ⟩ := h
  have hint : IsIntegral ℚ ζ := ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [hζ]⟩
  refine ⟨⟨ζ, mem_algebraicClosure_iff.2 hint.isAlgebraic⟩, rfl, m, hm, ?_⟩
  apply Subtype.ext
  simp [hζ]

end GlobalTheory.HeisTrans

theorem GlobalTheory.HeisTrans.main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p →
    ∀ (Ls : Submodule (𝓞 D.host.E) (Fin (G.pS p).rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin (G.pT p).rank → D.host.E))
    (κ : ℂ) (F : WO (G.pS p) (G.pT p) → ℂ), SD D Ls → SD D Lt →
    Differentiable ℂ (Iop D (tor0 D D.host.ccK S.Z.δ) (La0 D (tor0 D D.host.ccK S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK S.Z.δ) Ls Lt) (S.Z.e0 p)) →
    IsVacO W.ψ W.θ _ _ (G.cartS W.cart p) (G.onT W.cart p) (inV (frS S.N p) Ls) (inV (frT S.N p) Lt) F →
    (∀ k : FVar D (G.pT p).rank (G.pS p).rank →₀ ℕ, fockIn W S.N.frC p F (MvPolynomial.monomial k 1) 0 =
      S.Z.c0 p * opp p ((k.prod fun v e => period S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z =>
        κ * Iop D (tor0 D D.host.ccK S.Z.δ) (La0 D (tor0 D D.host.ccK S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK S.Z.δ) Ls Lt) (S.Z.e0 p) z)) →
    ∀ (n : ℕ), 0 < n → ∀ w : WO (G.pS p) (G.pT p), n • w ∈ latO _ _ (inV (frS S.N p) Ls) (inV (frT S.N p) Lt) (fun _ => True) →
    ∃ (ζ : Qbar) (s : VC D (G.pS p).rank (G.pT p).rank), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ n • s ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK S.Z.δ) Ls Lt ∧
    ∀ k : FVar D (G.pT p).rank (G.pS p).rank →₀ ℕ, fockIn W S.N.frC p (heisO W.ψ _ _ w F) (MvPolynomial.monomial k 1) 0 =
      S.Z.c0 p * opp p ((k.prod fun v e => period S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z =>
        κ * ((ζ : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK S.Z.δ) s
          (Iop D (tor0 D D.host.ccK S.Z.δ) (La0 D (tor0 D D.host.ccK S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK S.Z.δ) Ls Lt) (S.Z.e0 p)) z)) := by
  intro D T L sc G W S p hp Ls Lt κ F hLs hLt hdiff hvac hjets n hn w hw
  have hδ : S.Z.δ ≠ 0 := GlobalTheory.InertSign.delta_ne_zero S.Z.crv
  set Θ₀ := fun z => κ * Iop D (tor0 D D.host.ccK S.Z.δ) (La0 D (tor0 D D.host.ccK S.Z.δ) _ _)
    (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK S.Z.δ) Ls Lt) (S.Z.e0 p) z with hΘ₀
  have hΘ : Differentiable ℂ Θ₀ := hdiff.const_mul κ
  have hU : ∀ (s : VC D (G.pS p).rank (G.pT p).rank) (ζ : ℂ),
      (fun z => ζ * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK S.Z.δ) s Θ₀ z) = fun z =>
        κ * (ζ * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK S.Z.δ) s
          (Iop D (tor0 D D.host.ccK S.Z.δ) (La0 D (tor0 D D.host.ccK S.Z.δ) _ _)
            (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK S.Z.δ) Ls Lt) (S.Z.e0 p)) z) := by
    intro s ζ; funext z; simp only [hΘ₀, Formalism.MainNotions.TaylorLogMetric.U]; ring
  cases p with
  | top t j =>
    have hj : j + 1 ≤ D.R.m := hp
    have hcS := W.cart_is (.top j) (show j ≤ D.R.m by omega)
    have hcT := W.cart_is (.top (j + 1)) hj
    obtain ⟨ζ, s, hζ, hs, hk⟩ := GlobalTheory.HeisTrans.core W.ψ W.θ _ _ _ _ (S.N.fr (.top j)) (S.N.fr (.top (j + 1)))
      (S.N.fr_on _ (show j ≤ D.R.m by omega)) (S.N.fr_on _ hj) hcS hcT Ls Lt hLs hLt S.Z.δ hδ Θ₀ hΘ (S.Z.c0 (.top t j))
      F hvac hjets n hn w hw
    obtain ⟨ζ', hζ', hroot⟩ := GlobalTheory.HeisTrans.qbar_of_root hζ
    refine ⟨ζ', s, hroot, hs, fun k => ?_⟩
    have := hk k
    rw [hU] at this
    rw [hζ']
    exact this
  | chi i j =>
    obtain ⟨hi, rfl⟩ : i + 1 ≤ D.R.m ∧ j = D.R.m := hp
    obtain ⟨ζ, s, hζ, hs, hk⟩ := GlobalTheory.HeisTrans.coreNeg W.ψ W.θ _ _ _ _ (S.N.fr (.grid (i + 1) D.R.m))
      (S.N.fr (.grid i D.R.m)) (S.N.fr_on _ ⟨hi, rfl⟩) (S.N.fr_on _ ⟨by omega, rfl⟩)
      (W.cart_is (.grid (i + 1) D.R.m) ⟨hi, le_rfl⟩) (W.cart_is (.grid i D.R.m) ⟨by omega, le_rfl⟩) Ls Lt hLs hLt
      S.Z.δ hδ Θ₀ hΘ (S.Z.c0 (.chi i D.R.m)) F hvac hjets n hn w hw
    obtain ⟨ζ', hζ', hroot⟩ := GlobalTheory.HeisTrans.qbar_of_root hζ
    refine ⟨ζ', s, hroot, hs, fun k => ?_⟩
    have := hk k
    rw [hU] at this
    rw [hζ']
    exact this
  | mu _ i j => exact absurd hp (by simp [DefPair])
  | core i => exact absurd hp (by simp [DefPair])
