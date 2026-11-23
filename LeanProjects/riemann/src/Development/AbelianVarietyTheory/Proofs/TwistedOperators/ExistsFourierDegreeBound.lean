import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqZeroOfScalar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapDomainFstEqOfCoeffMatrixFamilyBilateralSubstiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffMatrixFamilyBilateralSubstitutionMonomialCoStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionCompEqMulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixFamilyBilateralSubstitutionScalarMonomialStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitaryRealPointsOfGramEqOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseUnitaryRealPointsAlgebraicEntriesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomWeilActionFockPureTensorSubstitutiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanCharacterThetaStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteMonomialsWithPrescribedPlaceDegree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralRealPointUnitScalarSinglePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowExpIOrInvInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealAvg

open MvPolynomial

variable {D : D7}

theorem substMat_mul (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) (g₁ g₂ : GA D V) :
    substMat θ V m d (g₁ * g₂) = substMat θ V m d g₁ * substMat θ V m d g₂ := by
  ext k' k
  simp only [substMat, Matrix.mul_apply]
  have e : (fun τ => compAt θ τ (Formalism.L2.Theta.mt V (g₁ * g₂))) =
      (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₁)) * (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₂)) :=
    funext fun τ => GlobalTheory.StdUnn.CartanMove.compAt_mt_mul θ τ V g₁ g₂
  have e1 : (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ)) = (fun _ => 1) * (fun _ => 1) := by
    funext τ; simp
  have e2 : GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
      (fun τ => compAt θ τ (Formalism.L2.Theta.mt V (g₁ * g₂))) (monomial k.1 1) =
      GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
        (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₁))
        (GlobalTheory.CompactHowe.substF (fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ))
          (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g₂)) (monomial k.1 1)) := by
    rw [GlobalTheory.T.matrixFamilyBilateralSubstitution_comp_eq_mul, ← e, ← e1]
  rw [e2]
  conv_lhs => rw [eq_sum_mon (d := d) (GlobalTheory.CompactHowe.substF _ _ (monomial k.1 1))
    (fun k'' h => (GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero _ _ _ _ h).trans k.2)]
  rw [map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun k'' _ => ?_
  rw [map_smul, coeff_smul, smul_eq_mul, mul_comm]

theorem substMat_cont {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ)
    (k' k : Mon D m V.rank d) :
    Continuous (fun g : GinfC V => substMat θ V m d g.1 k' k) := by
  have hc := (GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic (ι := D.what₂.Tau) (N := m) (n := V.rank) k.1 k'.1).1
  have hm : Continuous fun g : GinfC V => (fun τ : D.what₂.Tau => compAt θ τ (Formalism.L2.Theta.mt V g.1)) :=
    continuous_pi fun τ =>
      (GlobalTheory.RealWeil.continuous_compAt hθ τ _ _).comp ((GlobalTheory.RealWeil.continuous_mt V).1.comp continuous_subtype_val)
  have hp : Continuous fun g : GinfC V => ((fun _ : D.what₂.Tau => (1 : Matrix (Fin m) (Fin m) ℂ)),
      (fun τ : D.what₂.Tau => compAt θ τ (Formalism.L2.Theta.mt V g.1))) := continuous_const.prodMk hm
  have := hc.comp hp
  exact this

theorem substMat_alg (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ)
    (k' k : Mon D m V.rank d) (g : GA D V) (hg : ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g) a b)) :
    IsAlgebraic ℚ (substMat θ V m d g k' k) := by
  have ha := (GlobalTheory.T.coeff_matrixFamilyBilateralSubstitution_monomial_continuous_algebraic (ι := D.what₂.Tau) (N := m) (n := V.rank) k.1 k'.1).2
    (fun _ => (1 : Matrix (Fin m) (Fin m) ℂ)) (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g)) (one_alg m) hg
  exact ha

theorem substMat_central (θ : InfFam D) (V : HSp D) (m : ℕ) (d : D.what₂.Tau →₀ ℕ) (z : GA D V) (τ₀ : D.what₂.Tau) (ζ : ℂ)
    (h1 : compAt θ τ₀ (Formalism.L2.Theta.mt V z) = ζ • (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))
    (h2 : ∀ ρ, ρ ≠ τ₀ → compAt θ ρ (Formalism.L2.Theta.mt V z) = 1) :
    substMat θ V m d z = (ζ ^ d τ₀) • (1 : Matrix (Mon D m V.rank d) (Mon D m V.rank d) ℂ) := by
  classical
  have e : (fun ρ => compAt θ ρ (Formalism.L2.Theta.mt V z)) =
      fun ρ => if ρ = τ₀ then ζ • (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1 := by
    funext ρ
    by_cases hρ : ρ = τ₀
    · subst hρ; rw [if_pos rfl, h1]
    · rw [if_neg hρ, h2 ρ hρ]
  ext k' k
  simp only [substMat, e, GlobalTheory.T.matrixFamilyBilateralSubstitution_scalar_monomial, coeff_smul, coeff_monomial, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  rw [show Finsupp.mapDomain Prod.fst k.1 = d from k.2]
  by_cases h : k' = k
  · subst h; simp
  · have h' : (k.1 : FVar D m V.rank →₀ ℕ) ≠ k'.1 := fun e => h (Subtype.ext e.symm)
    simp [h, h']

end GlobalTheory.RealAvg

namespace GlobalTheory.RealAvg

open MvPolynomial
open GlobalTheory.Grid (neg sgn ofSgn)

theorem avg_kernel_alg : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ dg : D.what₂.Tau →₀ ℕ, ∀ (κ : Measure (GinfC A)), κ.IsMulLeftInvariant → IsProbabilityMeasure κ →
      ∀ (t : T), ∀ x ∈ GfC A, ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A.rank →₀ ℕ,
        ∃ (m : ℕ) (r : Fin m → ℂ) (kk : Fin m → (FVar D WW.rank A.rank →₀ ℕ)), (∀ p, IsAlgebraic ℚ (r p)) ∧
          (∀ p, Finsupp.mapDomain Prod.fst (kk p) = dg) ∧
          ∫ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A)) ∂κ =
            ∑ p, r p * X.ker W.ψ W.θ t (MvPolynomial.monomial (kk p) 1) h x := by
  intro D T _ L μ₀ sc G W i j A A' WW X hPr hN hL hX
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hgA : A.gram = 1 := hX.std.1
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig A.gram
  haveI : BorelSpace (GA D A) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig A.gram
  haveI : CompactSpace (GinfC A) := isCompact_iff_compactSpace.1 (GlobalTheory.T.isCompact_unitaryRealPoints_of_gram_eq_one D A hgA)
  haveI : BorelSpace (GinfC A) := Subtype.borelSpace _
  obtain ⟨χ, hχc, hχ, hχa⟩ := GlobalTheory.T.exists_archimedean_character_theta hPr hN hL hX
  have hΓ := GlobalTheory.T.dense_unitaryRealPoints_algebraicEntries D W.θ hθ A

  let ρ : ∀ d : D.what₂.Tau →₀ ℕ, GinfC A →* Matrix (Mon D WW.rank A.rank d) (Mon D WW.rank A.rank d) ℂ := fun d =>
    { toFun := fun g => χ g • substMat W.θ A WW.rank d g.1
      map_one' := by simp only [map_one, OneMemClass.coe_one, substMat_one, one_smul]
      map_mul' := fun a b => by
        simp only [map_mul, Subgroup.coe_mul, substMat_mul]
        rw [smul_mul_smul_comm] }
  have hρ : ∀ d g, ρ d g = χ g • substMat W.θ A WW.rank d g.1 := fun _ _ => rfl
  have hρc : ∀ d, Continuous (ρ d) := fun d => by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [hρ, Matrix.smul_apply, smul_eq_mul]
    exact hχc.mul (substMat_cont hθ A WW.rank d a b)
  have hρa : ∀ d, ∀ γ ∈ {g : GinfC A | ∀ τ a b, IsAlgebraic ℚ (compAt W.θ τ (Formalism.L2.Theta.mt A g.1) a b)}, ∀ a b,
      IsAlgebraic ℚ (ρ d γ a b) := fun d γ hγ a b => by
    simp only [hρ, Matrix.smul_apply, smul_eq_mul]
    exact (hχa γ hγ).mul (substMat_alg W.θ A WW.rank d a b γ.1 hγ)

  have hker : ∀ t P h (g : GA D A), X.ker W.ψ W.θ t P h g = thetaKO ((X.ω t).toSgn true) ((ofSgn true A).symm g) h
      (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := fun t P h g => by
    show thetaKO (X.ω t) g h _ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm g), h) _ 0
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hform : ∀ d t (x : GA D A) h (g : GinfC A) (k : Mon D WW.rank A.rank d),
      X.ker W.ψ W.θ t (monomial k.1 1) h (x * g.1) =
        ∑ k'' : Mon D WW.rank A.rank d, ρ d g k'' k * X.ker W.ψ W.θ t (monomial k''.1 1) h x := by
    intro d t x h g k
    rw [hker, map_mul]
    unfold thetaKO
    have e : ((ofSgn true A).symm x * (ofSgn true A).symm g.1, h) =
        ((ofSgn true A).symm x, h) * ((ofSgn true A).symm g.1, (1 : GA D WW)) := by
      rw [Prod.mk_mul_mk, mul_one]
    rw [e, map_mul, Module.End.mul_apply, GlobalTheory.T.definiteBottom_weilAction_fockPureTensor_substitution hX t g.1, hχ t g, GlobalTheory.FiniteFock.pureTensorO_smul]
    conv_lhs => rw [eq_sum_mon (d := d) (GlobalTheory.CompactHowe.substF _ _ (monomial k.1 1))
      (fun k'' hk => (GlobalTheory.T.mapDomain_fst_eq_of_coeff_matrixFamilyBilateralSubstitution_ne_zero _ _ _ _ hk).trans k.2)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hρ, Matrix.smul_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k'' _ => ?_
    rw [hker]
    unfold thetaKO substMat
    ring

  have he : ‖Complex.exp Complex.I‖ = 1 := by simpa using Complex.norm_exp_ofReal_mul_I 1
  choose z hz _hzc h1 h2 using fun τ => GlobalTheory.CentralUnit.exists_central_of_norm_one D W.θ hθ A τ (Complex.exp Complex.I) he
  let c : D.what₂.Tau → ℂ := fun τ => χ ⟨z τ, hz τ⟩
  have hcen : ∀ d τ, ρ d ⟨z τ, hz τ⟩ = (c τ * Complex.exp Complex.I ^ d τ) • 1 := fun d τ => by
    rw [hρ, substMat_central W.θ A WW.rank d (z τ) τ _ (h1 τ) (h2 τ), smul_smul]
  obtain ⟨dg, hdg⟩ : ∃ dg : D.what₂.Tau →₀ ℕ, ∀ d, d ≠ dg → ∃ τ, c τ * Complex.exp Complex.I ^ d τ ≠ 1 := by
    by_cases hex : ∃ d : D.what₂.Tau →₀ ℕ, ∀ τ, c τ * Complex.exp Complex.I ^ d τ = 1
    · obtain ⟨d₀, hd₀⟩ := hex
      refine ⟨d₀, fun d hd => ?_⟩
      by_contra hall
      push_neg at hall
      refine hd (Finsupp.ext fun τ => ?_)
      have hc0 : c τ ≠ 0 := fun h0 => by have := hd₀ τ; rw [h0, zero_mul] at this; exact zero_ne_one this
      exact GlobalTheory.ExpPow.pow_exp_I_or_inv_injective _ _ _ (Or.inl rfl)
        (mul_left_cancel₀ hc0 ((hall τ).trans (hd₀ τ).symm))
    · push_neg at hex
      exact ⟨0, fun d _ => hex d⟩
  refine ⟨dg, fun κ hκ hκp t x _ h _ k => ?_⟩
  haveI := hκp
  set d := Finsupp.mapDomain Prod.fst k with hd
  let kM : Mon D WW.rank A.rank d := ⟨k, hd.symm⟩
  have hexp := integral_expand κ (fun g => ρ d g) (hρc d) (fun k'' => X.ker W.ψ W.θ t (monomial k''.1 1) h x)
    (fun g : GinfC A => X.ker W.ψ W.θ t (monomial k 1) h (x * g.1)) kM (fun g => hform d t x h g kM)
  by_cases hdd : d = dg
  · let e := Fintype.equivFin (Mon D WW.rank A.rank d)
    refine ⟨Fintype.card (Mon D WW.rank A.rank d), fun p => ∫ g, ρ d g (e.symm p) kM ∂κ, fun p => (e.symm p).1,
      fun p => GlobalTheory.HaarAlg.isAlgebraic_integral κ (ρ d) (hρc d) _ hΓ (hρa d) _ _,
      fun p => (show Finsupp.mapDomain Prod.fst (e.symm p).1 = d from (e.symm p).2).trans hdd, ?_⟩
    rw [hexp, ← Equiv.sum_comp e.symm]
  · obtain ⟨τ, hτ⟩ := hdg d hdd
    refine ⟨0, Fin.elim0, Fin.elim0, fun p => p.elim0, fun p => p.elim0, ?_⟩
    rw [hexp, Fin.sum_univ_zero]
    refine Finset.sum_eq_zero fun k'' _ => ?_
    rw [integral_eq_zero_of_scalar κ (ρ d) (hρc d) ⟨z τ, hz τ⟩ _ hτ (hcen d τ), zero_mul]

end GlobalTheory.RealAvg
