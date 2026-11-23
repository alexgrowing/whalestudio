import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFourierDegreeBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsRealCharacterOfBottom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFourierDegreeBoundStatement

section
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
end GlobalTheory.RealAvg
namespace GlobalTheory.RealAvg
open MvPolynomial
open GlobalTheory.Grid (neg sgn ofSgn)
theorem real_average_kernel_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
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
  obtain ⟨χ, hχc, hχ, hχa⟩ := _root_.GlobalTheory.T.exists_real_character_twist hPr hN hL hX
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
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_real_average_kernel_isAlgebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ dg : D.what₂.Tau →₀ ℕ, ∀ (κ : Measure (GinfC A)), κ.IsMulLeftInvariant → IsProbabilityMeasure κ →
      ∀ (t : T), ∀ x ∈ GfC A, ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A.rank →₀ ℕ,
        ∃ (m : ℕ) (r : Fin m → ℂ) (kk : Fin m → (FVar D WW.rank A.rank →₀ ℕ)), (∀ p, IsAlgebraic ℚ (r p)) ∧
          (∀ p, Finsupp.mapDomain Prod.fst (kk p) = dg) ∧
          ∫ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A)) ∂κ =
            ∑ p, r p * X.ker W.ψ W.θ t (MvPolynomial.monomial (kk p) 1) h x := by
  first | exact @_root_.GlobalTheory.RealAvg.real_average_kernel_isAlgebraic | exact _root_.GlobalTheory.RealAvg.real_average_kernel_isAlgebraic | (intros; apply _root_.GlobalTheory.RealAvg.real_average_kernel_isAlgebraic <;> assumption)
end
