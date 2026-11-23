import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorFockUnitScaledBasisMonomial
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralRealPointUnitScalarSinglePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PowExpIOrInvInjective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteMonomialsWithPrescribedPlaceDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvari
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKORatLeftAndEigenRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.BottomDeg

open GlobalTheory.Grid (neg sgn ofSgn)

variable {D : D7}

open Classical in

theorem pureTensorO_scal_pm {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hs : ∀ τ, sS τ = 1 ∨ sS τ = -1) (ht : ∀ τ, sT τ = 1 ∨ sT τ = -1)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (ζ : D.what₂.Tau → ℂ) (hζ : ∀ τ, ‖ζ τ‖ = 1)
    (α : FVar D T.rank S.rank →₀ ℕ) :
    pureTensorO ψ θ S T sS sT (fun τ => ζ τ • BS τ) BT f (MvPolynomial.monomial α 1) =
      (∏ τ, (if (sS τ = 1 ↔ sT τ = 1) then (ζ τ)⁻¹ else ζ τ) ^ (∑ v ∈ α.support with v.1 = τ, α v)) •
        pureTensorO ψ θ S T sS sT BS BT f (MvPolynomial.monomial α 1) := by
  have hz : ∀ τ, ζ τ ≠ 0 := fun τ h => by simpa [h] using hζ τ
  let μ : D.what₂.Tau → ℂ := fun τ => if (sS τ = 1 ↔ sT τ = 1) then (ζ τ)⁻¹ else ζ τ
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) (fun τ => ζ τ • BS τ) BT i g =
      μ i.1 • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g := by
    rintro ⟨ρ, a, j⟩ g hg
    simp only [aPlusAll, μ]
    rw [GlobalTheory.FockScal.unitMap_smul _ _ (hz ρ),
      GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (GlobalTheory.FockScal.cplxO_pm (hs ρ) (ht ρ) a j _)]
    congr 1
    rw [map_inv₀, ← Complex.inv_eq_conj (hζ ρ), inv_inv]
    simp only [decide_eq_true_eq]
  have hA : ∀ i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i f) :=
    fun _ _ h => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ h
  have Asm : ∀ i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i f :=
    fun _ a _ h => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a h
  unfold pureTensorO
  exact GlobalTheory.FockScal.pure_scal (P := IsThetaFunO ψ S T) (fun v : FVar D T.rank S.rank => v.1) μ
    (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) hA Asm key hf α

open Classical in

theorem scalar_exists {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (τ₀ : D.what₂.Tau) :
    ∃ C w : ℂ, (w = Complex.exp Complex.I ∨ w = (Complex.exp Complex.I)⁻¹) ∧
      ∀ (k : FVar D WW.rank A.rank →₀ ℕ) (h : GA D WW),
        X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h =
          (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) * X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h := by
  classical
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  set om' := (X.ω t).toSgn true with hom'
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have he : ‖Complex.exp Complex.I‖ = 1 := by simpa using Complex.norm_exp_ofReal_mul_I 1
  obtain ⟨z', hz', -, h1, h2⟩ := GlobalTheory.CentralUnit.exists_central_of_norm_one D W.θ hθ (neg A) τ₀ (Complex.exp Complex.I) he
  set ζ : D.what₂.Tau → ℂ := fun τ => if τ = τ₀ then Complex.exp Complex.I else 1 with hζdef
  have hζ : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) z') = ζ τ • (1 : Matrix (Fin (neg A).rank) (Fin (neg A).rank) ℂ) := by
    intro τ
    by_cases hτ : τ = τ₀
    · subst hτ
      simp only [hζdef, if_pos rfl, h1]
    · simp only [hζdef, if_neg hτ, h2 τ hτ, one_smul]
  have hζn : ∀ τ, ‖ζ τ‖ = 1 := fun τ => by
    by_cases hτ : τ = τ₀
    · simp only [hζdef, if_pos hτ, he]
    · simp only [hζdef, if_neg hτ, norm_one]
  have hf : IsThetaFunO W.ψ (neg A) WW (X.f t) := (GlobalTheory.ConstRatio.theta_f hI t).1
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hfock : ∀ τ, IsFockVacAt (heisO W.ψ (neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (hI.fst t)
      hI.isVac.2.theta hf (hI.isVac.2.fock τ)
  have cS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hdet : ∀ τ, (gramAt D (neg A) τ).det ≠ 0 := fun τ h0 => by
    have := (cS τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  obtain ⟨r, hr, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (neg A) hdet z' hz'
  have hy1 : IsDetRoot WW 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have one : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one WW _
  obtain ⟨C, hC⟩ : ∃ C : ℂ, om' (z', 1) (X.f t) = C • X.f t :=
    ⟨_, GlobalTheory.WeilVacChar.vacuum_character D W.ψ hψ (neg A) WW W.θ hθ _ _ om' η hη hom (fun τ => -X.rA.s τ) X.rW.s cS cT
      z' hz' 1 (one_mem _) (fun τ => by rw [hζ τ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [one, one_mul, mul_one]) r 1 hr hy1 (X.f t) hf hfock⟩

  have hop : ∀ k : FVar D WW.rank A.rank →₀ ℕ, _ := fun k =>
    GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ om' hom hθ (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ)
      X.rA.B (fun τ => ζ τ • X.rA.B τ) X.rW.s X.rW.s X.rW.B X.rW.B z' 1
      (fun τ => by rw [hζ τ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [one, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [hζ τ, Matrix.smul_mul, Matrix.one_mul])
      (fun τ => by rw [one, Matrix.one_mul]) (X.f t) hf (MvPolynomial.monomial k 1)
  set w : ℂ := if (-X.rA.s τ₀ = 1 ↔ X.rW.s τ₀ = 1) then (Complex.exp Complex.I)⁻¹ else Complex.exp Complex.I with hw
  have hscal : ∀ k : FVar D WW.rank A.rank →₀ ℕ,
      om' (z', 1) (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t)
        (MvPolynomial.monomial k 1)) =
        (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) •
          pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (MvPolynomial.monomial k 1) := by
    intro k
    rw [(hop k).2, hC, GlobalTheory.FiniteFock.pureTensorO_smul,
      pureTensorO_scal_pm (S := neg A) (T := WW) hψ hθ (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (fun τ => Or.inr (by rw [hsA])) (fun τ => Or.inl (hsW τ)) (X.f t) hf ζ hζn k,
      smul_smul]
    congr 2
    rw [Finset.prod_eq_single τ₀]
    · simp only [hζdef, if_pos rfl, hw]
    · intro ρ _ hρ
      simp only [hζdef, if_neg hρ, inv_one, ite_self, one_pow]
    · simp
  refine ⟨C, w, by rw [hw]; split_ifs; exacts [Or.inr rfl, Or.inl rfl], fun k h => ?_⟩
  set φ := pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (MvPolynomial.monomial k 1)
    with hφ
  have hK := GlobalTheory.thetaKO_rat_left_and_eigen_right W.ψ (neg A) WW _ _ om' hom φ (hop k).1
  have hker : ∀ g : GA D A, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g = thetaKO om' ((ofSgn true A).symm g) h φ :=
    fun g => by
      show thetaKO (X.ω t) g h φ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm g), h) φ 0
      rw [MulEquiv.apply_symm_apply]
      rfl
  have hleft : ∀ γ ∈ GQ A, ∀ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (γ * g) =
      X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g := by
    intro γ hγ g
    rw [hker, hker, map_mul]
    have := hK.1 _ ((GlobalTheory.SgnIdent.mem_GQ_sgn true A _).2 (by rwa [MulEquiv.apply_symm_apply])) 1 (one_mem _)
      ((ofSgn true A).symm g) h
    rwa [one_mul] at this
  have hright : ∀ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (g * ofSgn true A z') =
      (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) * X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g := by
    intro g
    rw [hker, hker, map_mul, MulEquiv.symm_apply_apply]
    have := hK.2 z' 1 _ (hscal k) ((ofSgn true A).symm g) h
    rwa [mul_one] at this
  show ∫ g in X.fd, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g ∂X.m =
    _ * ∫ g in X.fd, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g ∂X.m
  calc _ = ∫ g in X.fd, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (g * ofSgn true A z') ∂X.m :=
        (GlobalTheory.ChainOnto.setIntegral_fd_mul_right D A X.m X.fd hI.meas.1 hI.meas.2 _ hleft (ofSgn true A z')).symm
    _ = _ := by
        simp_rw [hright]
        exact integral_const_mul _ _

theorem classSum_vanish_off_finite : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ K : Finset (FVar D WW.rank A.rank →₀ ℕ), ∀ t, ∀ h ∈ GfC WW, ∀ k ∉ K,
      X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h = 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX
  classical
  let Good : T → Set (FVar D WW.rank A.rank →₀ ℕ) := fun t =>
    {k | ∃ h ∈ GfC WW, X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h ≠ 0}
  have one_of : ∀ {c I : ℂ}, I = c * I → I ≠ 0 → c = 1 := fun {c I} e hI => by
    have h0 : (c - 1) * I = 0 := by rw [sub_mul, one_mul, ← e, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hI)
  have hfin : ∀ t, (Good t).Finite := by
    intro t
    by_cases hne : (Good t).Nonempty
    · obtain ⟨k₀, h₀, -, hk₀⟩ := hne
      refine (GlobalTheory.finite_monomials_of_placeDegree D WW.rank A.rank
        (fun τ => ∑ v ∈ k₀.support with v.1 = τ, k₀ v)).subset fun k hk τ => ?_
      obtain ⟨h, -, hk⟩ := hk
      obtain ⟨C, w, hw, hI⟩ := scalar_exists hX t τ
      have e1 := one_of (hI k h) hk
      have e0 := one_of (hI k₀ h₀) hk₀
      have hC : C ≠ 0 := fun h0 => by rw [h0, zero_mul] at e1; exact zero_ne_one e1
      exact GlobalTheory.ExpPow.pow_exp_I_or_inv_injective _ _ w hw (mul_left_cancel₀ hC (e1.trans e0.symm))
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]
      exact Set.finite_empty
  have hU : (⋃ t, Good t).Finite := Set.finite_iUnion hfin
  refine ⟨hU.toFinset, fun t h hh k hk => ?_⟩
  by_contra hne
  exact hk (hU.mem_toFinset.2 (Set.mem_iUnion.2 ⟨t, h, hh, hne⟩))

end GlobalTheory.BottomDeg

end
