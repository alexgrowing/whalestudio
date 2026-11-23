import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigThetaKernelIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigRouteKernelIntegrableOnUnitaryQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStandingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolIntegrableOnIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRelOfLocalMatching
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSBOfIsNatDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Zact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularisedComparison
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelLeftInvariantRationalUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameCompatibility
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeMemFockAlgebraicThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicVectorThetaTransformHeisenbergDer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAddEquivSymplecticCoordsOrientedModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformGaussianVacuumIsFiniteDatumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeRealPlacePureDatumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergDerivativeArchimedeanDirectionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanPreimageRealPlaceLineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaTripleProportionalToNonzero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDatumLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPolynomialVectorReachedByRealDatum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorProductMulPolynomials
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SquareIdent

section Core

open GlobalTheory.SquareComm GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.TripleRead GlobalTheory.TripleAssembly GlobalTheory.RouteSeesaw
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (incM)

variable {D : D7}

theorem eq_thO {S X : HSp D} {d : ℕ} {Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank}
    {Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws) (ψ : AddChar (AF D.host.F) ℂ)
    (e : Fin d ≃ Fin X.rank) {Gm : Matrix (Fin S.rank) (Fin S.rank) D.host.E} (hG : Gm.det ≠ 0)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e.symm id) (incM Gm) : Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    {Φ} {F : WO S X → ℂ} (h : IsDatum M ψ cS Φ F) : F = thO M ψ Gm e Φ := by
  funext x
  obtain ⟨u, rfl⟩ := cS.surjective x
  have e1 : incM Gm * incM Gm⁻¹ = 1 := by
    show Gm.map (incA D) * (Gm⁻¹).map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hG), Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : ptO Gm e (cS u) = u := by
    rw [hcS, ptO, Matrix.mul_assoc, e1, Matrix.mul_one]
    ext a b
    simp
  rw [thO, e2, h.2]

theorem adjM_coord (S B : HSp D) (y : Matrix (Fin S.rank) (Fin B.rank) (AE D)) :
    adjM S B (HMul.hMul yᵀ (incM S.gram) : Matrix (Fin B.rank) (Fin S.rank) (AE D)) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG B (y.map (cA D)) := by
  have e0 : ((incM S.gram).map (cA D))ᵀ = incM S.gram := by
    ext a b
    exact congrArg (incA D) (GlobalTheory.TripleSpace.star_gram S b a)
  have e1 : (S.gram⁻¹).map (incA D) * incM S.gram = 1 := by
    show (S.gram⁻¹).map (incA D) * S.gram.map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit (GlobalTheory.RouteCoords.gram_det_ne S)),
      Matrix.map_one _ (map_zero _) (map_one _)]
  unfold adjM GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG
  rw [Matrix.map_mul, Matrix.transpose_mul, e0, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  rfl

theorem adjM_neg (S B : HSp D) (y : Mx D B.rank S.rank) : adjM S B (-y) = -adjM S B y :=
  eq_neg_of_add_eq_zero_left (by rw [← adjM_add, neg_add_cancel, adjM_zero])

theorem thetaLift_pure {m k d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) {ψ : AddChar (AF D.host.F) ℂ} (hM : Mo.IsGood ψ) (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ)
    (hY : Y.J.det ≠ 0) (hZ : Z.J.det ≠ 0) {Gm : Matrix (Fin m) (Fin m) D.host.E} (hG : Gm.det ≠ 0) (e : Fin k ≃ Fin d) (τ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin m × Fin k) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin m × Fin k → Fv D.host.F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (Mo.vac v) = s v) {f} (hf : f ∈ Mo.Pol ψ τ) {φ} (h1 : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (h2 : ∀ᶠ v in Filter.cofinite, φ v = Mo.vac v) :
    thetaLift Mo ψ Gm e (darbAlg Mo ψ τ) (liftPure Mo pr pv s) (thO Mo ψ Gm e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) =
      pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s fun v => pv v (φ v) := by
  obtain ⟨T, hT, hinj⟩ := GlobalTheory.T.thetaTransform_darbouxModel_linear_injective D Mo ψ Gm e hM hψ hY hZ hG
  have hS := GlobalTheory.T.darbouxModelAlgebraicVectors_le_adelicSchwartz _ _ _ Mo ψ τ hM
  have H : ∃ q : (Matrix (Fin d) (Fin m) (AE D) → ℂ) →ₗ[ℂ] _, ∀ Ψ ∈ darbAlg Mo ψ τ,
      q (thO Mo ψ Gm e Ψ) = liftPure Mo pr pv s Ψ := by
    obtain ⟨q, hq⟩ := GlobalTheory.TripleAssembly.Onto.exists_factor T _ (fun x hx => hinj x (hS hx)) (liftPure Mo pr pv s)
    exact ⟨q, fun Ψ hΨ => by rw [← hT Ψ (hS hΨ)]; exact hq Ψ hΨ⟩
  have H' := GlobalTheory.T.weil_model_projection_factorisation _ Y Z Mo ψ hM P pr N pv s hs
  rw [thetaLift, dif_pos H, H.choose_spec _ (Submodule.subset_span ⟨f, φ, hf, h1, h2, rfl⟩), liftPure, dif_pos H']
  exact H'.choose_spec f φ h1 h2

theorem blkMat_submatrix {R : Type} [CommRing R] {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (A : Matrix (Fin p) (Fin p) R)
    (B : Matrix (Fin q) (Fin q) R) : (GlobalTheory.Doubling.blkMat finSumFinEquiv A B).submatrix (e.symm.trans finSumFinEquiv)
      (e.symm.trans finSumFinEquiv) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e A B := by
  ext a b
  simp [GlobalTheory.Doubling.blkMat, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk]

theorem rows_coord {U U' : HSp D} {n d : ℕ} (e : Fin U.rank ⊕ Fin U'.rank ≃ Fin d) (u : Matrix (Fin n) (Fin d) (AE D))
    (Gm : Matrix (Fin n) (Fin n) (AE D)) :
    topR (A := U) (B := U') (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) Gm) =
      (HMul.hMul (u.submatrix id fun k => e (.inl k))ᵀ Gm : Matrix (Fin U.rank) (Fin n) (AE D)) ∧
    botR (A := U) (B := U') (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) Gm) =
      (HMul.hMul (u.submatrix id fun k => e (.inr k))ᵀ Gm : Matrix (Fin U'.rank) (Fin n) (AE D)) := by
  constructor <;> ext a b <;> simp [topR, botR, Matrix.mul_apply]

theorem gauss_small {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'} (hb : B.IsGood σ) (hgeo : Γ.IsGood B) {f₀} (hf₀ : f₀ ≠ 0)
    (hG₀ : Γ.M'.IsGauss B.ψ B.emb f₀) (g) (hg : Γ.M'.IsGauss B.ψ B.emb g) : ∃ c : ℂ, g = c • f₀ := by
  choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hgeo.hV'.sig w) (hgeo.hV'.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists _ _ _ _ _ (hgeo.hW.sig w) (hgeo.hW.cartan w)
  have fr : GlobalTheory.RealLift.Framed B.emb (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.W.J) 1 Complex.I A C :=
    ⟨one_mul _, fun w => by rw [GlobalTheory.GaussLine.incM_map_piInf', one_smul]; exact hA w,
      fun w => by rw [GlobalTheory.GaussLine.incM_map_piInf']; exact hC w⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ Γ.M'.co 1 Complex.I A C hb.cm hb.std fr
  have toD : ∀ u (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))),
      GlobalTheory.RealLift.SD (fun t => Γ.M'.co.rho B.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t • u)) f f₁ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (Γ.M'.heisLine B.ψ u) f f₁ :=
    fun u f f₁ h => (GlobalTheory.T.archActionReadings_compatible F (Fin a' × Fin (a + a')) f f₁ f₁).1 _
      (fun t => by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]) h
  have line : ∀ f, Γ.M'.IsGauss B.ψ B.emb f → ∃ z : ℂ, f = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1) := by
    rintro f ⟨ε, hε⟩
    refine GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ Γ.M'.co 1 Complex.I A C Φ hb.cm hb.std fr hΦ f ε
      (fun u u' hu hu' c hc hc' f1 f1' hf hf' => hε u u' hu hu' (fun w => ?_) f1 f1' (toD _ _ _ hf) (toD _ _ _ hf'))
    have h2 := congrArg Matrix.transpose (hCθ w)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, GlobalTheory.GaussLine.Jm_transpose''] at h2
    rw [hc' w, hc w]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h2]
    rw [← Matrix.mul_assoc (Γ.V'.θ w), hAθ w, Matrix.mul_assoc]
  obtain ⟨z, hz⟩ := line f₀ hG₀
  obtain ⟨z', hz'⟩ := line g hg
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hf₀ (by rw [hz, zero_smul])
  exact ⟨z' / z, by rw [hz', hz, smul_smul, div_mul_cancel₀ _ hz0]⟩

set_option maxHeartbeats 1000000 in

theorem match_pure (hH : GlobalTheory.Published.HoweDualityReal) (hP : GlobalTheory.FunPr.Hypotheses₂) (hTL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    {α β : (AE D)ˣ →* Circle} (hT : IsTriple W W₁ X α β) {ωA : WRep W X} {ωB : WRep W₁ X} (hωA : IsWeil ψ true W X β (β / α) ωA)
    (hωB : IsWeil ψ false W₁ X α (α / β) ωB) {e : Fin (W.rank + W₁.rank) ≃ Fin X.rank} {Bs Γ Xc}
    (hR : IsReading ψ A A₁ B α β e Bs Γ Xc) {om₀ om₀'} (hT₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om₀ om₀') :
    ∃ om om' R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf ∧ ∃ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' ∧
      ∀ f₀ f₀', Γ.M.IsGauss Bs.ψ Bs.emb f₀ → f₀' ≠ 0 → Γ.M'.IsGauss Bs.ψ Bs.emb f₀' → ∀ P, ∃ P', ∀ φ φ',
        GlobalTheory.BigNZ.IsFinPart Γ.M Xc.T φ → GlobalTheory.BigNZ.IsFinPart Γ.M' Xc.T φ' → (∀ v, Rf.p v (φ v) = Rf.p' v (φ' v)) →
        ∀ (F : WO W X → ℂ) (F' : WO W₁ X → ℂ),
        IsDatum Γ.M ψ (fun u => (HMul.hMul (uᵀ.submatrix e.symm id) (incM (sgn true W).gram) :
          Matrix (Fin X.rank) (Fin W.rank) (AE D))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F →
        IsDatum Γ.M' ψ (fun u => (HMul.hMul (uᵀ.submatrix e.symm id) (incM W₁.gram) :
          Matrix (Fin X.rank) (Fin W₁.rank) (AE D))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀' φ') F' →
        IsFinF ψ θ true A B F ∧ IsFinF ψ θ false A₁ B F' ∧ p (fockF ψ θ true A B F P) = p' (fockF ψ θ false A₁ B F' P') := by
  obtain rfl := hR.ψ
  have hg := hT₀.geo
  have hstd : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hT₀.base.std
  obtain ⟨om, hom, tA⟩ := GlobalTheory.TripleDarboux.exists_weil Bs hT₀.base true W X e _ _ hg.hV hg.hW 1 hR.JW
    (by rw [neg_gram, one_smul, neg_neg]) hR.JX Γ.M hg.hM hωA
  obtain ⟨om', hom', tB⟩ := GlobalTheory.TripleDarboux.exists_weil Bs hT₀.base false W₁ X e _ _ hg.hV' hg.hW (-1) hR.JW₁
    (neg_one_smul _ _) hR.JX Γ.M' hg.hM' hωB
  have hT' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' :=
    ⟨hT₀.base, hg, hT₀.chars, by rw [hR.α, hR.β]; exact hom, by rw [hR.α, hR.β]; exact hom'⟩
  obtain ⟨R, Rf, hm⟩ := hTL _ _ _ Bs _ _ Γ Xc om om' hT'
  have sA := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D Bs.ψ θ hstd hθ true W X A B β (β / α) ωA hωA
  have sB := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D Bs.ψ θ hstd hθ false W₁ X A₁ B α (α / β) ωB hωB
  obtain ⟨oA, oB⟩ := GlobalTheory.T.algF_map_mapA_and_mapB_eq_top hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨iA, iB⟩ := GlobalTheory.T.mapA_mapB_invariant_under_finite_group hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨lA, lB⟩ := GlobalTheory.T.seesaw_weil_local_factor_eq hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨fA, fB⟩ := GlobalTheory.T.seesaw_weil_archimedean_factor hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  obtain ⟨dA, dB⟩ := GlobalTheory.T.seesaw_weil_unramified_factor hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  have ir := GlobalTheory.T.seesaw_weil_global_factor hH hP D Bs.ψ θ hstd hθ W W₁ X A A₁ B α β hT ωA ωB hωA hωB e Bs Γ Xc om om' hR tA tB R Rf hm
  refine ⟨om, om', R, Rf, hm, ModuleCat.of ℂ (PiT R Γ Rf), _, _, _, _,
    ⟨hωA, hωB, ir, ⟨sA.1, sA.2, oA, iA, lA, fA, dA⟩, ⟨sB.1, sB.2, oB, iB, lB, fB, dB⟩⟩, fun f₀ f₀' g1 n2 g2 P => ?_⟩
  obtain ⟨cA, hcA⟩ := GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords D W X e.symm (-1) (neg_ne_zero.2 one_ne_zero)
  obtain ⟨cB, hcB⟩ := GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.coords D W₁ X e.symm 1 one_ne_zero
  obtain ⟨a1, a2, -⟩ := fock_datum hθ true A B e.symm Bs hT₀.base hR.JW hR.JX hg.hV hg.hW
    (fun w => by
      obtain ⟨τ, a, b, -, d⟩ := hR.cart w
      exact ⟨τ, a, b.trans (one_smul _ _).symm, d⟩) Γ.M hg.hM cA hcA g1
  obtain ⟨b1, -, b3⟩ := fock_datum hθ false A₁ B e.symm Bs hT₀.base hR.JW₁ hR.JX hg.hV' hg.hW
    (fun w => by
      obtain ⟨τ, a, -, c, d⟩ := hR.cart w
      exact ⟨τ, a, c.trans (neg_one_smul _ _).symm, d⟩) Γ.M' hg.hM' cB hcB g2
  obtain ⟨f, hf, hPf⟩ := a2 P
  obtain ⟨f', hf', hff⟩ : R.p f ∈ (Γ.M'.Pol Bs.ψ Bs.emb).map R.p' := hm.real.quot'.onto ▸ Submodule.mem_top
  obtain ⟨P', hP'⟩ := b3 (gauss_small hT₀.base hg n2 g2) f' hf'
  refine ⟨P', fun φ φ' p1 q1 hv F F' kA kB => ?_⟩
  have p2 : ∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v := Xc.T.eventually_cofinite_notMem.mono p1.2
  have q2 : ∀ᶠ v in Filter.cofinite, φ' v = Γ.M'.vac v := Xc.T.eventually_cofinite_notMem.mono q1.2
  have hcA' : ∀ u, cA u = (HMul.hMul (uᵀ.submatrix e.symm id) (incM (sgn true W).gram) :
      Matrix (Fin X.rank) (Fin W.rank) (AE D)) := fun u => by rw [hcA, neg_one_smul]; rfl
  have hcB' : ∀ u, cB u = (HMul.hMul (uᵀ.submatrix e.symm id) (incM W₁.gram) :
      Matrix (Fin X.rank) (Fin W₁.rank) (AE D)) := fun u => by rw [hcB, one_smul]
  replace kA : IsDatum Γ.M Bs.ψ cA (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ φ) F := ⟨kA.1, fun u => by rw [hcA']; exact kA.2 u⟩
  replace kB : IsDatum Γ.M' Bs.ψ cB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀' φ') F' := ⟨kB.1, fun u => by rw [hcB']; exact kB.2 u⟩
  have gX := GlobalTheory.RouteCoords.gram_det_ne X
  have dV : Γ.V.J.det ≠ 0 := by rw [hR.JW, one_smul]; exact GlobalTheory.RouteCoords.gram_det_ne _
  have dV' : Γ.V'.J.det ≠ 0 := by
    rw [hR.JW₁, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (GlobalTheory.RouteCoords.gram_det_ne _)
  have dW : Γ.W.J.det ≠ 0 := by
    rw [hR.JX, det_smul, det_submatrix_equiv_self, det_transpose]
    exact mul_ne_zero (pow_ne_zero _ GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero) gX
  have mA := thetaLift_pure Γ.M hg.hM hT₀.base.std dV dW (GlobalTheory.RouteCoords.gram_det_ne (sgn true W)) e Bs.emb R.p Rf.p
    (vacIm Γ Rf) (Filter.Eventually.of_forall fun _ => rfl) hf p1.1 p2
  have mB := thetaLift_pure Γ.M' hg.hM' hT₀.base.std dV' dW (GlobalTheory.RouteCoords.gram_det_ne W₁) e Bs.emb R.p' Rf.p'
    (vacIm Γ Rf) (Xc.T.eventually_cofinite_notMem.mono fun v hv => (hm.fin.sph v hv).1.symm) hf' q1.1 q2
  have eA := eq_thO Γ.M Bs.ψ e (GlobalTheory.RouteCoords.gram_det_ne (sgn true W)) cA hcA' (hPf φ p1.1 p2 _ kA)
  have eB := eq_thO Γ.M' Bs.ψ e (GlobalTheory.RouteCoords.gram_det_ne W₁) cB hcB' (hP' φ' q1.1 q2 _ kB)
  refine ⟨a1 φ p1.1 p2 _ kA, b1 φ' q1.1 q2 _ kB, ?_⟩
  rw [eA, eB]
  refine mA.trans (Eq.trans ?_ mB.symm)
  rw [hff, funext hv]

end Core

section Read

open GlobalTheory.SquareAgree GlobalTheory.TripleRead GlobalTheory.RouteSeesaw
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (incM IsDatumA IsDatumB Num mulG colV adjV₁)

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {t : T} {i j : ℕ} {e : Num G i j}
  {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}

theorem isDatum_of_isDatumA {τ : TotT G (routeBig t i j)} {Φ} (h : IsDatumA W e Γ τ Φ) :
    IsDatum Γ.M W.ψ (fun u => (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id)
      (incM (GlobalTheory.Grid.sgn true (G.V (.grid (i + 1) (j + 1)))).gram) : Matrix (Fin (_ + _)) (Fin _) (AE D))) Φ
      (GlobalTheory.SquareDict.datumA W τ) := by
  refine ⟨h.1, fun u => (h.2 u).trans (Eq.symm ((Finset.sum_apply _ _ _).trans (Finset.sum_congr rfl fun d _ => ?_)))⟩
  have e3 : incM (GlobalTheory.Grid.sgn true (G.V (.grid (i + 1) (j + 1)))).gram = -incM (G.V (.grid (i + 1) (j + 1))).gram :=
    Matrix.ext fun a b => map_neg (incA D) _
  have e2 : adjM (G.V (.grid (i + 1) (j + 1))) (G.V (.grid (i + 1) j)) (HMul.hMul (u.submatrix id fun k => e (.inr k))ᵀ
      (incM (GlobalTheory.Grid.sgn true (G.V (.grid (i + 1) (j + 1)))).gram) :
        Matrix (Fin (G.V (.grid (i + 1) j)).rank) (Fin (G.V (.grid (i + 1) (j + 1))).rank) (AE D)) = adjV₁ e u := by
    rw [adjV₁, ← adjM_coord, ← adjM_neg, e3]
    exact congrArg _ (Matrix.mul_neg _ _)
  dsimp only
  rw [Pi.smul_apply, box2, (rows_coord e u _).1, (rows_coord e u _).2, e2]
  rfl

theorem isDatum_of_isDatumB {τ : TotT G (routeSmall t i j)} {Φ} (h : IsDatumB W e Γ τ Φ) :
    IsDatum Γ.M' W.ψ (fun u => (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id)
      (incM (G.V (.grid i j)).gram) : Matrix (Fin (_ + _)) (Fin _) (AE D))) Φ (GlobalTheory.SquareDict.datumB W τ) := by
  refine ⟨h.1, fun u => (h.2 u).trans (Eq.symm ((Finset.sum_apply _ _ _).trans (Finset.sum_congr rfl fun d _ => ?_)))⟩
  have e2 : adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) (HMul.hMul (u.submatrix id fun k => e (.inr k))ᵀ
      (incM (G.V (.grid i j)).gram) : Matrix (Fin (G.V (.grid (i + 1) j)).rank) (Fin _) (AE D)) = adjV₁ e u := by
    refine (adjM_coord _ (negSp (G.V (.grid (i + 1) j))) _).trans ?_
    rw [adjV₁, mulG, mulG, ← Matrix.mul_neg]
    congr 1
    ext a b
    exact map_neg (incA D) _
  dsimp only
  rw [Pi.smul_apply, box2, (rows_coord e u _).1, (rows_coord e u _).2, e2]
  rfl

end Read

open GlobalTheory.SquareAgree GlobalTheory.TripleRead in

theorem core : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m)
    (A : Fr (G.V (.grid (↑i + 1) (↑j + 1)))) (A₁ : Fr (G.V (.grid ↑i ↑j))) (AV : Fr (G.V (.grid ↑i (↑j + 1)))) (AV₁ : Fr (G.V (.grid (↑i + 1) ↑j))),
    GlobalTheory.SquareDict.IsGridFr W _ A → GlobalTheory.SquareDict.IsGridFr W _ A₁ → GlobalTheory.SquareDict.IsGridFr W _ AV → GlobalTheory.SquareDict.IsGridFr W _ AV₁ →
    ∀ (t : T) (B : Frames G) (ρ : RealMatch W) (M : Vol G), SquareStanding G t → M.Is t →
    GlobalTheory.SquareComm.IsTriple (G.V (.grid (↑i + 1) (↑j + 1))) (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) →
    ∀ (ωA : GlobalTheory.Grid.WRep (G.V (.grid (↑i + 1) (↑j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))) (ωB : GlobalTheory.Grid.WRep (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) / (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j)) ωA → GlobalTheory.Grid.IsWeil W.ψ false _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) / (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j)) ωB →
    ∃ Pi rf rl p p', GlobalTheory.SquareComm.IsMatch W.ψ W.θ A A₁ (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωA ωB Pi rf rl p p' ∧
      ∀ P, ∃ P', ∀ n Φ (τ : TotT G (routeBig t i j)) (τ' : TotT G (routeSmall t i j)),
        (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip B t ρ i j n Φ τ τ' →
        GlobalTheory.SquareComm.IsFinF W.ψ W.θ true A (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumA W τ) ∧
        GlobalTheory.SquareComm.IsFinF W.ψ W.θ false A₁ (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumB W τ') ∧
        p (GlobalTheory.SquareComm.fockF W.ψ W.θ true A (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumA W τ) P) =
          p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false A₁ (GlobalTheory.SquareComm.frSum AV AV₁) (GlobalTheory.SquareDict.datumB W τ') P') := by
  intro hH hP hTL D T L sc G μ₀ hL W i j A A₁ AV AV₁ hA hA₁ hV hV₁ t B ρ M hst hM hT ωA ωB hωA hωB
  obtain ⟨h1, h2⟩ := GlobalTheory.FlipMatch.flip_match hL W B ρ t i j hst M
  obtain ⟨e, Bs, Γ, X, om₀, om₀', h, hT₀, hti⟩ := h1 hM
  have hR : IsReading W.ψ A A₁ (GlobalTheory.SquareComm.frSum AV AV₁) _ _ (e.symm.trans finSumFinEquiv) Bs Γ X :=
    ⟨h.ψ, h.JW, h.JW₁, by
      rw [h.JWW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← blkMat_submatrix, GlobalTheory.Doubling.gram_hsum]
      rfl, fun w => by
      obtain ⟨τ, a, b, c, d⟩ := h.cart w
      refine ⟨τ, a, b.trans (hA τ).2.symm, c.trans (congrArg Neg.neg (hA₁ τ).2.symm), d.trans ?_⟩
      rw [GlobalTheory.SquareAlg.cart_frSum, (hV τ).2, (hV₁ τ).2, ← blkMat_submatrix], h.α, h.β⟩
  obtain ⟨om, om', R, Rf, hm, Pi, rf, rl, p, p', hM', H⟩ := match_pure hH hP hTL W.θ_is A A₁ _ hT hωA hωB hR hT₀
  obtain ⟨f₀, f₀', ⟨-, g1⟩, ⟨n2, g2⟩, hfl⟩ := h2 e Bs Γ X om om' h hti R Rf hm
  refine ⟨Pi, rf, rl, p, p', hM', fun P => ?_⟩
  obtain ⟨P', hP'⟩ := H f₀ f₀' g1 n2 g2 P
  refine ⟨P', fun n Φ τ τ' hn hF => ?_⟩
  obtain ⟨φ, φ', p1, q1, dA, dB, hv, -⟩ := hfl n Φ τ τ' hn hF
  exact hP' φ φ' p1 q1 hv _ _ (isDatum_of_isDatumA dA) (isDatum_of_isDatumB dB)

theorem thetaKO_left_neg {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {M X : HSp D} (A : Fr M) (B : Fr X)
    {χ χ' : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep M X} (hω : GlobalTheory.Grid.IsWeil ψ true M X χ χ' ω) {Φ : WO M X → ℂ}
    (hΦ : Φ ∈ GlobalTheory.SquareComm.algF ψ θ true A B) : ∀ γ ∈ GQ M, ∀ (g : GA D M) (h : GA D X),
    thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ := by
  intro γ hγ g h
  have hω' : IsWeilDatumO ψ (GlobalTheory.Grid.sgn true M) X χ χ' (ω.toSgn true) := hω
  have hth : IsThetaFunO ψ (GlobalTheory.Grid.sgn true M) X Φ := by
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact GlobalTheory.GalLift.Vec.theta_pureTensorO hω'.std hθ _ _ _ _ hf.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx
  unfold thetaKO
  have e : (γ * g, h) = (γ, (1 : GA D X)) * (g, h) := by simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hω'.om_aut ((GlobalTheory.Grid.ofSgn true M).symm γ) ((GlobalTheory.SgnIdent.mem_GQ_sgn true M _).2 hγ) _ (Subgroup.one_mem _) _
    (hω'.om_pres ((GlobalTheory.Grid.ofSgn true M).symm g, h) _ hth)

theorem exists_scalar {P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q] {x : P} (hx : x ≠ 0) (y : P) :
    ∃ c : ℂ, ∀ u u' : Q, x ⊗ₜ[ℂ] u = y ⊗ₜ[ℂ] u' → u = c • u' := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  refine ⟨l y, fun u u' h => ?_⟩
  have := congrArg (TensorProduct.lid ℂ Q ∘ LinearMap.rTensor Q l) h
  simpa [hl] using this

theorem square_ident : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ i j : Fin D.R.m, ∃ r : Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
    PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)), (∀ a, ∃ b, (a, b) ∈ r) ∧ (∀ b, ∃ a, (a, b) ∈ r) ∧ r ≠ ⊤ ∧
  ∀ ρ' : RealMatch W, ρ'.vX = ρ.vX → ρ'.vT = ρ.vT → ρ'.rel i j = r → ∀ t : T, ∃ c : ℂ, ∀ M : Vol G, M.Is t → ∀ Θ Θ',
    IsMatched B t ρ' i j Θ Θ' → ∀ g g₁, ∃ z, zdeg z ≠ 0 ∧ SquareConv W M Θ Θ' z g g₁ ∧
      zdeg z * ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _ := by
  intro hH hP hK hTL hWC hLM hTA
  refine ⟨0, fun ε CF _ => ⟨(12 : ℝ) ^ (5 / ε), fun D large₂ he hx Γ _ _ Pl0 T A0 Ks _ _ _ R F hS => ?_⟩⟩
  intro G W _ B ρ _ i j
  have hL := hS.core.lev
  have hst : ∀ t, SquareStanding G t := fun t => GlobalTheory.SquareConv.standing hS (GlobalTheory.SquareConv.splitBound_ge he hx) G t
  obtain ⟨A, hA⟩ := GlobalTheory.SquareDict.exists_isGridFr W (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩
  obtain ⟨A₁, hA₁⟩ := GlobalTheory.SquareDict.exists_isGridFr W (X := .grid i j) ⟨i.2.le, j.2.le⟩
  obtain ⟨AV, hV⟩ := GlobalTheory.SquareDict.exists_isGridFr W (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩
  obtain ⟨AV₁, hV₁⟩ := GlobalTheory.SquareDict.exists_isGridFr W (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩
  have hD := fun t => GlobalTheory.SquareDict.dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁
  by_cases hex : ∃ t, ∃ M : Vol G, M.Is t
  swap
  · obtain ⟨r, h1, h2, h3⟩ := exists_rel (G := G) (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid i j) (.grid (i + 1) j)
    exact ⟨r, h1, h2, h3, fun _ _ _ _ t => ⟨0, fun M hM => absurd ⟨t, M, hM⟩ hex⟩⟩
  obtain ⟨t₀, M₀, hM₀⟩ := hex
  have hT₀ := (hD t₀).1 (hst t₀) M₀ hM₀
  choose a b ha hb _ using hT₀.gap
  obtain ⟨ι, hι, hιA⟩ := realA hL W i j A AV AV₁ hA hV hV₁
  obtain ⟨ι', hι', hιB⟩ := realB hL W i j A₁ AV AV₁ hA₁ hV hV₁
  obtain ⟨Pr, q, q', hq, hq', H⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is _ _ _ A A₁ (GlobalTheory.SquareComm.frSum AV AV₁) a b
  have hexp : ∀ t τ, HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) τ (a τ) ∧ HasInfExp D (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) τ (b τ) :=
    fun t τ => ⟨GlobalTheory.SquareRel.hasInfExp_alpha G i j hL t₀ t τ (ha τ), hb τ⟩
  have hqi : Function.Surjective (q ∘ₗ ι) := hq.comp hι
  have hqi' : Function.Surjective (q' ∘ₗ ι') := hq'.comp hι'
  haveI hPr : Nontrivial Pr := by
    obtain ⟨⟨ωA, ωB, Pi, rf, rl, p, p', hm⟩, H2⟩ := H _ _ hT₀ (hexp t₀)
    obtain ⟨Pf, -, -, e, -⟩ := H2 ωA ωB Pi rf rl p p' hm
    haveI : Nontrivial Pi := hm.irred.1
    exact GlobalTheory.SquareRel.nontrivial_of_tensor e
  refine ⟨GlobalTheory.SquareRel.relOf (q ∘ₗ ι) (q' ∘ₗ ι'), GlobalTheory.SquareRel.relOf_fst hqi', GlobalTheory.SquareRel.relOf_snd hqi,
    GlobalTheory.SquareRel.relOf_ne_top hqi, fun ρ' _ _ hrel t => ?_⟩
  by_cases hex : ∃ M : Vol G, M.Is t
  swap
  · exact ⟨0, fun M hM => absurd ⟨M, hM⟩ hex⟩
  obtain ⟨M₁, hM₁⟩ := hex
  have hT := (hD t).1 (hst t) M₁ hM₁
  obtain ⟨⟨ωA, ωB, _, _, _, _, _, hm₀⟩, H2⟩ := H _ _ hT (hexp t)
  obtain ⟨Pi, rf, rl, p, p', hm, hcore⟩ := core hH hP hTL hL W i j A A₁ AV AV₁ hA hA₁ hV hV₁ t B ρ' M₁ (hst t) hM₁ hT ωA ωB
    hm₀.weilA hm₀.weilB
  obtain ⟨Pf, r, r', e, -, -, hp, hp'⟩ := H2 ωA ωB Pi rf rl p p' hm
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : Pr)
  obtain ⟨P₀, rfl⟩ := hq x₀
  obtain ⟨P₀', hP₀⟩ := hcore P₀
  obtain ⟨lam, hlam⟩ := exists_scalar (Q := Pf) hx₀ (q' P₀')
  have hbig : Node.InRange D.R.m (.grid (i + 1) (j + 1)) := ⟨i.2, j.2⟩
  have hsm : Node.InRange D.R.m (.grid i j) := ⟨i.2.le, j.2.le⟩
  obtain ⟨c₀, -, hc₀⟩ := GlobalTheory.RegCompare.regularised_comparison hP hK hTA D W.ψ W.θ W.θ_is _ _ _ A A₁
    (GlobalTheory.SquareComm.frSum AV AV₁) _ _ hT _ _ _ _ (hM₁.vtx _ hbig).haar_fund (hM₁.vtx _ hsm).haar_fund ωA ωB Pi rf rl p p' hm
  obtain ⟨κ, hκ⟩ := (hD t).2 ωA ωB hm.weilA hm.weilB
  refine ⟨lam * c₀, fun M hM Θ Θ' hΘ g g₁ => ?_⟩
  obtain ⟨aA, aB, kA, kB, iA, iB⟩ := hκ B ρ' Θ Θ' hΘ
  have hconv := GlobalTheory.T.bigRoute_kernel_integrableOn_unitary_quotient hWC hL W B ρ' t i j (GlobalTheory.T.squareThetaTripleHypotheses_of_standing hL W t i j (hst t)) M hM Θ Θ' hΘ g₁ g
  have hpp : p (GlobalTheory.SquareDict.datumA W Θ) = lam • p' (GlobalTheory.SquareDict.datumB W Θ') := by
    obtain ⟨a', b', τ, τ', n, Φ, hab, hn, hF, rfl, rfl⟩ := hΘ
    obtain ⟨f1, f2, f3⟩ := hP₀ n Φ τ τ' hn hF
    rw [hp _ f1, hp' _ f2] at f3
    have h1 := hlam _ _ (e.injective f3)
    have h2 : q (ι (toTens a')) = q' (ι' (toTens b')) := by
      have : (toTens a', toTens b') ∈ ρ'.rel i j := hab
      rw [hrel] at this
      exact this
    rw [hιA t B ρ' n Φ τ τ' hF, hιB t B ρ' n Φ τ τ' hF, hp _ f1, hp' _ f2, h1, h2, TensorProduct.tmul_smul, map_smul]
  obtain ⟨z, -, hz0, hzS, hzM, hz⟩ := hc₀ _ aB
  have ez : GlobalTheory.SquareDict.zact ωB z (GlobalTheory.SquareDict.datumB W Θ') = GlobalTheory.RegCompare.wop ωB z (GlobalTheory.SquareDict.datumB W Θ') :=
    (GlobalTheory.RegCompare.wop_apply _ _ _).symm
  have hI : zdeg z • GlobalTheory.SquareComm.thetaInt ωA (M₁.ν _) (M₁.fd _) (GlobalTheory.SquareDict.datumA W Θ) =
      (lam * c₀) • GlobalTheory.SquareComm.thetaInt ωB (M₁.ν _) (M₁.fd _) (GlobalTheory.RegCompare.wop ωB z (GlobalTheory.SquareDict.datumB W Θ')) := by
    by_cases h0 : lam = 0
    · obtain ⟨z', -, -, -, -, hz'⟩ := hc₀ 0 (Submodule.zero_mem _)
      have h1 := hz' _ aA (by rw [hpp, h0, zero_smul, map_zero, smul_zero])
      have h2 := GlobalTheory.RegCompare.thetaInt_smul ωB (M₁.ν _) (M₁.fd _) 0 0
      rw [zero_smul, zero_smul] at h2
      rw [h1, map_zero, h2, h0, zero_mul, zero_smul, smul_zero, smul_zero]
    · have h1 := hz ((zdeg z * lam⁻¹) • GlobalTheory.SquareDict.datumA W Θ) (Submodule.smul_mem _ _ aA)
        (by rw [map_smul, hpp, smul_smul, mul_assoc, inv_mul_cancel₀ h0, mul_one])
      rw [GlobalTheory.RegCompare.thetaInt_smul] at h1
      rw [mul_smul, ← h1, smul_smul, mul_left_comm, mul_inv_cancel₀ h0, mul_one]
  have invA : ∀ γ ∈ GQ (G.V (.grid (i + 1) (j + 1))), ∀ u, kerBig W Θ g g₁ (γ * u) = kerBig W Θ g g₁ u := fun γ hγ u => by
    rw [kA, kA, thetaKO_left_neg W.θ_is _ _ hm.weilA aA γ hγ]
  have invB : ∀ γ ∈ GQ (G.V (.grid i j)), ∀ u, translates z (kerSmall W Θ' g g₁) (γ * u) = translates z (kerSmall W Θ' g g₁) u :=
    fun γ hγ u => by
      rw [kB, kB, ez, GlobalTheory.SquareComm.ThetaLeft.main D W.ψ W.θ W.θ_is _ _ _ _ _ _ ωB hm.weilB _ hzS γ hγ]
  refine ⟨z, hz0, ⟨hconv, ?_⟩, ?_⟩
  · rw [GlobalTheory.VolIdent.vol_integrableOn_iff M M₁ hM hM₁ hsm _ invB, funext (kB z g g₁), ez]
    exact (GlobalTheory.RegCompare.intg_of_modInt hzM _).const_mul _
  · rw [GlobalTheory.VolIdent.vol_setIntegral_eq M M₁ hM hM₁ hbig _ invA, GlobalTheory.VolIdent.vol_setIntegral_eq M M₁ hM hM₁ hsm _ invB,
      iA, iB, ez]
    have := congrFun hI (GlobalTheory.SquareComm.blk _ _ (g, g₁))
    simp only [_root_.Pi.smul_apply, smul_eq_mul] at this
    linear_combination κ (g, g₁) * this

end GlobalTheory.SquareIdent

end
