import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAniso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBottomTriIs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBottomPairFinitePlacesBelowOfMemExceptional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomInfinityExponentsGapLargeGridsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainUnitaryQuotientVolume
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesIntegralNonzeroConstant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixAndKillThetaOffSupportMoveStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMatrixCoefficientEqZeroOfHeisenbergRelationsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchrodingerIntertwinerInjectiveSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionNegPairPureTensorFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndex
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumEqProdSplitPlaceFactors
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatNotSelfDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
import Development.AutomorphicArithmetic.DivisorFrames.FiniteComponentMemStabilizerOfStandardSectionNeZ
import Development.AutomorphicArithmetic.DivisorFrames.StdFstActOOfMemStabilizer
import Development.AutomorphicArithmetic.DivisorFrames.IsUnitDetProdDetIdlOfMemSt
import Development.AutomorphicArithmetic.DivisorFrames.ExistsStdFstNeZeroOfRankLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.BottomLoc

open GlobalTheory.BottomIPData

private theorem rcoef_one {D : D7} (V : HSp D) (m : Measure (GA D V)) (hm : m.IsHaarMeasure) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ g, rcoef m (fun _ => (1 : ℂ)) (fun _ => 1) g = c := by
  obtain ⟨ν, 𝓕, hν, h𝓕⟩ := GlobalTheory.ConstRatio.exists_meas V
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have h𝓕' : IsFundamentalDomain (GQ V) 𝓕 m := h𝓕.mono (Measure.absolutelyContinuous_isHaarMeasure m ν)
  refine ⟨((m 𝓕).toReal : ℂ), ?_, fun g => ?_⟩
  · exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨h𝓕'.measure_ne_zero (NeZero.ne m),
      (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V m _ hm h𝓕').ne⟩)
  · have e : rcoef m (fun _ => (1 : ℂ)) (fun _ => 1) g = ∫ _ in 𝓕, (1 : ℂ) * conj (1 : ℂ) ∂m :=
      GlobalTheory.AutomorphicL2Unitary.pet_eq h𝓕' (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    rw [e]
    simp [Measure.real]

private def topPol (D : D7) {a d : ℕ} (h : a ≤ d) (n : D.what₂.Tau → ℕ) : MvPolynomial (FVar D d a) ℂ :=
  ∏ τ, (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, Fin.castLE h i, i') : MvPolynomial (FVar D d a) ℂ)).det ^ n τ

private theorem topPol_ne_zero (D : D7) {a d : ℕ} (h : a ≤ d) (n : D.what₂.Tau → ℕ) : topPol D h n ≠ 0 := by
  intro h0
  have := congrArg (MvPolynomial.eval fun p : FVar D d a => if p.2.1.1 = p.2.2.1 then (1 : ℂ) else 0) h0
  rw [topPol, map_prod, map_zero, Finset.prod_eq_one] at this
  · exact one_ne_zero this
  · intro τ _
    rw [map_pow, RingHom.map_det]
    have e : (MvPolynomial.eval fun p : FVar D d a => if p.2.1.1 = p.2.2.1 then (1 : ℂ) else 0).mapMatrix
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, Fin.castLE h i, i') : MvPolynomial (FVar D d a) ℂ)) = 1 := by
      ext i i'
      simp [Matrix.one_apply, Fin.ext_iff]
    rw [e, Matrix.det_one, one_pow]

private theorem substF_topPol (D : D7) {a d : ℕ} (h : a ≤ d) (n : D.what₂.Tau → ℕ)
    (g : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) g (topPol D h n) =
      (∏ τ, (g τ).det ^ n τ) • topPol D h n := by
  unfold topPol
  have key : ∀ (τ : D.what₂.Tau) (r : Fin a → Fin d),
      GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) g
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, r i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det =
      MvPolynomial.C (g τ).det *
        (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, r i, i') : MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ)).det := by
    intro τ r
    rw [AlgHom.map_det, RingHom.map_det (MvPolynomial.C : ℂ →+* MvPolynomial (D.what₂.Tau × Fin d × Fin a) ℂ), mul_comm,
      ← Matrix.det_mul]
    congr 1
    ext1 i i'
    simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      GlobalTheory.CompactHowe.substF_X, Matrix.one_apply]
    rw [Finset.sum_eq_single (r i)]
    · simp [mul_comm]
    · intro b _ hb
      simp [hb]
    · simp
  rw [map_prod, MvPolynomial.smul_eq_C_mul, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_pow, key τ (Fin.castLE h), mul_pow, map_pow]

private theorem conj_transpose_inv {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (h : uᴴ * u = 1) :
    (((1 : Matrix (Fin m) (Fin m) ℂ)⁻¹ * u * 1)⁻¹)ᵀ.map (starRingEnd ℂ) = u := by
  rw [inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.inv_eq_left_inv h]
  ext i j
  simp [Matrix.conjTranspose_apply]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil}
  {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}

private theorem f_theta (hX : IsBottomTri W i j X) (t : T) : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) :=
  GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hX.is.isVac.1 hX.is.isVac.2.inf (hX.is.fst t) hX.is.isVac.2.theta

private theorem f_fock (hX : IsBottomTri W i j X) (t : T) (τ : D.what₂.Tau) :
    IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) :=
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.is.idem t)
  GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hX.is.isVac.1.1.1 hX.is.isVac.2.inf ho.infPart_eq ho.conj.infPart_eq (hX.is.fst t)
    hX.is.isVac.2.theta (f_theta hX t) (hX.is.isVac.2.fock τ)

set_option maxHeartbeats 1000000 in

private theorem real_fix (hX : IsBottomTri W i j X) (t : T) (hr : A.rank ≤ WW.rank) (n : D.what₂.Tau → ℕ)
    (hn : ∀ τ, HasInfExp D (betaB G i j / alphaB L i j t) τ ((n τ : ℚ) + (WW.rank : ℚ) / 2))
    {k : GA D (GlobalTheory.Grid.neg A)} (hk : k ∈ GinfC (GlobalTheory.Grid.neg A)) :
    (X.ω t).toSgn true (k, 1) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t)
      (topPol D hr n)) =
      pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (topPol D hr n) := by
  have h := isBottomTri_is hX
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have hW := h.weil t
  have hf := f_theta hX t
  have hv : ∀ ρ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ ρ (cplxO (-1) 1) (X.f t) := fun ρ => by
    have := f_fock hX t ρ
    simpa [(hX.std.2.2 ρ).1, (hX.stdW.2.2 ρ).1] using this
  have hgA : ∀ τ, gramAt D A τ = 1 := fun τ => by rw [gramAt, hX.std.1]; simp
  have hgW : ∀ τ, gramAt D WW τ = 1 := fun τ => by rw [gramAt, hX.stdW.1]; simp
  have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) :=
    funext fun τ => by rw [(hX.std.2.2 τ).1]
  have e2 : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
  have e3 : X.rA.B = fun _ => 1 := funext fun τ => (hX.std.2.2 τ).2
  have e4 : X.rW.B = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).2
  rw [e1, e2, e3, e4]
  choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ _ τ hθ hW.hecS hW.resS
  choose e he using fun τ => GlobalTheory.SplitParity.exists_int_add_half D _ _ τ _ hW.hecS hW.resS (ha τ)
  let k₀ : GA D A := GlobalTheory.Grid.ofSgn true A k
  have hu : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A k₀))ᴴ * compAt W.θ τ (Formalism.L2.Theta.mt A k₀) = 1 := fun τ => by
    have e : (compAt W.θ τ (Formalism.L2.Theta.mt A k₀)).conjTranspose * (gramAt D A τ) * compAt W.θ τ (Formalism.L2.Theta.mt A k₀) =
      gramAt D A τ := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ A k₀ τ
    rwa [hgA, Matrix.mul_one] at e
  have key := GlobalTheory.FockRealNeg.om_pureTensorO_neg D W.ψ W.θ A WW _ _ ((X.ω t).toSgn true) hW hθ (fun _ => 1) (fun _ => 1)
    (fun τ => by rw [hgA]; simp) (fun τ => by rw [hgW]; simp) a (fun τ => (n τ : ℚ) + (WW.rank : ℚ) / 2) ha
    hn (fun τ => e τ - A.rank) (fun τ => -(n τ : ℤ))
    (fun τ => by push_cast; rw [he τ]; show _ + (A.rank : ℚ) / 2 - _ = _; ring)
    (fun τ => by push_cast; ring) (X.f t) hf hv k hk 1 (one_mem _) (topPol D hr n)
  have c1 : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.JointHarm.compAt_mt_one' W.θ τ WW
  have ck : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp A) k) = compAt W.θ τ (Formalism.L2.Theta.mt A k₀) := fun τ => rfl
  have s1 : (fun τ => (((fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt WW 1) *
      (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ).map (starRingEnd ℂ)) = fun _ => 1 := by
    funext τ
    show ((1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt WW 1) * 1).map (starRingEnd ℂ) = 1
    rw [c1, inv_one, Matrix.one_mul, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have s2 : (fun τ => (((((fun _ => (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ)) τ)⁻¹ *
      compAt W.θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp A) k) * (fun _ => (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ)) τ)⁻¹)ᵀ).map
        (starRingEnd ℂ)) = fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A k₀) :=
    funext fun τ => conj_transpose_inv (hu τ)
  rw [s1, s2, substF_topPol, map_smul, smul_smul, ← Finset.prod_mul_distrib] at key
  have hone : (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (GlobalTheory.ChiGrid.negSp A) k)).det ^ (-(n τ : ℤ)) *
      (compAt W.θ τ (Formalism.L2.Theta.mt WW 1)).det ^ (e τ - A.rank) *
        (compAt W.θ τ (Formalism.L2.Theta.mt A k₀)).det ^ n τ) = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    have hne : (compAt W.θ τ (Formalism.L2.Theta.mt A k₀)).det ≠ 0 := (Matrix.isUnit_det_of_left_inverse (hu τ)).ne_zero
    rw [ck, c1, Matrix.det_one, _root_.one_zpow, mul_one, _root_.zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hne)]
  rw [hone, one_smul] at key
  exact key

private theorem exists_weights (hX : IsBottomTri W i j X) (t : T) {a b : D.what₂.Tau → ℚ}
    (h : ∀ τ, HasInfExp D (alphaB L i j t) τ (a τ) ∧ HasInfExp D (betaB G i j) τ (b τ) ∧
      2 * (a τ - b τ) < -((SqNum.botBig D i j + SqNum.botSmall D i j : ℕ) : ℚ)) :
    ∃ n : D.what₂.Tau → ℕ, ∀ τ, HasInfExp D (betaB G i j / alphaB L i j t) τ ((n τ : ℚ) + (WW.rank : ℚ) / 2) := by
  have hW := (isBottomTri_is hX).weil t
  have hd : WW.rank = SqNum.botBig D i j + SqNum.botSmall D i j := by rw [← hX.is.rank, hX.rank, hX.rank']
  have key : ∀ τ, ∃ n : ℕ, HasInfExp D (betaB G i j / alphaB L i j t) τ ((n : ℚ) + (WW.rank : ℚ) / 2) := fun τ => by
    obtain ⟨h1, h2, h3⟩ := h τ
    have h4 := GlobalTheory.RealQuot.hasInfExp_div D _ _ τ _ _ h1 h2
    obtain ⟨e, he⟩ := GlobalTheory.SplitParity.exists_int_add_half D _ _ τ _ hW.hecT hW.resT h4
    rw [← hd] at h3
    have h5 : (WW.rank : ℤ) ≤ e := by
      have : ((WW.rank : ℤ) : ℚ) ≤ (e : ℚ) := by push_cast; linarith
      exact_mod_cast this
    refine ⟨(e - WW.rank).toNat, ?_⟩
    have h6 : (((e - WW.rank).toNat : ℕ) : ℚ) = (e : ℚ) - WW.rank := by
      have := Int.toNat_of_nonneg (sub_nonneg.2 h5)
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) this
    convert h4 using 1
    rw [h6, he]; ring
  choose n hn using key
  exact ⟨n, hn⟩

private theorem chars_unram {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (hu : GlobalTheory.LFun.UnrOff (betaB G i j / alphaB L i j t) ((sfB G t : Finset (FinPl D)) : Set (FinPl D)))
    (v : FinPl D) (hv : ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (betaB G i j) v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (betaB G i j / alphaB L i j t) v := by
  classical
  have hS : v ∉ sfB G t := fun h => by
    obtain ⟨w, hw, e⟩ := Finset.mem_image.1 h
    exact hv w hw e
  have h0 : v ∉ G.pl.S0 := fun h => by
    have hw : G.pl.w v ∈ locPl G t := by
      unfold locPl GlobalTheory.ChiGrid.Places.W0
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
    exact hv _ hw (G.pl.under_w h)
  have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hχ : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (G.ch.chi (D.R.m - i)) v :=
    GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw =>
      (GlobalTheory.LFun.unrAt_iff_of_chrEq (G.ch.chi_eq _ h1 h2) w).2 (G.ch.unr _ h1 h2 w (by rwa [hw]))
  have hη : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D L.eta v :=
    GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w _ => (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 (L.C.isEta.unr w)
  refine ⟨fun x a b c d => ?_, GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => hu w ?_⟩
  · rw [betaB, MonoidHom.mul_apply, MonoidHom.pow_apply, hχ x a b c d, hη x a b c d, one_pow, one_mul]
  · show w.under (𝓞 D.host.F) ∉ sfB G t
    rwa [hw]

private theorem fin_fix {μ₀ : T} (hL : L.Is μ₀) (hX : IsBottomTri W i j X) (t : T)
    (hu : GlobalTheory.LFun.UnrOff (betaB G i j / alphaB L i j t) ((sfB G t : Finset (FinPl D)) : Set (FinPl D)))
    {k : GA D (GlobalTheory.Grid.neg A)} (hk : k ∈ GfC (GlobalTheory.Grid.neg A)) (hk' : k ∈ openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅) :
    (X.ω t).toSgn true (k, 1) (X.f t) = X.f t := by
  have h := isBottomTri_is hX
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW (betaB G i j) (betaB G i j / alphaB L i j t) ((X.ω t).toSgn true) := h.weil t
  have sdA : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' h.rigA.1
  have sdW : IsSelfDualC WW X.rW.Λ := h.rigW.1
  have he := h.idem t
  have hloc : ∀ v, proj D.sp.cm.sig (GlobalTheory.Grid.neg A).gram v k ∈ stabLoc D.sp.cm.sig (GlobalTheory.Grid.neg A).gram X.rA.Λ v :=
    fun v => hk' v (Finset.notMem_empty v)
  have hSt : Lev.finE (GlobalTheory.Grid.neg A) k ∈ Formalism.L2.DIV.St X.rA.β :=
    (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D (GlobalTheory.Grid.neg A) X.rA.β X.rA.Λ h.rigA.2.1 k).2 hloc
  have hid : ∀ w ∈ locPl G t, Formalism.L2.NTheta.IsIdemAt (GlobalTheory.RowVacScalar.idemAt w) w := fun w hw => by
    obtain ⟨⟨es, hes, -⟩, -⟩ := he
    exact Classical.epsilon_spec (p := fun e : AE D => Formalism.L2.NTheta.IsIdemAt e w) ⟨es w, hes w hw⟩
  have hvac := GlobalTheory.LatStabScalar.om_eq_prod_splitFac hW sdA sdW (locPl G t) hid (GlobalTheory.LevelPlaces.under_injOn he)
    (chars_unram hL t hu) k hk 1 (one_mem _)
    ((mem_levelOpen_iff_latHat D.sp.cm.sig (GlobalTheory.Grid.neg A).gram sdA.1.fg k).1 (mem_levelOpen.2 hloc))
    ((mem_levelOpen_iff_latHat D.sp.cm.sig WW.gram sdW.1.fg 1).1 (one_mem _))
    X.vac h.isVac.2.theta h.isVac.2.lat
  have hy := UpperTheory.isUnitDet_prod_detIdl_of_mem_St D (GlobalTheory.Grid.neg A) X.rA.β (X.e t) (locPl G t) he k hSt
  have hΦ := UpperTheory.stdFst_actO_of_mem_stabilizer D (GlobalTheory.Grid.neg A) WW X.rA.β X.rW.β (alphaB L i j t / betaB G i j) (X.e t) (locPl G t)
    (X.ideal (locPl G) t) he k hSt _ hy
  have d1 : ∀ w, GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) WW 1 = 1 := fun w => by
    unfold GlobalTheory.RowVacScalar.detIdl; split_ifs <;> simp
  have hc : (∏ w ∈ locPl G t, ((splitFacO (betaB G i j) (betaB G i j / alphaB L i j t)
      (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) (GlobalTheory.Grid.neg A) k)
      (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) WW 1) : Circle) : ℂ)) =
      (((alphaB L i j t / betaB G i j) (∏ w ∈ locPl G t,
        GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) (GlobalTheory.Grid.neg A) k) : Circle) : ℂ) := by
    rw [map_prod]
    refine Eq.trans ?_ (map_prod Circle.coeHom _ _).symm
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [d1, splitFacO, map_one, mul_one, MonoidHom.div_apply, MonoidHom.div_apply, inv_div]
    rfl
  rw [hc] at hvac
  have key := GlobalTheory.SchrMove.smul_om_eq D W.ψ (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ _ _ _ hW sdA sdW (X.e t)
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he) k 1
    (GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D _ WW _ _ _ _ sdA sdW h.rigA.2.1 h.rigW.2.1 k 1 hSt
      (by rw [map_one]; exact one_mem _))
    X.vac _ (X.f t) _ _ h.isVac.2.theta (h.fst t) (Circle.coe_ne_zero _) hvac hΦ
  exact smul_right_injective _ (Circle.coe_ne_zero _) key

private theorem std_isSB (hX : IsBottomTri W i j X) (t : T) :
    IsSBHalf (X.e t) (latO (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ fun _ => True)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (alphaB L i j t / betaB G i j) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β) := by
  have h := isBottomTri_is hX
  have sdA : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' h.rigA.1
  have sdW : IsSelfDualC WW X.rW.Λ := h.rigW.1
  have he := h.idem t
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := GlobalTheory.Grid.neg A) sdA.1 sdW.1 X.rA.β X.rW.β
  exact StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.stdFst_isSB (h.weil' t).hecT.1 he (GlobalTheory.ConstRatio.ideal_ne_bot X (locPl G) t) A WW
    X.rA.β X.rW.β _ (GlobalTheory.PlaceDatum.exists_den_frMapO (S := GlobalTheory.Grid.neg A) sdA.1.fg sdW.1.fg X.rA.β X.rW.β)
    ⟨K, hK, fun u hu => hC u (GlobalTheory.PlaceDatum.infPart_of_half (GlobalTheory.PlaceDatum.infPart_idemSum he) hu)⟩

private theorem f_ne_zero (hX : IsBottomTri W i j X) (t : T) : X.f t ≠ 0 := by
  have h := isBottomTri_is hX
  have sdA : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' h.rigA.1
  have he := h.idem t
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := h.fst t
  obtain ⟨x, hx⟩ := UpperTheory.exists_stdFst_ne_zero_of_rank_le D A WW X.rA.β X.rW.β (alphaB L i j t / betaB G i j) (X.e t) (locPl G t)
    (X.ideal (locPl G) t) (h.rank ▸ Nat.le_add_right _ _) he
  rw [hall Tm hTm]
  exact GlobalTheory.PlaceModelInj.placeModel_ne_zero D W.ψ (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ (X.e t) X.vac _ Tm h.isVac.1 sdA h.rigW.1
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 (GlobalTheory.PlaceDatum.infPart_idemSum he) hTm
    (GlobalTheory.Core.Rk.IP.Model.isSphOff_of_vac h.isVac ∅).2.2 (std_isSB hX t) fun h0 => hx (congrFun h0 x)

private theorem pt_theta (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A.rank) :
    IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW
      (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) :=
  (GlobalTheory.FockSph.isFockVec_pureTensorO (S := GlobalTheory.Grid.neg A) (T := WW) (sS := fun τ => -X.rA.s τ) (sT := X.rW.s)
    hX.is.isVac.1 hX.is.isVac.2.inf (fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hX.is.rigA.2.2 τ).1)
    (fun τ => (hX.is.rigW.2.2 τ).1) X.rA.B X.rW.B (f_theta hX t) (f_fock hX t) P).1

private theorem gramAt_neg (hX : IsBottomTri W i j X) (τ : D.what₂.Tau) : gramAt D (GlobalTheory.Grid.neg A) τ = -1 := by
  have e : (GlobalTheory.Grid.neg A).gram = -A.gram := GlobalTheory.Grid.neg_gram A
  rw [gramAt, e, hX.std.1]
  ext a b
  simp [Matrix.one_apply, apply_ite]

private theorem pt_ne_zero (hX : IsBottomTri W i j X) (t : T) {P : PolF D WW.rank A.rank} (hP : P ≠ 0) :
    pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P ≠ 0 := by
  have h := isBottomTri_is hX
  choose pW hpW using fun τ => (h.rigW.2.2 τ).2
  have hA : ∀ τ, IsONBasis (gramAt D (GlobalTheory.Grid.neg A) τ) (-X.rA.s τ) (X.rA.B τ) 0 := fun τ => by
    refine ⟨fun _ => -1, fun a => Or.inr ⟨rfl, Nat.zero_le _⟩, ?_, ?_⟩
    · rw [gramAt_neg hX, (hX.std.2.2 τ).2]
      ext a b
      simp [Matrix.one_apply, Matrix.diagonal_apply, apply_ite]
    · rw [(hX.std.2.2 τ).1, (hX.std.2.2 τ).2]
      ext a b
      simp [Matrix.one_apply, Matrix.diagonal_apply, apply_ite]
  have hinj := GlobalTheory.FockPolyInj.pureTensorO_injective_of_on W.ψ W.θ (GlobalTheory.Grid.neg A) WW h.isVac.1 h.isVac.2.inf
    (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B (fun _ => 0) pW hA hpW (X.f t) (f_theta hX t) (f_fock hX t) (f_ne_zero hX t)
  exact fun h0 => hP (hinj (h0.trans (map_zero _).symm))

private theorem wcoef_off (hX : IsBottomTri W i j X) (t : T) {ν : Measure (WO (GlobalTheory.Grid.neg A) WW)} {𝓕 : Set (WO (GlobalTheory.Grid.neg A) WW)}
    (hν : IsCovolOne (ratL WW (GlobalTheory.Grid.neg A)) ν 𝓕) (P : PolF D WW.rank A.rank) {g : GA D (GlobalTheory.Grid.neg A)}
    (hg : g ∈ openOff (GlobalTheory.Grid.neg A) X.rA.Λ (sfB G t)) (hn : g ∉ openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅) :
    wcoef ((X.ω t).toSgn true) ν 𝓕
      (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P)
      (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) g = 0 := by
  classical
  have h := isBottomTri_is hX
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW (betaB G i j) (betaB G i j / alphaB L i j t) ((X.ω t).toSgn true) := h.weil t
  have sdA : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' h.rigA.1
  have he := h.idem t
  have hint : ∀ v, (∀ PP ∈ locPl G t, PP.under (𝓞 D.host.F) ≠ v) →
      proj D.sp.cm.sig (GlobalTheory.Grid.neg A).gram v g ∈ stabLoc D.sp.cm.sig (GlobalTheory.Grid.neg A).gram X.rA.Λ v := fun v hv =>
    hg v fun hm => by
      obtain ⟨w, hw, e⟩ := Finset.mem_image.1 hm
      exact hv w hw e
  have hsupp := fun x hx => by_contra fun hx' => hn fun v _ =>
    (GlobalTheory.T.finitePart_mem_frameStabilizer_iff_local_stabilizer D (GlobalTheory.Grid.neg A) X.rA.β X.rA.Λ h.rigA.2.1 g).1
      (UpperTheory.finiteComponent_mem_stabilizer_of_standardSection_ne_zero D (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rA.β X.rW.β (alphaB L i j t / betaB G i j) (X.e t) (locPl G t)
        (X.ideal (locPl G) t) sdA h.rigA.2.1 (show A.rank ≤ WW.rank from h.rank ▸ Nat.le_add_right _ _) he g hint x hx hx') v
  obtain ⟨n, a, y, h0, h1, h2⟩ := GlobalTheory.T.heisenberg_fix_and_kill_theta_off_support_move D W.ψ (GlobalTheory.Grid.neg A) WW hW.std X.rA.Λ X.rW.Λ sdA h.rigW.1
    (locPl G t) (X.e t) he X.vac _ (X.f t) (std_isSB hX t) (h.fst t) g hsupp
  have k1 := GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (GlobalTheory.Grid.neg A) WW hW.std h.isVac.2.inf
    (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (f_theta hX t) n a y (fun l => (h0 l).1) P
  have k2 := GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D W.ψ W.θ (GlobalTheory.Grid.neg A) WW hW.std h.isVac.2.inf
    (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (f_theta hX t) n (fun l => conj (a l))
    (fun l => actO (GlobalTheory.Grid.neg A) WW g⁻¹ 1 (-(y l))) (fun l => (h0 l).2) P
  exact GlobalTheory.T.weilMatrixCoefficient_eq_zero_of_heisenberg_relations D W.ψ (GlobalTheory.Grid.neg A) WW _ _ _ hW ν 𝓕 hν _ (pt_theta hX t P) g n a y
    (k1.1.trans (by rw [h1])) (k2.1.trans (by rw [h2]; exact k2.2))

private theorem openOff_eq (hX : IsBottomTri W i j X) (Λ : Lat (GlobalTheory.Grid.neg A)) {a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)}
    (ha : IsMaj (GlobalTheory.Grid.neg A) a)
    (ha' : ∀ τ, (compAt W.θ τ a.1)ᴴ * (gramAt D (GlobalTheory.Grid.neg A) τ * (-X.rA.s τ)) * compAt W.θ τ a.1 = 1) :
    openOff (GlobalTheory.Grid.neg A) Λ ∅ = levelAll D.sp.cm.sig (GlobalTheory.Grid.neg A).gram Λ a := by
  have h1 : ∀ τ, frameInv W.θ (GlobalTheory.Grid.neg A) a τ = -1 := fun τ => by
    have h3 := ha' τ
    rw [gramAt_neg hX, (hX.std.2.2 τ).1, neg_mul_neg, Matrix.mul_one, Matrix.mul_one] at h3
    rw [frameInv, mul_eq_one_comm.1 h3, gramAt_neg hX, Matrix.one_mul]
  ext g
  rw [SetLike.mem_coe, mem_levelAll]
  refine ⟨fun hg => ⟨fun v => hg v (Finset.notMem_empty v), (placeOf_bijective D).2.forall.2 fun τ => ?_⟩,
    fun hg v _ => hg.1 v⟩
  refine (ha.mem_stabArch_iff hX.is.isVac.2.inf τ g).2 ?_
  rw [h1]
  exact Commute.neg_one_right _

end GlobalTheory.BottomLoc

open GlobalTheory.BottomIPData GlobalTheory.BottomLoc in

theorem _root_.GlobalTheory.T.definiteBottom_localDoublingIntegral_converges : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ (cA : CptF (GlobalTheory.Grid.neg A)) (a : GL (Fin (GlobalTheory.Grid.neg A).rank) (AE D)) (νW : Measure (WO (GlobalTheory.Grid.neg A) WW)) (𝓕W : Set (WO (GlobalTheory.Grid.neg A) WW)), Pair W.ψ W.θ (GlobalTheory.Grid.neg A) WW (GlobalTheory.BottomIPData.betaB G i j) (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) (fun τ => -X.rA.s τ) X.rW.s A'.rank cA a ((X.ω t).toSgn true) νW 𝓕W →
  ∃ P : PolF D WW.rank A.rank, ∀ m : Measure (GA D (GlobalTheory.Grid.neg A)), m.IsHaarMeasure →
    (∃ s₁ : ℝ, s₁ < (A'.rank : ℝ) / 2 ∧ IntegrableOn
      (integrand ((X.ω t).toSgn true) m νW 𝓕W X.rA.Λ a (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (fun _ => 1) (fun _ => 1) s₁) (openOff (GlobalTheory.Grid.neg A) X.rA.Λ (GlobalTheory.BottomIPData.sfB G t)) m) ∧
    ∫ g in openOff (GlobalTheory.Grid.neg A) X.rA.Λ (GlobalTheory.BottomIPData.sfB G t), wcoef ((X.ω t).toSgn true) νW 𝓕W (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) g * rcoef m (fun _ => 1) (fun _ => 1) g ∂m ≠ 0 := by
  have H0 : GBig fun {_} _ Lc _ _ μ₀ _ _ _ => Lc.Is μ₀ :=
    ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ _ _ _ _ _ _ _ _ hL _ => hL⟩⟩
  refine gbig_mono (gbig_and H0 (gbig_and GlobalTheory.T.unramifiedInnerProductData_definiteBottom_largeGrids GlobalTheory.T.exists_bottomInfinityExponents_gap_largeGrids)) ?_
  intro D T Lc sc G μ₀ C x b ⟨hL, H1, H2⟩ W i j A A' WW X hX t cA a νW 𝓕W hP
  have h := isBottomTri_is hX
  have hr : A.rank ≤ WW.rank := h.rank ▸ Nat.le_add_right _ _
  obtain ⟨ea, eb, hab⟩ := H2 W i j
  obtain ⟨n, hn⟩ := exists_weights hX t (hab t)
  refine ⟨topPol D hr n, fun m hm => ?_⟩
  have hU := H1 W i j A A' WW X hX t (topPol D hr n)
  have hoff := fun g => wcoef_off (g := g) hX t hP.covol (topPol D hr n)
  have hth := pt_theta hX t (topPol D hr n)
  have hne := pt_ne_zero hX t (topPol_ne_zero D hr n)
  have hfix : ∀ g ∈ openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅, (X.ω t).toSgn true (g, 1)
      (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (topPol D hr n)) =
      pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (topPol D hr n) := by
    intro g hg
    have hk := GlobalTheory.LevelNbhd.finPartG_mem_GfC (GlobalTheory.Grid.neg A) g
    have hk' : GlobalTheory.LevelNbhd.finPartG (GlobalTheory.Grid.neg A) g ∈ openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅ := fun v hv => by
      rw [GlobalTheory.SuppLevO.proj_finPartG]; exact hg v hv
    have e : ((g, 1) : GA D (GlobalTheory.Grid.neg A) × GA D WW) = (GlobalTheory.LevelNbhd.finPartG (GlobalTheory.Grid.neg A) g, 1) *
        ((GlobalTheory.LevelNbhd.finPartG (GlobalTheory.Grid.neg A) g)⁻¹ * g, 1) := by simp
    rw [e, map_mul, Module.End.mul_apply, real_fix hX t hr n hn (GlobalTheory.LevelNbhd.inv_finPartG_mul_mem_GinfC _ g),
      GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ WW _ _ _ hP.weil W.θ h.isVac.2.inf _ hk 1 (one_mem _) _ _ _ _ _ _
        (f_theta hX t), fin_fix hL hX t hU.unr hk hk']
  generalize pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (topPol D hr n) = Φ
    at hoff hth hne hfix ⊢
  obtain ⟨c, hc, hrc⟩ := rcoef_one (GlobalTheory.Grid.neg A) m hm
  set c₀ : ℂ := GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip (GlobalTheory.Grid.neg A) WW νW 𝓕W Φ Φ with hc₀
  have hc0 : c₀ ≠ 0 := by
    have h' := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hP.weil.std hth hne hP.covol
    have e : c₀ = GlobalTheory.RawLift.thetaIP νW 𝓕W Φ Φ := by
      simp only [hc₀, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, GlobalTheory.RawLift.thetaIP, mul_comm (Φ _), Complex.star_def]
    rwa [e]
  have hon : ∀ g ∈ openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅, wcoef ((X.ω t).toSgn true) νW 𝓕W Φ Φ g = c₀ := fun g hg => by
    simp only [wcoef, hfix g hg, hc₀]
  have hK := openOff_eq hX X.rA.Λ hP.maj hP.maj_eq
  haveI : Submodule.IsLattice D.host.E X.rA.Λ := hU.sdA.1
  have hhgt : ∀ g ∈ openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅, GlobalTheory.Core.Rk.IP.hgtL (GlobalTheory.Grid.neg A) X.rA.Λ a g = 1 := by
    rw [hK]
    intro g hg
    have := hgtAd_mul (Q := (dblSp (GlobalTheory.Grid.neg A)).gram) (L := X.rA.Λ) (a := a) (isCMExt_host D) 1
      (k := io (GlobalTheory.Grid.neg A) (g, 1)) ((ioH_mem_KAd _).2 ⟨hg, one_mem _⟩)
    simpa [GlobalTheory.Core.Rk.IP.hgtL] using this
  have hKc : IsCompact (openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅) := by
    rw [hK]
    exact isCompact_levelAll (isCMExt_host D) _ _ _
  have hKo : IsOpen (openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅) := GlobalTheory.Core.Rk.IP.isOpen_openOff _ _ hU.sdA _
  have hOm : MeasurableSet (openOff (GlobalTheory.Grid.neg A) X.rA.Λ (sfB G t)) :=
    (GlobalTheory.Core.Rk.IP.isOpen_openOff _ _ hU.sdA _).measurableSet
  have hsub : openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅ ⊆ openOff (GlobalTheory.Grid.neg A) X.rA.Λ (sfB G t) :=
    fun g hg v _ => hg v (Finset.notMem_empty v)
  have hI : ∀ s : ℂ, Set.EqOn (integrand ((X.ω t).toSgn true) m νW 𝓕W X.rA.Λ a Φ Φ (fun _ => 1) (fun _ => 1) s)
      ((openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅).indicator fun _ => c₀ * c) (openOff (GlobalTheory.Grid.neg A) X.rA.Λ (sfB G t)) := by
    intro s g hg
    by_cases hg' : g ∈ openOff (GlobalTheory.Grid.neg A) X.rA.Λ ∅
    · rw [Set.indicator_of_mem hg']
      simp only [integrand, hon g hg', hhgt g hg', hrc, one_npow, mul_one]
    · rw [Set.indicator_of_notMem hg']
      simp only [integrand, hoff g hg hg', zero_mul]
  refine ⟨⟨(A'.rank : ℝ) / 2 - 1, by linarith, ?_⟩, ?_⟩
  · refine IntegrableOn.congr_fun ?_ (hI _).symm hOm
    exact ((integrable_indicator_iff hKo.measurableSet).2 (integrableOn_const hKc.measure_ne_top)).integrableOn
  · simp only [← GlobalTheory.Core.Rk.IP.integrand_sZero _ m νW 𝓕W X.rA.Λ a]
    rw [setIntegral_congr_fun hOm (hI _), setIntegral_indicator hKo.measurableSet, Set.inter_eq_right.2 hsub,
      setIntegral_const]
    refine smul_ne_zero ?_ (mul_ne_zero hc0 hc)
    exact ENNReal.toReal_ne_zero.2 ⟨(hKo.measure_pos m ⟨1, GlobalTheory.Core.Rk.IP.one_mem_openOff _ _ _⟩).ne', hKc.measure_ne_top⟩

end
