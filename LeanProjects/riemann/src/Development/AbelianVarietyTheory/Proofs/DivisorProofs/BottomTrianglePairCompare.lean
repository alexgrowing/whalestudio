import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeightEqAbsInfType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionNegPairPureTensorFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndex
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotKerRealInv

open Matrix

private theorem substF_minorPol {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (g : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ)) g (GlobalTheory.NormSum.minorPol D T) =
      (∏ τ, (g τ).det ^ n τ) • GlobalTheory.NormSum.minorPol D T := by
  unfold GlobalTheory.NormSum.minorPol
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
  rw [map_prod]
  refine (Finset.prod_congr rfl fun j _ => key τ (T τ j).1).trans ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_pow]

private theorem substF_minorF {D : D7} {a d a₁ d₁ : ℕ} {n : D.what₂.Tau → ℕ} (ha : a = a₁) (hd : d = d₁) (T : Tup D a d n)
    (g : D.what₂.Tau → Matrix (Fin a₁) (Fin a₁) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin d₁) (Fin d₁) ℂ)) g (GlobalTheory.BotFormula.minorF ha hd T) =
      (∏ τ, (g τ).det ^ n τ) • GlobalTheory.BotFormula.minorF ha hd T := by
  subst ha hd
  have e : GlobalTheory.BotFormula.minorF rfl rfl T = GlobalTheory.NormSum.minorPol D T := by
    unfold GlobalTheory.BotFormula.minorF
    exact MvPolynomial.rename_id_apply _
  rw [e]
  exact substF_minorPol T g

private theorem conj_transpose_inv {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (h : uᴴ * u = 1) :
    (((1 : Matrix (Fin m) (Fin m) ℂ)⁻¹ * u * 1)⁻¹)ᵀ.map (starRingEnd ℂ) = u := by
  rw [inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.inv_eq_left_inv h]
  ext i j
  simp [Matrix.conjTranspose_apply]

private theorem hasInf_of_fin {D : D7} {N : ℕ} (χ : HeckeU D N) (e : ℤ) (χ' : Formalism.L2.Host.HChar D.host.E)
    (hf : ∀ x, χ.f x ^ e = χ'.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x)) :
    χ'.HasInf (Formalism.L2.Host.embTau D) (fun τ => e * χ.n τ) := by
  intro u
  set φ := Formalism.L2.Host.embTau D
  have hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
      ∏ τ, (φ τ u / ((‖φ τ u‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1 := χ.aut u
  have hB := χ'.2.2 u
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← GlobalTheory.Mem.Col2.SplitChar.finIdl_incU, ← hf] at hB
  have hB' : ((χ'.inf u : ℂˣ) : ℂ) * ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) ^ e = 1 := by
    have := congrArg Units.val hB
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_one] at this
    exact this
  rw [eq_inv_of_mul_eq_one_left hA, _root_.inv_zpow, ← Finset.prod_zpow] at hB'
  rw [eq_inv_of_mul_eq_one_left hB', inv_inv]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← _root_.zpow_mul, mul_comm]

private theorem hasInfExp_nu_inv {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc)
    (s : T) (i j : Fin D.R.m) {δ t0 : ℂ} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q} {𝔪} (hB : IsBottom G s i j 𝔪 P P')
    (τ : D.what₂.Tau) :
    HasInfExp D (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2) / (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2))) τ
      ((P.n τ : ℚ) + (P.d : ℚ) / 2) := by
  have h1 := hasInf_of_fin P.W.chV' P.W.ep' _ hB.chars.2
  have h2 : (nuH G s i j).HasInfQ (tauE D) fun τ => -((P.n τ : ℚ) + (P.d : ℚ) / 2) := by
    refine ⟨fun τ => -(P.W.ep' * P.W.chV'.n τ), fun τ => ?_, fun k => ?_⟩
    · have : ((2 * (P.n τ : ℤ) : ℤ) : ℚ) = ((P.W.ep' * P.W.chV'.n τ - (P.d : ℤ) : ℤ) : ℚ) := by rw [P.wt τ]
      push_cast at this ⊢
      linarith
    · have h3 := h1 k
      rw [Formalism.L2.Host.HChar.inf_inv, Units.val_inv_eq_inv_val] at h3
      rw [← inv_inv (((nuH G s i j).inf k : ℂˣ) : ℂ), h3, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [_root_.zpow_neg]
      rfl
  have h4 := GlobalTheory.Chain.StepVac.hasInfExp_inv
    (GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (chrEq_nu G s i j hL) h2 τ)
  rw [neg_neg] at h4
  have e : G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2) / (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)) =
      (G.nu s i (j + 1))⁻¹ := by
    rw [mul_div_mul_right_eq_div, ← inv_div]
    rfl
  rw [e]
  exact h4

private theorem om_fix {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (s : T)
    {δ t0 : ℂ} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q} {𝔪} (hB : IsBottom G s i j 𝔪 P P') (ea : P.a = A.rank) (ed : P.d = WW.rank)
    (Tp : Tup D P.a P.d P.n) {k : Formalism.L2.Theta.GA D A} (hk : k ∈ GinfC A) :
    X.ω s (k, 1) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f s)
      (GlobalTheory.BotFormula.minorF ea ed Tp)) =
      pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f s)
        (GlobalTheory.BotFormula.minorF ea ed Tp) := by
  have h := hX.is
  have hψ : IsStdChar D W.ψ (-1) := h.isVac.1
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have hW := h.weil s
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f s) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (h.fst s) h.isVac.2.theta
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (h.idem s)
  have hv : ∀ ρ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ ρ (cplxO (-1) 1) (X.f s) := fun ρ => by
    have := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (h.fst s)
      h.isVac.2.theta hf (h.isVac.2.fock ρ)
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
  let k' : Formalism.L2.Theta.GA D (GlobalTheory.Grid.neg A) := (GlobalTheory.Grid.ofSgn true A).symm k
  have hk' : k' ∈ GinfC (GlobalTheory.Grid.neg A) :=
    (GlobalTheory.SgnIdent.mem_GinfC_sgn true A _).2 (by rwa [MulEquiv.apply_symm_apply])
  have hu : ∀ τ, (compAt W.θ τ (Formalism.L2.Theta.mt A k))ᴴ * compAt W.θ τ (Formalism.L2.Theta.mt A k) = 1 := fun τ => by
    have e : (compAt W.θ τ (Formalism.L2.Theta.mt A k)).conjTranspose * (gramAt D A τ) * compAt W.θ τ (Formalism.L2.Theta.mt A k) =
      gramAt D A τ := GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ A k τ
    rwa [hgA, Matrix.mul_one] at e
  have key := GlobalTheory.FockRealNeg.om_pureTensorO_neg D W.ψ W.θ A WW _ _ ((X.ω s).toSgn true) hW hθ (fun _ => 1) (fun _ => 1)
    (fun τ => by rw [hgA]; simp) (fun τ => by rw [hgW]; simp) a (fun τ => (P.n τ : ℚ) + (P.d : ℚ) / 2) ha
    (hasInfExp_nu_inv hL G s i j hB) (fun τ => e τ - A.rank) (fun τ => -(P.n τ : ℤ))
    (fun τ => by push_cast; rw [he τ]; show _ + (A.rank : ℚ) / 2 - _ = _; ring)
    (fun τ => by rw [← ed]; push_cast; ring) (X.f s) hf hv k' hk' 1 (one_mem _) (GlobalTheory.BotFormula.minorF ea ed Tp)
  have c1 : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.JointHarm.compAt_mt_one' W.θ τ WW
  have ck : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (negSp A) k') = compAt W.θ τ (Formalism.L2.Theta.mt A k) := fun τ => rfl
  have s1 : (fun τ => (((fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt WW 1) *
      (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) τ).map (starRingEnd ℂ)) = fun _ => 1 := by
    funext τ
    show ((1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt WW 1) * 1).map (starRingEnd ℂ) = 1
    rw [c1, inv_one, Matrix.one_mul, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have s2 : (fun τ => (((((fun _ => (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ)) τ)⁻¹ *
      compAt W.θ τ (Formalism.L2.Theta.mt (negSp A) k') * (fun _ => (1 : Matrix (Fin A.rank) (Fin A.rank) ℂ)) τ)⁻¹)ᵀ).map
        (starRingEnd ℂ)) = fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A k) :=
    funext fun τ => conj_transpose_inv (hu τ)
  rw [s1, s2, substF_minorF, map_smul, smul_smul, ← Finset.prod_mul_distrib] at key
  have hone : (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (negSp A) k')).det ^ (-(P.n τ : ℤ)) *
      (compAt W.θ τ (Formalism.L2.Theta.mt WW 1)).det ^ (e τ - A.rank) *
        (compAt W.θ τ (Formalism.L2.Theta.mt A k)).det ^ P.n τ) = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    have hne : (compAt W.θ τ (Formalism.L2.Theta.mt A k)).det ≠ 0 := (Matrix.isUnit_det_of_left_inverse (hu τ)).ne_zero
    rw [ck, c1, Matrix.det_one, _root_.one_zpow, mul_one, _root_.zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hne)]
  rw [hone, one_smul] at key
  exact key

end GlobalTheory.BotKerRealInv

end

theorem _root_.GlobalTheory.T.bottom_triangle_pair_compare : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (s : T) (Q : ℕ) (δ t0 : ℂ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (g : Formalism.L2.Theta.GA D WW) (T : Tup D P.a P.d P.n),
        ∀ k ∈ GinfC A, ∀ y, X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g (y * k) =
          X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g y := by
  intro _ _ _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W _ i j A A' WW X hX s Q δ t0 P P' hB ea ed g Tp k hk y
  unfold Tri.ker thetaKO
  have e : X.ω s (y * k, g) = X.ω s (y, g) * X.ω s (k, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  rw [e, Module.End.mul_apply, GlobalTheory.BotKerRealInv.om_fix hL hX s hB ea ed Tp hk]
