import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.APlusComm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPoint
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.FockAdjoint

variable {D : D7}

def cdag (S T : HSp D) (τ : D.what₂.Tau) (w : Matrix (Fin S.rank) (Fin T.rank) ℂ) : Matrix (Fin T.rank) (Fin S.rank) ℂ :=
  (gramAt D T τ)⁻¹ * wᴴ * gramAt D S τ

theorem compAt_adjO {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (τ : D.what₂.Tau) (y : WO T S) :
    compAt θ τ (adjO S T y) = cdag S T τ (compAt θ τ y) := by
  have e : ∀ {a b : ℕ} (x : Matrix (Fin a) (Fin b) (AE D)), compAt θ τ x = x.map ((θ τ).comp (infPart D)) :=
    fun _ => rfl
  have hi : ∀ x, ((θ τ).comp (infPart D)) (incA D x) = tauE D τ x := GlobalTheory.FockCompare.comp_incA hθ τ
  have hc : ∀ z, ((θ τ).comp (infPart D)) (cA D z) = starRingEnd ℂ (((θ τ).comp (infPart D)) z) :=
    GlobalTheory.FockCompare.comp_cA hθ τ
  have h1 : ((T.gram⁻¹).map (incA D)).map ((θ τ).comp (infPart D)) = (T.gram⁻¹).map (tauE D τ) := by
    ext a b; exact hi _
  have h2 : (((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D)).transpose).map ((θ τ).comp (infPart D)) =
      (y.map ((θ τ).comp (infPart D)))ᴴ := by
    ext a b; simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]; rw [hc]; rfl
  have h3 : (S.gram.map (incA D)).map ((θ τ).comp (infPart D)) = S.gram.map (tauE D τ) := by
    ext a b; exact hi _
  rw [e, e, adjO, Matrix.map_mul, Matrix.map_mul, h1, h2, h3, cdag, gramAt, gramAt,
    GlobalTheory.OrientedChar.map_inv_field _ _ (Formalism.L2.Theta.gram_det_ne T)]

theorem finPart_adjO (S T : HSp D) (y : WO T S) (hy : y.map (finPart D) = 0) :
    (adjO S T y).map (finPart D) = 0 := by
  have h0 : (((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D)).transpose).map (finPart D) = 0 := by
    ext a b
    have : finPart D (y b a) = 0 := congrFun (congrFun hy b) a
    simp [GlobalTheory.OrientedChar.finPart_cA_eq_zero this]
  rw [adjO, Matrix.map_mul, Matrix.map_mul, h0, Matrix.mul_zero, Matrix.zero_mul]

end GlobalTheory.FockAdjoint

namespace GlobalTheory.FockAdjoint

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem cdag_smul_real (τ : D.what₂.Tau) (t : ℝ) (w : Matrix (Fin S.rank) (Fin T.rank) ℂ) :
    cdag S T τ ((t : ℂ) • w) = (t : ℂ) • cdag S T τ w := by
  simp [cdag, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem cdag_zero (τ : D.what₂.Tau) : cdag S T τ (0 : Matrix (Fin S.rank) (Fin T.rank) ℂ) = 0 := by
  simp [cdag]

theorem lineAt_adjO (hθ : IsInfFam θ) (L : AdjLaw ψ S T) (τ : D.what₂.Tau) (w : Matrix (Fin S.rank) (Fin T.rank) ℂ)
    (t : ℝ) : adjO S T (lineAt θ τ w t) = lineAt θ τ (cdag S T τ w) t := by
  have hw := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ w
  let L' : ℝ →+ WO S T := (AddMonoidHom.mk' (adjO S T) L.add).comp (lineAt θ τ w)
  have hL' : IsLineAt θ τ (cdag S T τ w) L' := by
    refine ⟨L.cont.comp hw.1, fun t => finPart_adjO S T _ (hw.2.1 t), fun t τ' => ?_⟩
    show compAt θ τ' (adjO S T (lineAt θ τ w t)) = _
    rw [compAt_adjO hθ, hw.2.2 t τ']
    split_ifs with h
    · subst h; exact cdag_smul_real _ _ _
    · exact cdag_zero _
  have := GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ hL' (GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ _)
  exact DFunLike.congr_fun this t

theorem dRho_dag (hθ : IsInfFam θ) (L : AdjLaw ψ S T) (τ : D.what₂.Tau) (w : Matrix (Fin S.rank) (Fin T.rank) ℂ)
    (g : WO S T → ℂ) :
    dRho (heisO ψ T S) θ τ w (dag S T g) = dag S T (dRho (heisO ψ S T) θ τ (cdag S T τ w) g) := by
  funext x
  show deriv (fun t : ℝ => heisO ψ T S (lineAt θ τ w t) (dag S T g) x) 0 =
    starRingEnd ℂ (deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ (cdag S T τ w) t) g (adjO S T x)) 0)
  have e : (fun t : ℝ => heisO ψ T S (lineAt θ τ w t) (dag S T g) x) =
      fun t => star (heisO ψ S T (lineAt θ τ (cdag S T τ w) t) g (adjO S T x)) := by
    funext t
    rw [L.Heisenberg₂, dag, lineAt_adjO hθ L]
    rfl
  rw [e, deriv.star]
  rfl

end GlobalTheory.FockAdjoint

namespace GlobalTheory.FockAdjoint

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem gramAt_det_ne (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ).det ≠ 0 := by
  rw [gramAt, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)

theorem cart_adj {n : ℕ} {G s : Matrix (Fin n) (Fin n) ℂ} (h : IsCartanInv G s) : sᴴ * G = G * s := by
  rw [← Matrix.mul_one (sᴴ * G), ← h.1, ← Matrix.mul_assoc, h.2.1]

theorem cdag_cplx {aS : Matrix (Fin S.rank) (Fin S.rank) ℂ} {bT : Matrix (Fin T.rank) (Fin T.rank) ℂ} (τ : D.what₂.Tau)
    (hS : IsCartanInv (gramAt D S τ) aS) (hT : IsCartanInv (gramAt D T τ) bT)
    (w : Matrix (Fin S.rank) (Fin T.rank) ℂ) :
    cdag S T τ (cplxO bT aS w) = -cplxO aS bT (cdag S T τ w) := by
  have hu : IsUnit (gramAt D T τ).det := isUnit_iff_ne_zero.2 (gramAt_det_ne T τ)
  have k1 : aSᴴ * gramAt D S τ = gramAt D S τ * aS := cart_adj hS
  have k2 : (gramAt D T τ)⁻¹ * bTᴴ = bT * (gramAt D T τ)⁻¹ := by
    calc (gramAt D T τ)⁻¹ * bTᴴ = (gramAt D T τ)⁻¹ * (bTᴴ * gramAt D T τ) * (gramAt D T τ)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = (gramAt D T τ)⁻¹ * gramAt D T τ * bT * (gramAt D T τ)⁻¹ := by
          rw [cart_adj hT]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have key : (gramAt D T τ)⁻¹ * (bTᴴ * wᴴ * aSᴴ) * gramAt D S τ =
      bT * ((gramAt D T τ)⁻¹ * wᴴ * gramAt D S τ) * aS := by
    calc _ = ((gramAt D T τ)⁻¹ * bTᴴ) * wᴴ * (aSᴴ * gramAt D S τ) := by simp only [Matrix.mul_assoc]
      _ = (bT * (gramAt D T τ)⁻¹) * wᴴ * (gramAt D S τ * aS) := by rw [k1, k2]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [cdag, cdag, cplxO, cplxO, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    ← Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul, key, Complex.star_def, Complex.conj_I, neg_smul]

theorem dRho_neg' (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    dRho (heisO ψ S T) θ τ (-z) g = -dRho (heisO ψ S T) θ τ z g := by
  have := (GlobalTheory.FockSubst.dRho_laws hψ hθ hg τ z).2.2.2.1 (-1)
  simpa using this

theorem aPlus_dag (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (L : AdjLaw ψ S T)
    {aS : Matrix (Fin S.rank) (Fin S.rank) ℂ} {bT : Matrix (Fin T.rank) (Fin T.rank) ℂ} (τ : D.what₂.Tau)
    (hS : IsCartanInv (gramAt D S τ) aS) (hT : IsCartanInv (gramAt D T τ) bT)
    (w : Matrix (Fin S.rank) (Fin T.rank) ℂ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) :
    aPlus (heisO ψ T S) θ τ (cplxO bT aS) w (dag S T g) =
      dag S T (aPlus (heisO ψ S T) θ τ (cplxO aS bT) (cdag S T τ w) g) := by
  rw [GlobalTheory.FockSubst.aPlus_eq, GlobalTheory.FockSubst.aPlus_eq, dRho_dag hθ L, dRho_dag hθ L, cdag_cplx τ hS hT,
    dRho_neg' hψ hθ hg]
  funext x
  simp only [dag, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul, map_mul, map_add, map_neg, map_inv₀,
    Complex.conj_ofReal, Complex.conj_I]
  ring

theorem vac_dag (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (L : AdjLaw ψ S T)
    {aS : Matrix (Fin S.rank) (Fin S.rank) ℂ} {bT : Matrix (Fin T.rank) (Fin T.rank) ℂ} (τ : D.what₂.Tau)
    (hS : IsCartanInv (gramAt D S τ) aS) (hT : IsCartanInv (gramAt D T τ) bT) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ (cplxO aS bT) f) :
    IsFockVacAt (heisO ψ T S) θ τ (cplxO bT aS) (dag S T f) := by
  intro w
  have h0 := hv (cdag S T τ w)
  unfold annih at h0 ⊢
  rw [dRho_dag hθ L, dRho_dag hθ L, cdag_cplx τ hS hT, dRho_neg' hψ hθ hf]
  funext x
  have := congrFun h0 (adjO S T x)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  simp only [dag, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply]
  have e := congrArg (starRingEnd ℂ) this
  simp only [map_add, map_mul, Complex.conj_I, map_zero] at e
  rw [map_neg]
  linear_combination e

end GlobalTheory.FockAdjoint

namespace GlobalTheory.FockAdjoint

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

def sg (b : Bool) : ℝ := if b then 1 else -1

theorem sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> norm_num [sg]

theorem Jm_mul_self' {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

theorem Jm_single_Jm {m n : ℕ} (εm : Fin m → Bool) (εn : Fin n → Bool) (i : Fin m) (j : Fin n) :
    Formalism.REAL.Jm εm * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm εn =
      ((sg (εm i) * sg (εn j) : ℝ) : ℂ) • Matrix.single i j (1 : ℂ) := by
  ext k l
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul]
  by_cases hk : i = k
  · by_cases hl : j = l
    · subst hk hl
      cases εm i <;> cases εn j <;> simp [sg]
    · simp [hl]
  · simp [hk]

theorem cdag_unitMap (A : Fr S) (B : Fr T) (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank) :
    cdag S T τ (unitMap (B.onb τ) (A.onb τ) j i) =
      ((sg (B.ε τ i) * sg (A.ε τ j) : ℝ) : ℂ) • unitMap (A.onb τ) (B.onb τ) i j := by
  have ha : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hb : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
  have hu : IsUnit (gramAt D T τ).det := isUnit_iff_ne_zero.2 (gramAt_det_ne T τ)
  have e1 : (gramAt D T τ)⁻¹ * (B.fr τ)ᴴ = (B.fr τ)⁻¹ * Formalism.REAL.Jm (B.ε τ) := by
    have h : (B.fr τ)ᴴ = gramAt D T τ * ((B.fr τ)⁻¹ * Formalism.REAL.Jm (B.ε τ)) := by
      rw [← B.fr_gram τ]
      calc (B.fr τ)ᴴ = (B.fr τ)ᴴ * (Formalism.REAL.Jm (B.ε τ) * (B.fr τ * (B.fr τ)⁻¹) * Formalism.REAL.Jm (B.ε τ)) := by
            rw [Matrix.mul_nonsing_inv _ hb, Matrix.mul_one, Jm_mul_self', Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have e2 : ((A.fr τ)⁻¹)ᴴ * gramAt D S τ = Formalism.REAL.Jm (A.ε τ) * A.fr τ := by
    rw [← A.fr_gram τ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ ha, Matrix.conjTranspose_one, Matrix.one_mul]
  have e3 : (Matrix.single j i (1 : ℂ))ᴴ = Matrix.single i j (1 : ℂ) := by
    ext k l
    simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
    by_cases h1 : i = k <;> by_cases h2 : j = l <;> simp [h1, h2, eq_comm]
  simp only [unitMap, Fr.onb, Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.nonsing_inv_nonsing_inv _ hb, cdag]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, e3]
  calc (gramAt D T τ)⁻¹ * ((B.fr τ)ᴴ * (Matrix.single i j (1 : ℂ) * ((A.fr τ)⁻¹)ᴴ)) * gramAt D S τ
      = ((gramAt D T τ)⁻¹ * (B.fr τ)ᴴ) * Matrix.single i j (1 : ℂ) * (((A.fr τ)⁻¹)ᴴ * gramAt D S τ) := by
        simp only [Matrix.mul_assoc]
    _ = (B.fr τ)⁻¹ * (Formalism.REAL.Jm (B.ε τ) * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
        rw [e1, e2]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [Jm_single_Jm, Matrix.mul_smul, Matrix.smul_mul]

theorem aPlus_real_smul (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (t : ℝ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    aPlus (heisO ψ S T) θ τ (cplxO sS sT) ((t : ℂ) • z) g = (t : ℂ) • aPlus (heisO ψ S T) θ τ (cplxO sS sT) z g := by
  have hJ : cplxO sS sT ((t : ℂ) • z) = (t : ℂ) • cplxO sS sT z := by
    simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul]
    rw [smul_comm]
  rw [GlobalTheory.FockSubst.aPlus_eq, GlobalTheory.FockSubst.aPlus_eq, hJ, (GlobalTheory.FockSubst.dRho_laws hψ hθ hg τ z).2.2.2.1 t,
    (GlobalTheory.FockSubst.dRho_laws hψ hθ hg τ _).2.2.2.1 t]
  rw [smul_comm (-Complex.I) (t : ℂ), ← smul_add, smul_comm]

variable {V W : HSp D}

theorem ptF_theta (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr V) (B : Fr W) {g : WO V W → ℂ}
    (hg : IsThetaFunO ψ V W g) (Q : PolF D W.rank V.rank) : IsThetaFunO ψ V W (ptF ψ θ A B g Q) := by
  unfold ptF pureTensorO
  exact GlobalTheory.Ker.FockAlg.pure_mem (P := IsThetaFunO ψ V W) (fun _ _ h h' => GlobalTheory.OrientedHeis.theta_add h h')
    (fun a _ h => GlobalTheory.OrientedHeis.theta_smul a h) (fun _ _ h => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ h) hg Q

theorem ptF_X_mul (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr V) (B : Fr W) {g : WO V W → ℂ}
    (hg : IsThetaFunO ψ V W g) (Q : PolF D W.rank V.rank) (v : FVar D W.rank V.rank) :
    ptF ψ θ A B g (MvPolynomial.X v * Q) =
      aPlus (heisO ψ V W) θ v.1 (cplxO (A.cart v.1) (B.cart v.1)) (unitMap (A.onb v.1) (B.onb v.1) v.2.1 v.2.2)
        (ptF ψ θ A B g Q) := by
  unfold ptF pureTensorO
  refine GlobalTheory.Ker.FockAlg.pure_X_mul (P := IsThetaFunO ψ V W)
      (fun _ _ h h' => GlobalTheory.OrientedHeis.theta_add h h') (fun a _ h => GlobalTheory.OrientedHeis.theta_smul a h)
      (fun i _ h => ?_) (fun i j _ h => ?_) (fun i _ _ h h' => ?_) (fun i a _ h => ?_) hg Q v
  all_goals unfold aPlusAll
  · exact GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ h
  · exact GlobalTheory.FockSubst.aPlus_comm hψ hθ i.1 _ (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A)
      (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B) j.1 _ h
  · exact GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ h h'
  · exact GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a h

theorem ptF_C (A : Fr V) (B : Fr W) (g : WO V W → ℂ) (x : ℂ) (Q : PolF D W.rank V.rank) :
    ptF ψ θ A B g (MvPolynomial.C x * Q) = x • ptF ψ θ A B g Q := by
  unfold ptF
  rw [MvPolynomial.C_mul', map_smul]

theorem ptF_add (A : Fr V) (B : Fr W) (g : WO V W → ℂ) (p q : PolF D W.rank V.rank) :
    ptF ψ θ A B g (p + q) = ptF ψ θ A B g p + ptF ψ θ A B g q := by
  unfold ptF
  rw [map_add]

theorem ptF_one (A : Fr V) (B : Fr W) (g : WO V W → ℂ) : ptF ψ θ A B g 1 = g := by
  unfold ptF pureTensorO
  exact GlobalTheory.Ker.FockAlg.pure_one g

end GlobalTheory.FockAdjoint

namespace GlobalTheory.FockAdjoint

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

def sgv (A : Fr S) (B : Fr T) (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank) : ℂ :=
  ((sg (B.ε τ i) * sg (A.ε τ j) : ℝ) : ℂ)

theorem sgv_mul_self (A : Fr S) (B : Fr T) (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank) :
    sgv A B τ i j * sgv A B τ i j = 1 := by
  unfold sgv
  rw [← Complex.ofReal_mul, mul_mul_mul_comm, sg_mul_self, sg_mul_self, one_mul, Complex.ofReal_one]

theorem conj_sgv (A : Fr S) (B : Fr T) (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank) :
    starRingEnd ℂ (sgv A B τ i j) = sgv A B τ i j := Complex.conj_ofReal _

def jHom (A : Fr S) (B : Fr T) : PolF D T.rank S.rank →+* PolF D S.rank T.rank :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (starRingEnd ℂ))
    fun v => MvPolynomial.C (sgv A B v.1 v.2.1 v.2.2) * MvPolynomial.X (v.1, v.2.2, v.2.1)

def jInv (A : Fr S) (B : Fr T) : PolF D S.rank T.rank →+* PolF D T.rank S.rank :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (starRingEnd ℂ))
    fun v => MvPolynomial.C (sgv A B v.1 v.2.2 v.2.1) * MvPolynomial.X (v.1, v.2.2, v.2.1)

theorem jHom_C (A : Fr S) (B : Fr T) (c : ℂ) : jHom A B (MvPolynomial.C c) = MvPolynomial.C (starRingEnd ℂ c) := by
  simp [jHom]

theorem jHom_X (A : Fr S) (B : Fr T) (v : FVar D T.rank S.rank) :
    jHom A B (MvPolynomial.X v) = MvPolynomial.C (sgv A B v.1 v.2.1 v.2.2) * MvPolynomial.X (v.1, v.2.2, v.2.1) := by
  simp [jHom]

theorem jInv_jHom (A : Fr S) (B : Fr T) : (jInv A B).comp (jHom A B) = RingHom.id _ := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
  · simp [jHom, jInv]
  · simp only [RingHom.comp_apply, jHom_X, map_mul, RingHom.id_apply]
    simp only [jInv, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', RingHom.comp_apply, conj_sgv]
    rw [← mul_assoc, ← map_mul, sgv_mul_self, map_one, one_mul]

theorem jHom_jInv (A : Fr S) (B : Fr T) : (jHom A B).comp (jInv A B) = RingHom.id _ := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
  · simp [jHom, jInv]
  · simp only [RingHom.comp_apply, RingHom.id_apply, jInv, MvPolynomial.eval₂Hom_X', map_mul, RingHom.comp_apply]
    rw [jHom_C, jHom_X, conj_sgv, ← mul_assoc, ← map_mul, sgv_mul_self, map_one, one_mul]

def jEquiv (A : Fr S) (B : Fr T) : PolF D T.rank S.rank ≃+* PolF D S.rank T.rank :=
  RingEquiv.ofRingHom (jHom A B) (jInv A B) (jHom_jInv A B) (jInv_jHom A B)

theorem dag_add (f g : WO S T → ℂ) : dag S T (f + g) = dag S T f + dag S T g := by
  funext x; simp [dag]

theorem dag_smul' (c : ℂ) (f : WO S T → ℂ) : dag S T (c • f) = starRingEnd ℂ c • dag S T f := by
  funext x; simp [dag]

end GlobalTheory.FockAdjoint

open GlobalTheory.FockAdjoint in

theorem GlobalTheory.FockAdjoint.fock_dag : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) →
    IsInfFam θ → ∀ (S T : HSp D) (A : Fr S) (B : Fr T), ∃ j : PolF D T.rank S.rank ≃+ PolF D S.rank T.rank,
      (∀ (c : ℂ) P, j (c • P) = starRingEnd ℂ c • j P) ∧ ∀ f, IsVacF ψ θ A B f → IsVacF ψ θ B A (dag S T f) ∧
        ∀ P, ptF ψ θ B A (dag S T f) (j P) = dag S T (ptF ψ θ A B f P) := by
  intro D ψ θ hψ hθ S T A B
  have L := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hψ S T
  have cA := GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A
  have cB := GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B
  refine ⟨(jEquiv A B).toAddEquiv, fun c P => ?_, fun f hf => ⟨⟨L.theta f hf.1, fun τ =>
    vac_dag hψ hθ L τ (cA τ) (cB τ) hf.1 (hf.2 τ)⟩, fun P => ?_⟩⟩
  · show jHom A B (c • P) = starRingEnd ℂ c • jHom A B P
    rw [MvPolynomial.smul_eq_C_mul, map_mul, jHom_C, MvPolynomial.smul_eq_C_mul]
  · have hd := L.theta f hf.1
    show ptF ψ θ B A (dag S T f) (jHom A B P) = dag S T (ptF ψ θ A B f P)
    induction P using MvPolynomial.induction_on with
    | C a =>
      rw [jHom_C, ← mul_one (MvPolynomial.C _), ptF_C, ptF_one, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one,
        dag_smul']
    | add p q hp hq => rw [map_add, ptF_add, ptF_add, hp, hq, dag_add]
    | mul_X p v hp =>
      obtain ⟨τ, i, j⟩ := v
      rw [map_mul, jHom_X, mul_comm (jHom A B p), mul_assoc, ptF_C, ptF_X_mul hψ hθ B A hd, hp, mul_comm p,
        ptF_X_mul hψ hθ A B hf.1]
      dsimp only
      rw [aPlus_dag hψ hθ L τ (cA τ) (cB τ) _ (ptF_theta hψ hθ A B hf.1 p), cdag_unitMap,
        aPlus_real_smul hψ hθ (ptF_theta hψ hθ A B hf.1 p), dag_smul', Complex.conj_ofReal, smul_smul]
      rw [show ((sg (B.ε τ i) * sg (A.ε τ j) : ℝ) : ℂ) = sgv A B τ i j from rfl, sgv_mul_self, one_smul]
