import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsGridFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorOrthogonalBoxProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawOneSourceOrthogonalSumTargets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductRouteBEqExternalProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteCombinationMulLiftByDegree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict.AlgSmall

open GlobalTheory.FockAdjoint GlobalTheory.PairLift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

def negFr {V : HSp D} (B : Fr V) : Fr (negSp V) := GlobalTheory.SquareComm.frSgn true B

theorem negFr_cart {V : HSp D} (B : Fr V) (τ : D.what₂.Tau) : (negFr B).cart τ = -B.cart τ := by
  have e' : Formalism.REAL.Jm (fun a => xor true (B.ε τ a)) = -Formalism.REAL.Jm (B.ε τ) := by
    ext a b
    by_cases h : a = b
    · subst h; cases h' : B.ε τ a <;> simp [Formalism.REAL.Jm, h']
    · simp [Formalism.REAL.Jm, h]
  show (B.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (B.ε τ a)) * B.fr τ = -((B.fr τ)⁻¹ * Formalism.REAL.Jm (B.ε τ) * B.fr τ)
  rw [e', Matrix.mul_neg, Matrix.neg_mul]

def rd (S V : HSp D) (g : WO (negSp V) S → ℂ) : WO S V → ℂ := fun y => g (adjO (negSp V) S y)

variable {S V : HSp D}

theorem rd_eq (g : WO (negSp V) S → ℂ) : rd S V g = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (dag (negSp V) S g) := by
  funext y; simp [rd, dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]

theorem rd_theta (hψ : IsStdChar D ψ (-1)) {g : WO (negSp V) S → ℂ} (hg : IsThetaFunO ψ (negSp V) S g) :
    IsThetaFunO ψ S V (rd S V g) := by
  rw [rd_eq]
  exact GlobalTheory.CjNeg.theta_negT' hψ ((GlobalTheory.AdjLawPf.adjLaw D ψ hψ (negSp V) S).theta g hg)

theorem dRho_rd (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (w : Matrix (Fin V.rank) (Fin S.rank) ℂ) (g : WO (negSp V) S → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S V) θ τ w (rd S V g) =
      rd S V (Formalism.IndefR.Datum.dRho (heisO ψ (negSp V) S) θ τ (cdag (negSp V) S τ w) g) := by
  have L := GlobalTheory.AdjLawPf.adjLaw D ψ hψ (negSp V) S
  funext x
  show deriv (fun t : ℝ => heisO ψ S V (lineAt θ τ w t) (rd S V g) x) 0 =
    deriv (fun t : ℝ => heisO ψ (negSp V) S (lineAt θ τ (cdag (negSp V) S τ w) t) g (adjO (negSp V) S x)) 0
  congr 1
  funext t
  rw [rd_eq, GlobalTheory.CjNeg.heis_negT' hψ, L.Heisenberg₂, ← rd_eq, lineAt_adjO hθ L]
  rfl

theorem cdag_cplx_neg (A : Fr S) (B : Fr V) (τ : D.what₂.Tau) (w : Matrix (Fin V.rank) (Fin S.rank) ℂ) :
    cdag (negSp V) S τ (cplxO (A.cart τ) (B.cart τ) w) =
      cplxO ((negFr B).cart τ) (A.cart τ) (cdag (negSp V) S τ w) := by
  have h := cdag_cplx τ (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv (negFr B) τ)
    (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ) w
  have e : cplxO (A.cart τ) ((negFr B).cart τ) w = -cplxO (A.cart τ) (B.cart τ) w := by
    rw [negFr_cart]; simp [cplxO]
  rw [e] at h
  have e2 : ∀ z : Matrix (Fin V.rank) (Fin S.rank) ℂ, cdag (negSp V) S τ (-z) = -cdag (negSp V) S τ z := by
    intro z; simp [cdag]
  rw [e2] at h
  exact neg_inj.1 h

theorem rd_vac (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr V) {g : WO (negSp V) S → ℂ}
    (hg : IsVacF ψ θ (negFr B) A g) : IsVacF ψ θ A B (rd S V g) := by
  refine ⟨rd_theta hψ hg.1, fun τ w => ?_⟩
  have h0 := hg.2 τ (cdag (negSp V) S τ w)
  unfold annih at h0 ⊢
  rw [dRho_rd hψ hθ, dRho_rd hψ hθ, cdag_cplx_neg]
  funext x
  exact congrFun h0 (adjO (negSp V) S x)

theorem aPlus_rd (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr V) (τ : D.what₂.Tau)
    (w : Matrix (Fin V.rank) (Fin S.rank) ℂ) (g : WO (negSp V) S → ℂ) :
    aPlus (heisO ψ S V) θ τ (cplxO (A.cart τ) (B.cart τ)) w (rd S V g) =
      rd S V (aPlus (heisO ψ (negSp V) S) θ τ (cplxO ((negFr B).cart τ) (A.cart τ)) (cdag (negSp V) S τ w) g) := by
  unfold aPlus crea
  rw [dRho_rd hψ hθ, dRho_rd hψ hθ, cdag_cplx_neg]
  rfl

theorem rd_ptF (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr V) {g : WO (negSp V) S → ℂ}
    (hg : IsThetaFunO ψ (negSp V) S g) (P : PolF D S.rank (negSp V).rank) :
    ∃ Q, rd S V (ptF ψ θ (negFr B) A g P) = ptF ψ θ A B (rd S V g) Q := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨MvPolynomial.C a * 1, ?_⟩
    rw [ptF_C, ptF_one, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one]
    rfl
  | add p q hp hq =>
    obtain ⟨p', hp⟩ := hp
    obtain ⟨q', hq⟩ := hq
    refine ⟨p' + q', ?_⟩
    rw [ptF_add, ptF_add, ← hp, ← hq]
    rfl
  | mul_X p v hp =>
    obtain ⟨p', hp⟩ := hp
    obtain ⟨τ, i, j⟩ := v
    refine ⟨MvPolynomial.C (sgv (negFr B) A τ i j) * (MvPolynomial.X (τ, j, i) * p'), ?_⟩
    rw [ptF_C, ptF_X_mul hψ hθ A B (rd_theta hψ hg), ← hp, mul_comm p, ptF_X_mul hψ hθ (negFr B) A hg]
    dsimp only
    have e := cdag_unitMap (negFr B) A τ i j
    have e' : (negFr B).onb τ = B.onb τ := rfl
    rw [aPlus_rd hψ hθ, ← e', e, aPlus_real_smul hψ hθ (ptF_theta hψ hθ (negFr B) A hg p)]
    funext x
    have := sgv_mul_self (negFr B) A τ i j
    simp only [rd, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc]
    change _ = (sgv (negFr B) A τ i j * sgv (negFr B) A τ i j) * _
    rw [this, one_mul]

section Box

def prL (a b : ℕ) : Matrix (Fin a) (Fin (a + b)) ℂ :=
  (fromCols (1 : Matrix (Fin a) (Fin a) ℂ) (0 : Matrix (Fin a) (Fin b) ℂ)).submatrix id finSumFinEquiv.symm

def prR (a b : ℕ) : Matrix (Fin b) (Fin (a + b)) ℂ :=
  (fromCols (0 : Matrix (Fin b) (Fin a) ℂ) (1 : Matrix (Fin b) (Fin b) ℂ)).submatrix id finSumFinEquiv.symm

theorem prL_blk {a b : ℕ} (X : Matrix (Fin a) (Fin a) ℂ) (Y : Matrix (Fin b) (Fin b) ℂ) :
    prL a b * GlobalTheory.Doubling.blkMat finSumFinEquiv X Y = X * prL a b := by
  unfold prL GlobalTheory.Doubling.blkMat
  rw [Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks]
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with s | s <;> simp [Matrix.mul_apply, Matrix.one_apply]

theorem prR_blk {a b : ℕ} (X : Matrix (Fin a) (Fin a) ℂ) (Y : Matrix (Fin b) (Fin b) ℂ) :
    prR a b * GlobalTheory.Doubling.blkMat finSumFinEquiv X Y = Y * prR a b := by
  unfold prR GlobalTheory.Doubling.blkMat
  rw [Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks]
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with s | s <;> simp [Matrix.mul_apply, Matrix.one_apply]

theorem Jm_append {a b : ℕ} (ε : Fin a → Bool) (ε' : Fin b → Bool) :
    Formalism.REAL.Jm (Fin.append ε ε') = GlobalTheory.Doubling.blkMat finSumFinEquiv (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε') := by
  refine GlobalTheory.Doubling.submatrix_inj finSumFinEquiv ?_
  rw [GlobalTheory.Doubling.submatrix_blkMat]
  ext (a | a) (b | b) <;> simp [Formalism.REAL.Jm, Matrix.diagonal_apply, Fin.ext_iff] <;> omega

theorem mul_inv_of_comm {k m : ℕ} {q : Matrix (Fin k) (Fin m) ℂ} {M : Matrix (Fin m) (Fin m) ℂ}
    {X : Matrix (Fin k) (Fin k) ℂ} (hM : IsUnit M) (hX : IsUnit X) (h : q * M = X * q) : q * M⁻¹ = X⁻¹ * q := by
  have hM' := (Matrix.isUnit_iff_isUnit_det _).1 hM
  have hX' := (Matrix.isUnit_iff_isUnit_det _).1 hX
  calc q * M⁻¹ = X⁻¹ * (X * q) * M⁻¹ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hX', Matrix.one_mul]
    _ = X⁻¹ * q * (M * M⁻¹) := by rw [← h]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hM', Matrix.mul_one]

variable {U U' : HSp D} (B : Fr U) (B' : Fr U') (τ : D.what₂.Tau)

theorem prL_onb : prL U.rank U'.rank * (GlobalTheory.SquareComm.frSum B B').onb τ = B.onb τ * prL U.rank U'.rank :=
  mul_inv_of_comm ((GlobalTheory.SquareComm.frSum B B').fr_unit τ) (B.fr_unit τ) (prL_blk _ _)

theorem prR_onb : prR U.rank U'.rank * (GlobalTheory.SquareComm.frSum B B').onb τ = B'.onb τ * prR U.rank U'.rank :=
  mul_inv_of_comm ((GlobalTheory.SquareComm.frSum B B').fr_unit τ) (B'.fr_unit τ) (prR_blk _ _)

theorem prL_cart : prL U.rank U'.rank * (GlobalTheory.SquareComm.frSum B B').cart τ = B.cart τ * prL U.rank U'.rank := by
  have h := prL_onb B B' τ
  show prL U.rank U'.rank * ((GlobalTheory.SquareComm.frSum B B').onb τ * Formalism.REAL.Jm (Fin.append (B.ε τ) (B'.ε τ)) *
    GlobalTheory.Doubling.blkMat finSumFinEquiv (B.fr τ) (B'.fr τ)) = B.onb τ * Formalism.REAL.Jm (B.ε τ) * B.fr τ * prL U.rank U'.rank
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Jm_append, Matrix.mul_assoc (B.onb τ), prL_blk, Matrix.mul_assoc,
    Matrix.mul_assoc, prL_blk]
  simp only [Matrix.mul_assoc]

theorem prR_cart : prR U.rank U'.rank * (GlobalTheory.SquareComm.frSum B B').cart τ = B'.cart τ * prR U.rank U'.rank := by
  have h := prR_onb B B' τ
  show prR U.rank U'.rank * ((GlobalTheory.SquareComm.frSum B B').onb τ * Formalism.REAL.Jm (Fin.append (B.ε τ) (B'.ε τ)) *
    GlobalTheory.Doubling.blkMat finSumFinEquiv (B.fr τ) (B'.fr τ)) = B'.onb τ * Formalism.REAL.Jm (B'.ε τ) * B'.fr τ * prR U.rank U'.rank
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Jm_append, Matrix.mul_assoc (B'.onb τ), prR_blk, Matrix.mul_assoc,
    Matrix.mul_assoc, prR_blk]
  simp only [Matrix.mul_assoc]

theorem pr_single {a b n : ℕ} (j : Fin n) :
    (∀ i : Fin a, prL a b * Matrix.single (Fin.castAdd b i) j (1 : ℂ) = Matrix.single i j 1 ∧
      prR a b * Matrix.single (Fin.castAdd b i) j (1 : ℂ) = 0) ∧
    (∀ i : Fin b, prL a b * Matrix.single (Fin.natAdd a i) j (1 : ℂ) = 0 ∧
      prR a b * Matrix.single (Fin.natAdd a i) j (1 : ℂ) = Matrix.single i j 1) := by
  refine ⟨fun i => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩⟩ <;>
  · ext k l
    by_cases h : l = j
    · subst h
      rw [Matrix.mul_single_apply_same]
      simp [prL, prR, Matrix.one_apply, Matrix.single_apply, eq_comm]
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ h]
      simp [Matrix.single_apply, Ne.symm h]

theorem pr_unit {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    (∀ i : Fin U.rank, prL U.rank U'.rank * unitMap C ((GlobalTheory.SquareComm.frSum B B').onb τ) (Fin.castAdd _ i) j =
        unitMap C (B.onb τ) i j ∧
      prR U.rank U'.rank * unitMap C ((GlobalTheory.SquareComm.frSum B B').onb τ) (Fin.castAdd _ i) j = 0) ∧
    (∀ i : Fin U'.rank, prL U.rank U'.rank * unitMap C ((GlobalTheory.SquareComm.frSum B B').onb τ) (Fin.natAdd _ i) j = 0 ∧
      prR U.rank U'.rank * unitMap C ((GlobalTheory.SquareComm.frSum B B').onb τ) (Fin.natAdd _ i) j =
        unitMap C (B'.onb τ) i j) := by
  have h := pr_single (a := U.rank) (b := U'.rank) j
  unfold unitMap
  refine ⟨fun i => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, prL_onb, Matrix.mul_assoc (B.onb τ), (h.1 i).1]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, prR_onb, Matrix.mul_assoc (B'.onb τ), (h.1 i).2, Matrix.mul_zero,
      Matrix.zero_mul]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, prL_onb, Matrix.mul_assoc (B.onb τ), (h.2 i).1, Matrix.mul_zero,
      Matrix.zero_mul]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, prR_onb, Matrix.mul_assoc (B'.onb τ), (h.2 i).2]

theorem heisenbergDerivative_externalProduct_hermitianSum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (z : Matrix (Fin (U.rank + U'.rank)) (Fin S.rank) ℂ) {f : WO S U → ℂ} {g : WO S U' → ℂ}
    (hf : IsThetaFunO ψ S U f) (hg : IsThetaFunO ψ S U' g) :
    Formalism.IndefR.Datum.dRho (heisO ψ S (GlobalTheory.Doubling.hsum U U')) θ τ z (box2 f g) =
      box2 (Formalism.IndefR.Datum.dRho (heisO ψ S U) θ τ (prL _ _ * z) f) g +
        box2 f (Formalism.IndefR.Datum.dRho (heisO ψ S U') θ τ (prR _ _ * z) g) := by
  have h := GlobalTheory.Core.Rk.FockBoxT.dRho_boxT (GlobalTheory.BiTransfer.sumDec U U') hθ hψ τ z hf hg
  have e1 : (GlobalTheory.BiTransfer.sumDec U U').qA.map (tauE D τ) = prL U.rank U'.rank := by
    rw [GlobalTheory.SeesawSumTarget.qA_sumDec]
    ext i j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    rcases s with s | s <;> simp [prL, Matrix.one_apply, apply_ite (tauE D τ)]
  have e2 : (GlobalTheory.BiTransfer.sumDec U U').qB.map (tauE D τ) = prR U.rank U'.rank := by
    rw [GlobalTheory.SeesawSumTarget.qB_sumDec]
    ext i j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    rcases s with s | s <;> simp [prR, Matrix.one_apply, apply_ite (tauE D τ)]
  rw [e1, e2] at h
  simp only [GlobalTheory.SeesawSumTarget.boxT_sumDec] at h
  exact h

theorem pr_cplxO {n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (z : Matrix (Fin (U.rank + U'.rank)) (Fin n) ℂ) :
    prL U.rank U'.rank * cplxO (m := U.rank + U'.rank) s ((GlobalTheory.SquareComm.frSum B B').cart τ) z =
      cplxO s (B.cart τ) (prL U.rank U'.rank * z) ∧
    prR U.rank U'.rank * cplxO (m := U.rank + U'.rank) s ((GlobalTheory.SquareComm.frSum B B').cart τ) z =
      cplxO s (B'.cart τ) (prR U.rank U'.rank * z) :=
  ⟨GlobalTheory.Core.Rk.FockBoxT.mul_cplxO (prL_cart B B' τ) s z, GlobalTheory.Core.Rk.FockBoxT.mul_cplxO (prR_cart B B' τ) s z⟩

theorem heisenbergDerivative_externalProduct_complexStructure (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (s : Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin (U.rank + U'.rank)) (Fin S.rank) ℂ) {f : WO S U → ℂ} {g : WO S U' → ℂ}
    (hf : IsThetaFunO ψ S U f) (hg : IsThetaFunO ψ S U' g) :
    Formalism.IndefR.Datum.dRho (heisO ψ S (GlobalTheory.Doubling.hsum U U')) θ τ (cplxO s ((GlobalTheory.SquareComm.frSum B B').cart τ) z)
              (box2 f g) =
      box2 (Formalism.IndefR.Datum.dRho (heisO ψ S U) θ τ (cplxO s (B.cart τ) (prL _ _ * z)) f) g +
        box2 f (Formalism.IndefR.Datum.dRho (heisO ψ S U') θ τ (cplxO s (B'.cart τ) (prR _ _ * z)) g) := by
  erw [← (pr_cplxO B B' τ s z).1, ← (pr_cplxO B B' τ s z).2]
  exact heisenbergDerivative_externalProduct_hermitianSum τ hψ hθ _ hf hg

theorem isThetaFunction_externalProductOnHermitianSum {f : WO S U → ℂ} {g : WO S U' → ℂ} (hf : IsThetaFunO ψ S U f) (hg : IsThetaFunO ψ S U' g) :
    IsThetaFunO ψ S (GlobalTheory.Doubling.hsum U U') (box2 f g) := by
  rw [← GlobalTheory.SeesawSumTarget.boxT_sumDec]
  exact (GlobalTheory.BiTransfer.sumDec U U').isThetaFunO_boxT hf hg

theorem fockVacuum_externalProductOnHermitianSum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) {f : WO S U → ℂ} {g : WO S U' → ℂ}
    (hf : IsVacF ψ θ A B f) (hg : IsVacF ψ θ A B' g) : IsVacF ψ θ A (GlobalTheory.SquareComm.frSum B B') (box2 f g) := by
  refine ⟨isThetaFunction_externalProductOnHermitianSum hf.1 hg.1, fun τ (z : Matrix (Fin (U.rank + U'.rank)) (Fin S.rank) ℂ) => ?_⟩
  have h1 := hf.2 τ (prL _ _ * z)
  have h2 := hg.2 τ (prR _ _ * z)
  unfold annih at h1 h2 ⊢
  rw [heisenbergDerivative_externalProduct_hermitianSum τ hψ hθ z hf.1 hg.1, heisenbergDerivative_externalProduct_complexStructure B B' τ hψ hθ _ z hf.1 hg.1]
  funext x
  have k1 := congrFun h1 (topR (A := U) (B := U') x)
  have k2 := congrFun h2 (botR (A := U) (B := U') x)
  simp only [box2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at k1 k2 ⊢
  linear_combination g (botR (A := U) (B := U') x) * k1 + f (topR (A := U) (B := U') x) * k2

theorem creationOperator_externalProductOnHermitianSum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S)
    (z : Matrix (Fin (U.rank + U'.rank)) (Fin S.rank) ℂ) {f : WO S U → ℂ} {g : WO S U' → ℂ}
    (hf : IsThetaFunO ψ S U f) (hg : IsThetaFunO ψ S U' g) :
    aPlus (heisO ψ S (GlobalTheory.Doubling.hsum U U')) θ τ (cplxO (A.cart τ) ((GlobalTheory.SquareComm.frSum B B').cart τ)) z (box2 f g) =
      box2 (aPlus (heisO ψ S U) θ τ (cplxO (A.cart τ) (B.cart τ)) (prL _ _ * z) f) g +
        box2 f (aPlus (heisO ψ S U') θ τ (cplxO (A.cart τ) (B'.cart τ)) (prR _ _ * z) g) := by
  unfold aPlus crea
  rw [heisenbergDerivative_externalProduct_hermitianSum τ hψ hθ z hf hg, heisenbergDerivative_externalProduct_complexStructure B B' τ hψ hθ _ z hf hg]
  funext x
  simp only [box2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem aPlus_zero (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {g : WO S U → ℂ} (hg : IsThetaFunO ψ S U g)
    (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin U.rank) (Fin U.rank) ℂ) :
    aPlus (heisO ψ S U) θ τ (cplxO sS sT) 0 g = 0 := by
  simpa using aPlus_real_smul hψ hθ hg τ sS sT 0 0

theorem fockVector_externalProductOnHermitianSum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) {f : WO S U → ℂ} {g : WO S U' → ℂ}
    (hf : IsThetaFunO ψ S U f) (hg : IsThetaFunO ψ S U' g) (P : PolF D U.rank S.rank) (Q : PolF D U'.rank S.rank) :
    ∃ R, box2 (ptF ψ θ A B f P) (ptF ψ θ A B' g Q) = ptF ψ θ A (GlobalTheory.SquareComm.frSum B B') (box2 f g) R := by
  have hfg := isThetaFunction_externalProductOnHermitianSum hf hg
  have H : ∃ R, box2 f (ptF ψ θ A B' g Q) = ptF ψ θ A (GlobalTheory.SquareComm.frSum B B') (box2 f g) R := by
    induction Q using MvPolynomial.induction_on with
    | C a =>
      refine ⟨MvPolynomial.C a * 1, ?_⟩
      rw [ptF_C, ptF_one, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one]
      funext x; simp only [box2, Pi.smul_apply, smul_eq_mul]; ring
    | add p q hp hq =>
      obtain ⟨p', hp⟩ := hp
      obtain ⟨q', hq⟩ := hq
      refine ⟨p' + q', ?_⟩
      rw [ptF_add, ptF_add, ← hp, ← hq]
      funext x; simp only [box2, Pi.add_apply]; ring
    | mul_X p v hp =>
      obtain ⟨p', hp⟩ := hp
      obtain ⟨τ, i, j⟩ := v
      refine ⟨MvPolynomial.X (τ, Fin.natAdd _ i, j) * p', ?_⟩
      rw [ptF_X_mul hψ hθ A _ hfg, ← hp, mul_comm p, ptF_X_mul hψ hθ A B' hg]
      dsimp only
      rw [creationOperator_externalProductOnHermitianSum B B' τ hψ hθ A _ hf (ptF_theta hψ hθ A B' hg p)]
      erw [((pr_unit B B' τ _ j).2 i).1, ((pr_unit B B' τ _ j).2 i).2]
      rw [aPlus_zero τ hψ hθ hf]
      funext x; simp [box2]
  have hg' := ptF_theta hψ hθ A B' hg Q
  induction P using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨R, hR⟩ := H
    refine ⟨MvPolynomial.C a * R, ?_⟩
    rw [ptF_C, ← hR, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one, externalProductOnHermitianSum_smul_left]
  | add p q hp hq =>
    obtain ⟨p', hp⟩ := hp
    obtain ⟨q', hq⟩ := hq
    refine ⟨p' + q', ?_⟩
    rw [ptF_add, ptF_add, ← hp, ← hq, externalProductOnHermitianSum_add_left]
  | mul_X p v hp =>
    obtain ⟨p', hp⟩ := hp
    obtain ⟨τ, i, j⟩ := v
    refine ⟨MvPolynomial.X (τ, Fin.castAdd _ i, j) * p', ?_⟩
    rw [ptF_X_mul hψ hθ A _ hfg, ← hp, mul_comm p, ptF_X_mul hψ hθ A B hf]
    dsimp only
    rw [creationOperator_externalProductOnHermitianSum B B' τ hψ hθ A _ (ptF_theta hψ hθ A B hf p) hg']
    erw [((pr_unit B B' τ _ j).1 i).1, ((pr_unit B B' τ _ j).1 i).2]
    rw [aPlus_zero τ hψ hθ hg']
    funext x; simp [box2]

end Box

theorem frSgn_false_cart (A : Fr S) (τ : D.what₂.Tau) : (GlobalTheory.SquareComm.frSgn false A).cart τ = A.cart τ := by
  simp [Fr.cart, GlobalTheory.SquareComm.frSgn]

theorem fockVector_product_adjointReading_algebraic (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {U : HSp D} (A : Fr S) (B : Fr U) (B' : Fr V)
    {f : WO S U → ℂ} {g : WO (negSp V) S → ℂ} (hf : IsVacF ψ θ A B f) (hg : IsVacF ψ θ (negFr B') A g)
    (P : PolF D U.rank S.rank) (Q : PolF D S.rank (negSp V).rank) :
    box2 (ptF ψ θ A B f P) (rd S V (ptF ψ θ (negFr B') A g Q)) ∈
      GlobalTheory.SquareComm.algF ψ θ false A (GlobalTheory.SquareComm.frSum B B') := by
  obtain ⟨Q', hQ⟩ := rd_ptF hψ hθ A B' hg.1 Q
  have hg' := rd_vac hψ hθ A B' hg
  obtain ⟨R, hR⟩ := fockVector_externalProductOnHermitianSum B B' hψ hθ A hf.1 hg'.1 P Q'
  have hv := fockVacuum_externalProductOnHermitianSum B B' hψ hθ A hf hg'
  have e : (GlobalTheory.SquareComm.frSgn false A).cart = A.cart := funext (frSgn_false_cart A)
  rw [hQ, hR]
  refine Submodule.subset_span ⟨box2 f (rd S V g), R, ⟨hv.1, fun τ => ?_⟩, ?_⟩
  · rw [e]; exact hv.2 τ
  · unfold GlobalTheory.SquareComm.fockF
    rw [e]; rfl

end GlobalTheory.SquareDict.AlgSmall

open GlobalTheory.SquareDict.AlgSmall in

theorem GlobalTheory.SquareDict.datumB_mem_algF : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (A₁ : Fr (G.V (.grid ↑i ↑j))) (AV : Fr (G.V (.grid ↑i (↑j + 1)))) (AV₁ : Fr (G.V (.grid (↑i + 1) ↑j))),
    GlobalTheory.SquareDict.IsGridFr W _ A₁ → GlobalTheory.SquareDict.IsGridFr W _ AV → GlobalTheory.SquareDict.IsGridFr W _ AV₁ →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
      GlobalTheory.SquareDict.datumB W Θ' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false A₁ (GlobalTheory.SquareComm.frSum AV AV₁) := by
  intro D T L sc G μ₀ _ W t i j A₁ AV AV₁ h₁ hV hV₁ B ρ Θ Θ' hΘ
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, he, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hΘ
  refine Submodule.sum_mem _ fun d hd => Submodule.smul_mem _ _ ?_
  obtain ⟨d₀, hd₀, P, rfl⟩ := GlobalTheory.SmallRoute.mem_support_tensT W hd
  obtain ⟨h1, h2⟩ := hloc d₀ hd₀
  have v1 := ρ.vT_is t i j i.2.le j.2
  have v2 := ρ.vX_is i j i.2 j.2.le
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  have t2 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h2.2 v2.2.theta
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have f1 := fun s => GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq h1.2
    v1.2.theta t1 (v1.2.fock s)
  have f2 := fun s => GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq h2.2
    v2.2.theta t2 (v2.2.fock s)
  have c₁ : A₁.cart = W.cart _ := funext fun s => (h₁ s).2
  have cV : AV.cart = W.cart _ := funext fun s => (hV s).2
  have cV₁ : (negFr AV₁).cart = fun s => -W.cart (.grid (i + 1) j) s := funext fun s => by rw [negFr_cart, (hV₁ s).2]
  have o₁ : A₁.onb = W.onb _ := funext fun s => (h₁ s).1
  have oV : AV.onb = W.onb _ := funext fun s => (hV s).1
  have oV₁ : (negFr AV₁).onb = W.onb (.grid (i + 1) j) := funext fun s => (hV₁ s).1
  have key := fockVector_product_adjointReading_algebraic W.ψ_std W.θ_is A₁ AV AV₁ (f := d₀.1.2) (g := d₀.2)
    ⟨t1, fun s => by rw [c₁, cV]; exact f1 s⟩ ⟨t2, fun s => by rw [c₁, cV₁]; exact f2 s⟩ P.1.2 P.2
  unfold ptF at key
  rw [c₁, cV, cV₁, o₁, oV, oV₁] at key
  exact key

end
