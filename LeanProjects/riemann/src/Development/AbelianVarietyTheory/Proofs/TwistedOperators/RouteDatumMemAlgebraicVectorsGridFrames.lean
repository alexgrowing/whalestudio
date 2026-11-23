import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsGridFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawOneSourceOrthogonalSumTargets
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorOrthogonalBoxProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsConjAdjointPullbackBijection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFockPureTensorMapNegFormSpaceEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SquareAlg

open GlobalTheory.MixModel GlobalTheory.FockAdjoint

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem eq_sum_unitMap {S T : HSp D} (A : Fr S) (B : Fr T) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    z = ∑ p : Fin T.rank × Fin S.rank, (B.fr τ * z * A.onb τ) p.1 p.2 • unitMap (A.onb τ) (B.onb τ) p.1 p.2 := by
  have ha : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hb : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
  have e : ∀ c : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      ∑ p : Fin T.rank × Fin S.rank, c p.1 p.2 • Matrix.single p.1 p.2 (1 : ℂ) = c := fun c => by
    conv_rhs => rw [Matrix.matrix_eq_sum_single c]
    rw [Fintype.sum_prod_type]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  have e2 : ∀ c : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      ∑ p : Fin T.rank × Fin S.rank, c p.1 p.2 • unitMap (A.onb τ) (B.onb τ) p.1 p.2 = B.onb τ * c * (A.onb τ)⁻¹ :=
    fun c => by
      conv_rhs => rw [← e c, Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, unitMap]
  rw [e2]
  simp only [Fr.onb, Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hb, Matrix.one_mul]

theorem exists_aPlus_ptF (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {S T : HSp D} (A : Fr S) (B : Fr T)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (Q : PolF D T.rank S.rank) :
    ∃ R, aPlus (heisO ψ S T) θ τ (cplxO (A.cart τ) (B.cart τ)) z (ptF ψ θ A B f Q) = ptF ψ θ A B f R := by
  have hg := ptF_theta hψ hθ A B hf Q
  refine ⟨∑ p : Fin T.rank × Fin S.rank, (if decide (B.ε τ p.1 = A.ε τ p.2) then (B.fr τ * z * A.onb τ) p.1 p.2 else
    starRingEnd ℂ ((B.fr τ * z * A.onb τ) p.1 p.2)) • (MvPolynomial.X (τ, p.1, p.2) * Q), ?_⟩
  conv_lhs => rw [eq_sum_unitMap A B τ z]
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  conv_rhs => unfold ptF
  rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ _ _ hg _ _ (GlobalTheory.CompactFockAction.Jm_single A B τ p.1 p.2), map_smul]
  congr 1
  exact (ptF_X_mul hψ hθ A B hf Q (τ, p.1, p.2)).symm

section Box

variable {S X V H : HSp D} (o : OrthDec X V H) (A : Fr S) (BX : Fr X) (BV : Fr V) (BH : Fr H)

theorem aPlus_boxT (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (hV : o.qA.map (tauE D τ) * BX.cart τ = BV.cart τ * o.qA.map (tauE D τ))
    (hH : o.qB.map (tauE D τ) * BX.cart τ = BH.cart τ * o.qB.map (tauE D τ))
    (z : Matrix (Fin X.rank) (Fin S.rank) ℂ) {f : WO S V → ℂ} {g : WO S H → ℂ} (hf : IsThetaFunO ψ S V f)
    (hg : IsThetaFunO ψ S H g) :
    aPlus (heisO ψ S X) θ τ (cplxO (A.cart τ) (BX.cart τ)) z (o.boxT S f g) =
      o.boxT S (aPlus (heisO ψ S V) θ τ (cplxO (A.cart τ) (BV.cart τ)) (o.qA.map (tauE D τ) * z) f) g +
        o.boxT S f (aPlus (heisO ψ S H) θ τ (cplxO (A.cart τ) (BH.cart τ)) (o.qB.map (tauE D τ) * z) g) := by
  unfold aPlus crea
  rw [GlobalTheory.Core.Rk.FockBoxT.dRho_boxT o hθ hψ τ _ hf hg, GlobalTheory.Core.Rk.FockBoxT.dRho_boxT o hθ hψ τ _ hf hg,
    GlobalTheory.Core.Rk.FockBoxT.mul_cplxO hV, GlobalTheory.Core.Rk.FockBoxT.mul_cplxO hH]
  funext x
  simp only [OrthDec.boxT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem isVacF_boxT (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (hV : ∀ τ, o.qA.map (tauE D τ) * BX.cart τ = BV.cart τ * o.qA.map (tauE D τ))
    (hH : ∀ τ, o.qB.map (tauE D τ) * BX.cart τ = BH.cart τ * o.qB.map (tauE D τ))
    {f : WO S V → ℂ} {g : WO S H → ℂ} (hf : IsVacF ψ θ A BV f) (hg : IsVacF ψ θ A BH g) :
    IsVacF ψ θ A BX (o.boxT S f g) := by
  refine ⟨o.isThetaFunO_boxT hf.1 hg.1, fun τ z => ?_⟩
  have h1 := hf.2 τ (o.qA.map (tauE D τ) * z)
  have h2 := hg.2 τ (o.qB.map (tauE D τ) * z)
  unfold annih at h1 h2 ⊢
  rw [GlobalTheory.Core.Rk.FockBoxT.dRho_boxT o hθ hψ τ _ hf.1 hg.1, GlobalTheory.Core.Rk.FockBoxT.dRho_boxT o hθ hψ τ _ hf.1 hg.1,
    GlobalTheory.Core.Rk.FockBoxT.mul_cplxO (hV τ), GlobalTheory.Core.Rk.FockBoxT.mul_cplxO (hH τ)]
  funext x
  have e1 := congrFun h1 (o.resT S x).1
  have e2 := congrFun h2 (o.resT S x).2
  simp only [OrthDec.boxT, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e1 e2 ⊢
  linear_combination g (o.resT S x).2 * e1 + f (o.resT S x).1 * e2

theorem exists_boxT_ptF (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (hV : ∀ τ, o.qA.map (tauE D τ) * BX.cart τ = BV.cart τ * o.qA.map (tauE D τ))
    (hH : ∀ τ, o.qB.map (tauE D τ) * BX.cart τ = BH.cart τ * o.qB.map (tauE D τ))
    {f : WO S V → ℂ} {g : WO S H → ℂ} (hf : IsThetaFunO ψ S V f) (hg : IsThetaFunO ψ S H g)
    (P : PolF D V.rank S.rank) (Q : PolF D H.rank S.rank) :
    ∃ R, o.boxT S (ptF ψ θ A BV f P) (ptF ψ θ A BH g Q) = ptF ψ θ A BX (o.boxT S f g) R := by
  have hfg := o.isThetaFunO_boxT hf hg
  have base : ∃ R, o.boxT S f (ptF ψ θ A BH g Q) = ptF ψ θ A BX (o.boxT S f g) R := by
    induction Q using MvPolynomial.induction_on with
    | C a =>
      refine ⟨MvPolynomial.C a * 1, ?_⟩
      rw [ptF_C, ptF_one, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one]
      funext x
      simp only [OrthDec.boxT, Pi.smul_apply, smul_eq_mul]
      ring
    | add p q hp hq =>
      obtain ⟨R, hR⟩ := hp
      obtain ⟨R', hR'⟩ := hq
      refine ⟨R + R', ?_⟩
      rw [ptF_add, ptF_add, ← hR, ← hR']
      funext x
      simp only [OrthDec.boxT, Pi.add_apply]
      ring
    | mul_X p v hp =>
      obtain ⟨R, hR⟩ := hp
      obtain ⟨R', hR'⟩ := exists_aPlus_ptF hψ hθ A BX hfg v.1
        (o.iB.map (tauE D v.1) * unitMap (A.onb v.1) (BH.onb v.1) v.2.1 v.2.2) R
      refine ⟨R', ?_⟩
      rw [← hR', ← hR, aPlus_boxT o A BX BV BH hψ hθ v.1 (hV _) (hH _) _ hf (ptF_theta hψ hθ A BH hg p),
        ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, o.qA_iB, o.qB_iB,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul,
        GlobalTheory.FockSubst.aPlus_dir_zero hψ hθ _ _ _ hf, mul_comm p, ptF_X_mul hψ hθ A BH hg]
      funext x
      simp only [OrthDec.boxT, Pi.add_apply, Pi.zero_apply, zero_mul, zero_add]
  induction P using MvPolynomial.induction_on with
  | C a =>
    obtain ⟨R, hR⟩ := base
    refine ⟨MvPolynomial.C a * R, ?_⟩
    rw [ptF_C, ← hR, ← mul_one (MvPolynomial.C a), ptF_C, ptF_one]
    funext x
    simp only [OrthDec.boxT, Pi.smul_apply, smul_eq_mul]
    ring
  | add p q hp hq =>
    obtain ⟨R, hR⟩ := hp
    obtain ⟨R', hR'⟩ := hq
    refine ⟨R + R', ?_⟩
    rw [ptF_add, ptF_add, ← hR, ← hR']
    funext x
    simp only [OrthDec.boxT, Pi.add_apply]
    ring
  | mul_X p v hp =>
    obtain ⟨R, hR⟩ := hp
    obtain ⟨R', hR'⟩ := exists_aPlus_ptF hψ hθ A BX hfg v.1
      (o.iA.map (tauE D v.1) * unitMap (A.onb v.1) (BV.onb v.1) v.2.1 v.2.2) R
    have hQ := ptF_theta hψ hθ A BH hg Q
    refine ⟨R', ?_⟩
    rw [← hR', ← hR, aPlus_boxT o A BX BV BH hψ hθ v.1 (hV _) (hH _) _ (ptF_theta hψ hθ A BV hf p) hQ,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, o.qA_iA, o.qB_iA,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul,
      GlobalTheory.FockSubst.aPlus_dir_zero hψ hθ _ _ _ hQ, mul_comm p, ptF_X_mul hψ hθ A BV hf]
    funext x
    simp only [OrthDec.boxT, Pi.add_apply, Pi.zero_apply, mul_zero, add_zero]

end Box

open GlobalTheory.Doubling in

theorem cart_frSum {V H : HSp D} (A : Fr V) (B : Fr H) (τ : D.what₂.Tau) :
    (GlobalTheory.SquareComm.frSum A B).cart τ = blkMat finSumFinEquiv (A.cart τ) (B.cart τ) := by
  have ha : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hb : IsUnit (B.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
  have e' : Formalism.REAL.Jm (Fin.append (A.ε τ) (B.ε τ)) =
      blkMat finSumFinEquiv (Formalism.REAL.Jm (A.ε τ)) (Formalism.REAL.Jm (B.ε τ)) := by
    refine submatrix_inj finSumFinEquiv ?_
    rw [submatrix_blkMat]
    ext (a | a) (b | b) <;> simp [Formalism.REAL.Jm, Matrix.diagonal_apply, Fin.ext_iff] <;> omega
  have e : (blkMat finSumFinEquiv (A.fr τ) (B.fr τ))⁻¹ = blkMat finSumFinEquiv (A.fr τ)⁻¹ (B.fr τ)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [blkMat_mul, Matrix.nonsing_inv_mul _ ha, Matrix.nonsing_inv_mul _ hb]
    simp [GlobalTheory.Doubling.blkMat]
  show (blkMat finSumFinEquiv (A.fr τ) (B.fr τ))⁻¹ * Formalism.REAL.Jm (Fin.append (A.ε τ) (B.ε τ)) *
    blkMat finSumFinEquiv (A.fr τ) (B.fr τ) = _
  rw [e, e', blkMat_mul, blkMat_mul]
  rfl

theorem qA_cart_frSum {V H : HSp D} (A : Fr V) (B : Fr H) (τ : D.what₂.Tau) :
    (GlobalTheory.BiTransfer.sumDec V H).qA.map (tauE D τ) * (GlobalTheory.SquareComm.frSum A B).cart τ =
      A.cart τ * (GlobalTheory.BiTransfer.sumDec V H).qA.map (tauE D τ) := by
  have e : (GlobalTheory.BiTransfer.sumDec V H).qA.map (tauE D τ) =
      (fromCols (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) 0).submatrix id finSumFinEquiv.symm := by
    rw [GlobalTheory.SeesawSumTarget.qA_sumDec]
    ext i j
    simp only [Matrix.map_apply, submatrix_apply, id]
    rcases finSumFinEquiv.symm j with k | k <;> simp [Matrix.one_apply, apply_ite (tauE D τ)]
  rw [e, cart_frSum, GlobalTheory.Doubling.blkMat, Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks]
  ext i j
  simp only [Matrix.mul_apply, submatrix_apply, id]
  rcases finSumFinEquiv.symm j with k | k <;> simp [Matrix.one_apply]

theorem qB_cart_frSum {V H : HSp D} (A : Fr V) (B : Fr H) (τ : D.what₂.Tau) :
    (GlobalTheory.BiTransfer.sumDec V H).qB.map (tauE D τ) * (GlobalTheory.SquareComm.frSum A B).cart τ =
      B.cart τ * (GlobalTheory.BiTransfer.sumDec V H).qB.map (tauE D τ) := by
  have e : (GlobalTheory.BiTransfer.sumDec V H).qB.map (tauE D τ) =
      (fromCols (0 : Matrix (Fin H.rank) (Fin V.rank) ℂ) 1).submatrix id finSumFinEquiv.symm := by
    rw [GlobalTheory.SeesawSumTarget.qB_sumDec]
    ext i j
    simp only [Matrix.map_apply, submatrix_apply, id]
    rcases finSumFinEquiv.symm j with k | k <;> simp [Matrix.one_apply, apply_ite (tauE D τ)]
  rw [e, cart_frSum, GlobalTheory.Doubling.blkMat, Matrix.submatrix_mul_equiv, fromCols_mul_fromBlocks]
  ext i j
  simp only [Matrix.mul_apply, submatrix_apply, id]
  rcases finSumFinEquiv.symm j with k | k <;> simp [Matrix.one_apply]

theorem fockVector_product_mem_algebraicVectors (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (ε : Bool) {S V H : HSp D} (A : Fr S) (BV : Fr V)
    (BH : Fr H) {f : WO (GlobalTheory.Grid.sgn ε S) V → ℂ} {g : WO (GlobalTheory.Grid.sgn ε S) H → ℂ} (hf : IsVacF ψ θ (GlobalTheory.SquareComm.frSgn ε A) BV f)
    (hg : IsVacF ψ θ (GlobalTheory.SquareComm.frSgn ε A) BH g) (P : PolF D V.rank S.rank) (Q : PolF D H.rank S.rank) :
    box2 (S := GlobalTheory.Grid.sgn ε S) (A := V) (B := H) (ptF ψ θ (GlobalTheory.SquareComm.frSgn ε A) BV f P) (ptF ψ θ (GlobalTheory.SquareComm.frSgn ε A) BH g Q) ∈
      GlobalTheory.SquareComm.algF ψ θ ε A (GlobalTheory.SquareComm.frSum BV BH) := by
  obtain ⟨R, hR⟩ := exists_boxT_ptF (GlobalTheory.BiTransfer.sumDec V H) (GlobalTheory.SquareComm.frSgn ε A) (GlobalTheory.SquareComm.frSum BV BH) BV BH
    hψ hθ (qA_cart_frSum BV BH) (qB_cart_frSum BV BH) hf.1 hg.1 P Q
  have hv := isVacF_boxT (GlobalTheory.BiTransfer.sumDec V H) (GlobalTheory.SquareComm.frSgn ε A) (GlobalTheory.SquareComm.frSum BV BH) BV BH
    hψ hθ (qA_cart_frSum BV BH) (qB_cart_frSum BV BH) hf hg
  rw [GlobalTheory.SeesawSumTarget.boxT_sumDec] at hR
  exact Submodule.subset_span ⟨_, R, hv, hR⟩

theorem isVacF_cj (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {S T : HSp D} (A : Fr S) (B : Fr T) {f : WO S T → ℂ}
    (hf : IsVacF ψ θ A B f) : IsVacF ψ θ (GlobalTheory.PairLift.frSgn true A) B (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) := by
  have ht : IsThetaFunO ψ (GlobalTheory.Grid.neg S) T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) := GlobalTheory.CjNeg.theta_negS hψ hf.1
  refine ⟨ht, fun τ z => ?_⟩
  have h0 := hf.2 τ z
  have e : ∀ w, dRho (heisO ψ S T) θ τ w f = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (dRho (heisO ψ (GlobalTheory.Grid.neg S) T) θ τ w (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f)) := fun w => by
    rw [← GlobalTheory.FockConjNeg.dRho_cj_neg hψ, GlobalTheory.CjNeg.cj_id_cj_id]
  unfold annih at h0 ⊢
  rw [e, e] at h0
  rw [GlobalTheory.PairLift.cart_frSgn, show GlobalTheory.Grid.sgnM true (A.cart τ) = -A.cart τ from rfl, GlobalTheory.FockConjNeg.cplxO_neg_left,
    dRho_neg' hψ hθ ht]
  funext x
  have h2 := congrArg (starRingEnd ℂ) (congrFun h0 x)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply, map_add, map_mul,
    Complex.conj_I, Complex.conj_conj, map_zero] at h2 ⊢
  linear_combination h2

theorem adj_ptF (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {S T : HSp D} (A : Fr S) (B : Fr T) {g : WO T S → ℂ}
    (hg : IsVacF ψ θ B A g) :
    IsVacF ψ θ (GlobalTheory.SquareComm.frSgn true A) B (fun y => g (adjM S T y)) ∧ ∀ P, ∃ R,
      (fun y => ptF ψ θ B A g P (adjM S T y)) = ptF ψ θ (GlobalTheory.SquareComm.frSgn true A) B (fun y => g (adjM S T y)) R := by
  obtain ⟨j, -, hj⟩ := fock_dag D ψ θ hψ hθ T S B A
  obtain ⟨hv, hP⟩ := hj g hg
  have e : ∀ φ : WO T S → ℂ, (fun y => φ (adjM S T y)) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.PairLift.dag T S φ) := fun φ => by
    funext y
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, GlobalTheory.PairLift.dag, Complex.conj_conj]
    rfl
  have hc := isVacF_cj hψ hθ A B hv
  rw [e]
  refine ⟨hc, fun P => ⟨MvPolynomial.map (starRingEnd ℂ) (j P), ?_⟩⟩
  have h := GlobalTheory.FockConjNeg.cj_ptF_neg hψ hθ A B hc.1 (MvPolynomial.map (starRingEnd ℂ) (j P))
  rw [GlobalTheory.CjNeg.cj_id_cj_id, MvPolynomial.map_map, show (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ from
    RingHom.ext fun z => Complex.conj_conj z, MvPolynomial.map_id, hP] at h
  rw [e, ← h, GlobalTheory.CjNeg.cj_id_cj_id]
  rfl

theorem datumA_mem_algF : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (A : Fr (G.V (.grid (↑i + 1) (↑j + 1)))) (AV : Fr (G.V (.grid ↑i (↑j + 1)))) (AV₁ : Fr (G.V (.grid (↑i + 1) ↑j))),
    GlobalTheory.SquareDict.IsGridFr W _ A → GlobalTheory.SquareDict.IsGridFr W _ AV → GlobalTheory.SquareDict.IsGridFr W _ AV₁ →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
      GlobalTheory.SquareDict.datumA W Θ ∈ GlobalTheory.SquareComm.algF W.ψ W.θ true A (GlobalTheory.SquareComm.frSum AV AV₁) := by
  intro D T L sc G μ₀ _hL W t i j A AV AV₁ hA hV hV₁ B ρ Θ Θ' hM
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, hF, rfl, -⟩ := hM
  obtain ⟨e, he, -, φ₁, φ₂, hφ, -⟩ := hF
  refine Submodule.sum_mem _ fun d hd => Submodule.smul_mem _ _ ?_
  unfold tensT at hd
  obtain ⟨P, -, hd⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d', hd', hd⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  have hd := Finsupp.support_single_subset hd
  rw [Finset.mem_singleton] at hd
  subst hd
  obtain ⟨h₁, h₂⟩ := hφ d' hd'
  have v₁ := (ρ.vX_is i (j + 1) i.2 j.2).2
  have v₂ := (ρ.vT_is t (i + 1) j i.2 j.2).2
  have t₁ := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h₁.2 v₁.2
  have t₂ := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h₂.2 v₂.2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have cA : (GlobalTheory.SquareComm.frSgn true A).cart = fun τ => -W.cart (.grid (↑i + 1) (↑j + 1)) τ := funext fun τ =>
    (GlobalTheory.PairLift.cart_frSgn true A τ).trans (congrArg Neg.neg (hA τ).2)
  have cA' : A.cart = W.cart _ := funext fun τ => (hA τ).2
  have cV : AV.cart = W.cart _ := funext fun τ => (hV τ).2
  have cV₁ : AV₁.cart = W.cart _ := funext fun τ => (hV₁ τ).2
  have oA : A.onb = W.onb _ := funext fun τ => (hA τ).1
  have oV : AV.onb = W.onb _ := funext fun τ => (hV τ).1
  have oV₁ : AV₁.onb = W.onb _ := funext fun τ => (hV₁ τ).1
  have w₁ : IsVacF W.ψ W.θ (GlobalTheory.SquareComm.frSgn true A) AV d'.1.2 := ⟨t₁, fun τ => by
    rw [cA, cV]
    exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq h₁.2 v₁.theta t₁
      (v₁.fock τ)⟩
  have w₂ : IsVacF W.ψ W.θ AV₁ A d'.2 := ⟨t₂, fun τ => by
    rw [cA', cV₁]
    exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq h₂.2 v₂.theta t₂
      (v₂.fock τ)⟩
  have e₁ : W.fock (.chi i (j + 1)) d'.1.2 P.1.2 = ptF W.ψ W.θ (GlobalTheory.SquareComm.frSgn true A) AV d'.1.2 P.1.2 := by
    unfold ptF
    rw [cA, cV, oV, show (GlobalTheory.SquareComm.frSgn true A).onb = W.onb _ from oA]
    rfl
  have e₂ : W.fock (.mu t (i + 1) j) d'.2 P.2 = ptF W.ψ W.θ AV₁ A d'.2 P.2 := by
    unfold ptF
    rw [cA', cV₁, oA, oV₁]
    rfl
  obtain ⟨w₃, hP⟩ := adj_ptF W.ψ_std W.θ_is A AV₁ w₂
  obtain ⟨R, hR⟩ := hP P.2
  have key := fockVector_product_mem_algebraicVectors W.ψ_std W.θ_is true A AV AV₁ w₁ w₃ P.1.2 R
  rw [← hR, ← e₁, ← e₂] at key
  exact key

end GlobalTheory.SquareAlg

end
