import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hTens_eq_trace {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  calc _ = ∑ j, ∑ i, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, ∑ l, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ l, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ k, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (HMul.hMul (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ) (T.gram.map (incA D)))
      (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by
  simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ c', ∑ d, incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a
      = ∑ b, ∑ d, ∑ c', incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c', incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem trace_mul_submatrix {A : Type} [CommRing A] {m d : ℕ} (e : Fin m ≃ Fin d) (P : Matrix (Fin d) (Fin d) A)
    (K : Matrix (Fin m) (Fin m) A) : (P * K.submatrix e.symm e.symm).trace = (P.submatrix e e * K).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.submatrix_apply]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp e]
  simp

theorem cA_inc (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, sigR, CMData.sig, inclR]; rfl

theorem gram_herm (S : HSp D) : S.gramᴴ = S.gram :=
  Matrix.ext fun _ _ => S.herm.eq _ _

theorem gram_map_herm (S : HSp D) : ((S.gram.map (incA D)).map (cA D))ᵀ = S.gram.map (incA D) := by
  refine Matrix.ext fun i j => ?_
  exact (cA_inc _).trans (congrArg (incA D) (congrFun (congrFun (gram_herm S) i) j))

theorem gram_inv_mul (T : HSp D) : T.gram⁻¹.map (incA D) * T.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne _))]; simp

theorem hTens_eq_trace' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (c' : A →+* A)
    (hc : ∀ a, c a = c' a) {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A)
    (x y : Matrix α β A) : GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c' * JBᵀ).trace := by
  rw [hTens_eq_trace]
  congr 3
  ext i j
  exact hc _

end GlobalTheory.SquareAgree.HeisCov

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem sgn_gram (ε : Bool) (S : HSp D) : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
  cases ε <;> ext i j <;> simp [Formalism.BasicNotions.HSpace.gram]

set_option maxHeartbeats 1000000 in

theorem symp_eq (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (JV : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (JW : Matrix (Fin d) (Fin d) D.host.E)
    (hJ : JV = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : JW = D.host.xi0 • reindex e e X.gramᵀ)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) → WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    (u w : Matrix (Fin S.rank) (Fin d) (AE D)) :
    GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JV)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JW) u w = symplO (sgn ε S) X (cS u) (cS w) := by
  have hGs : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram) = (sgn ε S).gram.map (incA D) := by
    rw [← sgn_gram]; rfl
  have hJA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JV = -(sgn ε S).gram.map (incA D) := by
    rw [hJ, sgn_gram]
    cases ε <;> ext i j <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hJB : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JW)ᵀ =
      incA D D.host.xi0 • (X.gram.map (incA D)).submatrix e.symm e.symm := by
    rw [hJW]; ext i j; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  unfold GlobalTheory.WeilM.symp symplO
  rw [hTens_eq_trace' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (cA D) (fun _ => rfl), hO_eq_trace, hcS, hcS, hGs, hJA, hJB]
  have hinv := gram_inv_mul (sgn ε S)
  have hh := gram_map_herm (sgn ε S)
  have hW : ((wᵀ.submatrix e id).map (cA D))ᵀ = (w.map (cA D)).submatrix id e := rfl
  congr 1
  rw [Matrix.map_mul, Matrix.transpose_mul, hh, ← Matrix.mul_assoc _ _ (((wᵀ.submatrix e id).map (cA D))ᵀ), hinv,
    Matrix.one_mul, hW]
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.trace_neg,
    smul_eq_mul, trace_mul_submatrix, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]
  rw [Matrix.mul_assoc (uᵀ.submatrix e id * _), Matrix.trace_mul_comm (uᵀ.submatrix e id * _)]
  ring

end GlobalTheory.SquareAgree.HeisCov

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem invOf_two' {D : D7} : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul, mul_one_div_cancel two_ne_zero, map_one]

theorem isDatum_rho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ), IsDatum M ψ cS Φ f →
        ∀ w : Matrix (Fin S.rank) (Fin d) (AE D), IsDatum M ψ cS (M.co.rho ψ w Φ) (heisO ψ (sgn ε S) X (cS w) f) := by
  intro D ψ θ _ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW _ _ _ M _ cS hcS Φ f hD w
  refine ⟨?_, fun u => ?_⟩
  · have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ ▸ hBs.std
    exact GlobalTheory.HeisSchA.rho_mem_schA M ψ hstd w Φ hD.1
  · rw [GlobalTheory.BigDat.rho_rho M.co ψ u w Φ, GlobalTheory.WeilM.thetaSum_smul, hD.2 (u + w)]
    unfold heisO symplOH
    rw [symp_eq ε S X e Vs.J Ws.J hJ hJW cS hcS u w, map_add, invOf_two']

end GlobalTheory.SquareAgree.HeisCov
