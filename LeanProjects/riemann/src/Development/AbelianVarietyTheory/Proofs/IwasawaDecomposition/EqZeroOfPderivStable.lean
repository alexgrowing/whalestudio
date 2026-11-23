import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealPlaceSymplecticFormPositiveComplexStru
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDirectionalDerivFormulaAndSmooth
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeCommutatorRelation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField Matrix Complex
open scoped Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockIndep

section Generic

variable {ι X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem foldr_mem (hA : ∀ i f, P f → P (A i f)) {f : X → ℂ} (hf : P f) (l : List ι) :
    P (l.foldr (fun i g => A i g) f) := by
  induction l with
  | nil => exact hf
  | cons i l ih => exact hA i _ ih

theorem foldr_perm (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    {f : X → ℂ} (hf : P f) {l l' : List ι} (h : l.Perm l') :
    l.foldr (fun i g => A i g) f = l'.foldr (fun i g => A i g) f := by
  induction h with
  | nil => rfl
  | cons i _ ih => simp only [List.foldr_cons, ih]
  | swap i j l => exact hc _ _ _ (foldr_mem hA hf l)
  | trans _ _ ih ih' => exact ih.trans ih'

theorem pure_monomial (f : X → ℂ) (k : ι →₀ ℕ) (c : ℂ) :
    pureTensorL A f (MvPolynomial.monomial k c) = c • opPow A k f := by
  have h : MvPolynomial.monomial k c = c • MvPolynomial.basisMonomials ι ℂ k := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, pureTensorL, Module.Basis.constr_basis]

theorem pure_one (f : X → ℂ) : pureTensorL A f 1 = f := by
  rw [MvPolynomial.one_def, pure_monomial, one_smul]
  simp [opPow]

theorem pure_mem (hadd : ∀ f f', P f → P f' → P (f + f')) (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f)) {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) : P (pureTensorL A f Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c => rw [pure_monomial]; exact hsm _ _ (foldr_mem hA hf _)
  | add p q hp hq => rw [map_add]; exact hadd _ _ hp hq

theorem pure_X_mul (hadd : ∀ f f', P f → P f' → P (f + f')) (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f)
    {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) (v : ι) :
    pureTensorL A f (MvPolynomial.X v * Q) = A v (pureTensorL A f Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, pure_monomial, pure_monomial,
      Asm _ _ (opPow A k f) (foldr_mem hA hf _)]
    congr 1
    refine foldr_perm hA hc hf (l' := v :: (Finsupp.toMultiset k).toList) ?_
    rw [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.coe_toList, Multiset.coe_toList, map_add,
      Finsupp.toMultiset_single, one_smul, Multiset.singleton_add]
  | add p q hp hq =>
    rw [mul_add, map_add, map_add, hp, hq, Aadd _ _ _ (pure_mem hadd hsm hA hf _) (pure_mem hadd hsm hA hf _)]

theorem eq_zero_of_pderiv_stable {K : MvPolynomial ι ℂ → Prop} (hd : ∀ Q i, K Q → K (MvPolynomial.pderiv i Q))
    (hc : ∀ a, K (MvPolynomial.C a) → a = 0) (Q : MvPolynomial ι ℂ) (hQ : K Q) : Q = 0 := by
  have key : ∀ n : ℕ, ∀ Q : MvPolynomial ι ℂ, K Q → (∀ m : ι →₀ ℕ, n ≤ m.degree → Q.coeff m = 0) → Q = 0 := by
    intro n
    induction n with
    | zero => exact fun Q _ h => MvPolynomial.ext _ _ fun m => h m (Nat.zero_le _)
    | succ n ih =>
      intro Q hQ h
      have h1 : ∀ i, MvPolynomial.pderiv i Q = 0 := fun i => ih _ (hd Q i hQ) fun m hm => by
        rw [MvPolynomial.coeff_pderiv, h _ (by rw [map_add, Finsupp.degree_single]; omega), zero_mul]
      have h2 : Q = MvPolynomial.C (Q.coeff 0) := by
        refine MvPolynomial.ext _ _ fun m => ?_
        rw [MvPolynomial.coeff_C]
        split_ifs with hm
        · rw [hm]
        · obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 (Ne.symm hm)
          have hle : Finsupp.single i 1 ≤ m := by
            rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.2 hi
          have h3 := MvPolynomial.coeff_pderiv (i := i) Q (m - Finsupp.single i 1)
          rw [h1, tsub_add_cancel_of_le hle, MvPolynomial.coeff_zero] at h3
          exact (mul_eq_zero.1 h3.symm).resolve_right (Nat.cast_add_one_ne_zero _)
      rw [h2] at hQ ⊢
      rw [hc _ hQ, map_zero]
  refine key (Q.totalDegree + 1) Q hQ fun m hm => ?_
  refine MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_
  exact hm

theorem pure_injective {B : ι → (X → ℂ) → (X → ℂ)} {c : ι → ℂ}
    (hadd : ∀ f f', P f → P f' → P (f + f')) (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f)) (hB : ∀ i f, P f → P (B i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f)
    (Badd : ∀ i f f', P f → P f' → B i (f + f') = B i f + B i f')
    (Bsm : ∀ i (a : ℂ) f, P f → B i (a • f) = a • B i f)
    (hBA : ∀ i j f, P f → B i (A j f) = A j (B i f) + (if i = j then c i else 0) • f) (hc0 : ∀ i, c i ≠ 0)
    {f : X → ℂ} (hf : P f) (f0 : f ≠ 0) (hv : ∀ i, B i f = 0) : Function.Injective (pureTensorL A f) := by
  have hC : ∀ a, pureTensorL A f (MvPolynomial.C a) = a • f := fun a => by
    rw [← mul_one (MvPolynomial.C a), MvPolynomial.C_mul', map_smul, pure_one]
  have hm := pure_mem hadd hsm hA hf
  have hX := pure_X_mul hadd hsm hA hc Aadd Asm hf
  have key : ∀ i Q, B i (pureTensorL A f Q) = c i • pureTensorL A f (MvPolynomial.pderiv i Q) := by
    intro i Q
    induction Q using MvPolynomial.induction_on with
    | C a => rw [hC, Bsm _ _ _ hf, hv, MvPolynomial.pderiv_C, map_zero, smul_zero, smul_zero]
    | add p q hp hq => rw [map_add, Badd _ _ _ (hm _) (hm _), hp, hq, map_add, map_add, smul_add]
    | mul_X p j hp =>
      rw [mul_comm, hX, hBA _ _ _ (hm _), hp, Asm _ _ _ (hm _), MvPolynomial.pderiv_mul, map_add, hX,
        MvPolynomial.pderiv_X, add_comm, smul_add]
      congr 1
      by_cases h : i = j
      · subst h; simp
      · simp [h, Pi.single_apply, Ne.symm h]
  rw [injective_iff_map_eq_zero]
  refine eq_zero_of_pderiv_stable (K := fun Q => pureTensorL A f Q = 0) (fun Q i h => ?_) fun a h => ?_
  · have h1 := key i Q
    have h2 := Bsm i 0 f hf
    rw [zero_smul, zero_smul] at h2
    rw [h, h2] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_left (hc0 i)
  · rw [hC] at h
    exact (smul_eq_zero.1 h).resolve_right f0

end Generic

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem piW_lineAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    piW θ T S (lineAt θ τ z 1) = (Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) := by
  funext τ'
  refine ((isLineAt_lineAt hθ τ z).2.2 1 τ').trans ?_
  rw [Pi.single_apply, Complex.ofReal_one, one_smul]

noncomputable def omDir (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ' : D.what₂.Tau)
    (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℝ :=
  if τ = τ' then 2 * (tauE D τ D.host.xi0 * ((gramAt D S τ)⁻¹ * z'ᴴ * gramAt D T τ * z).trace).re else 0

theorem omO_single (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ' : D.what₂.Tau)
    (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omO S T (Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ)
      (Pi.single τ' z' : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) = omDir S T τ z τ' z' := by
  show ∑ σ, formAt S T σ ((Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) σ)
    ((Pi.single τ' z' : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) σ) = _
  simp only [GlobalTheory.OrientedRealForm.formAt_eq]
  rw [Finset.sum_eq_single τ (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp), omDir, Pi.single_eq_same]
  split_ifs with h
  · subst h; rw [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

section Laws

variable (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
include hψ hθ

theorem dRho_add (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f f' : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') :
    dRho (heisO ψ S T) θ τ z (f + f') = dRho (heisO ψ S T) θ τ z f + dRho (heisO ψ S T) θ τ z f' := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hE : ∀ g, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g =
      FockCompare.hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ z 1)) g := fun g =>
    dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  have hd : ∀ {g}, IsThetaFunO ψ S T g → ∀ w, DifferentiableAt ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 :=
    fun hg w => ((theta_sm h hg w).differentiable (by simp)).differentiableAt
  funext w
  rw [Pi.add_apply, hE, hE, hE, hD_eq_fderiv _ _ _ _ (theta_sm h (theta_add hf hf')),
    hD_eq_fderiv _ _ _ _ (theta_sm h hf), hD_eq_fderiv _ _ _ _ (theta_sm h hf')]
  have e : (fun x : RW T S => (f + f') (w + iotaW σ T S x)) =
      fun x : RW T S => f (w + iotaW σ T S x) + f' (w + iotaW σ T S x) := rfl
  rw [e, fderiv_fun_add (hd hf w) (hd hf' w), ContinuousLinearMap.add_apply, Pi.add_apply]
  ring

theorem dRho_smul (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (a : ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dRho (heisO ψ S T) θ τ z (a • f) = a • dRho (heisO ψ S T) θ τ z f := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hE : ∀ g, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g =
      FockCompare.hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ z 1)) g := fun g =>
    dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  have hd : ∀ {g}, IsThetaFunO ψ S T g → ∀ w, DifferentiableAt ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 :=
    fun hg w => ((theta_sm h hg w).differentiable (by simp)).differentiableAt
  funext w
  rw [Pi.smul_apply, hE, hE, hD_eq_fderiv _ _ _ _ (theta_sm h (theta_smul a hf)), hD_eq_fderiv _ _ _ _ (theta_sm h hf)]
  have e : (fun x : RW T S => (a • f) (w + iotaW σ T S x)) =
      fun x : RW T S => a • f (w + iotaW σ T S x) := rfl
  rw [e, fderiv_fun_const_smul (hd hf w), ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
    smul_eq_mul]
  ring

theorem dRho_comm (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ' : D.what₂.Tau)
    (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    dRho (heisO ψ S T) θ τ z (dRho (heisO ψ S T) θ τ' z' f) =
      (-(2 * π * I) * (omDir S T τ z τ' z' : ℝ)) • f + dRho (heisO ψ S T) θ τ' z' (dRho (heisO ψ S T) θ τ z f) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hE : ∀ τ z g, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g =
      FockCompare.hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ z 1)) g := fun τ z g =>
    dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  have sk : ∀ u v, omO S T v u = -omO S T u v := fun u v => by
    have h1 := omO_self h (S := S) (T := T) (u + v)
    simp only [LinearMap.map_add, LinearMap.add_apply, omO_self h] at h1
    linarith
  apply eq_add_of_sub_eq
  rw [hE, hE, hE, hE, heisenberg_derivative_commutator _ _ _ _ _ (h.pi_iota T S)
    (fun g hg u w => hD_eq_fderiv _ _ _ g hg u w) sk f (theta_sm h hf), piW_lineAt hθ, piW_lineAt hθ, omO_single]

variable (τ : D.what₂.Tau) (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
  (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)

omit hψ hθ in
theorem aPlus_eq (f : WO S T → ℂ) : aPlus (heisO ψ S T) θ τ J z f =
    ((fockScale D τ : ℂ)⁻¹) • (dRho (heisO ψ S T) θ τ z f + (-I) • dRho (heisO ψ S T) θ τ (J z) f) := by
  rw [aPlus, crea, neg_smul, sub_eq_add_neg]

theorem aPlus_theta {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (aPlus (heisO ψ S T) θ τ J z f) := by
  rw [aPlus_eq]
  exact theta_smul _ (theta_add (theta_dRho hθ hψ τ z hf) (theta_smul _ (theta_dRho hθ hψ τ (J z) hf)))

theorem aPlus_add {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') :
    aPlus (heisO ψ S T) θ τ J z (f + f') = aPlus (heisO ψ S T) θ τ J z f + aPlus (heisO ψ S T) θ τ J z f' := by
  simp only [aPlus_eq, fun z => dRho_add hψ hθ τ z hf hf']
  module

theorem aPlus_smul (a : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ J z (a • f) = a • aPlus (heisO ψ S T) θ τ J z f := by
  simp only [aPlus_eq, fun z => dRho_smul hψ hθ τ z a hf]
  module

theorem annih_theta {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (annih (heisO ψ S T) θ τ J z f) :=
  theta_add (theta_dRho hθ hψ τ z hf) (theta_smul _ (theta_dRho hθ hψ τ (J z) hf))

theorem annih_add {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') :
    annih (heisO ψ S T) θ τ J z (f + f') = annih (heisO ψ S T) θ τ J z f + annih (heisO ψ S T) θ τ J z f' := by
  simp only [annih, fun z => dRho_add hψ hθ τ z hf hf']
  module

theorem annih_smul (a : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    annih (heisO ψ S T) θ τ J z (a • f) = a • annih (heisO ψ S T) θ τ J z f := by
  simp only [annih, fun z => dRho_smul hψ hθ τ z a hf]
  module

variable {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
include hS hT

omit hψ hθ in

theorem omDir_cplx (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omDir S T τ (cplxO (sS τ) (sT τ) z) τ' (cplxO (sS τ') (sT τ') z') = omDir S T τ z τ' z' ∧
    omDir S T τ z τ' (cplxO (sS τ') (sT τ') z') = -omDir S T τ (cplxO (sS τ) (sT τ) z) τ' z' := by
  unfold omDir
  split_ifs with h
  · subst h
    refine ⟨by rw [GlobalTheory.RealSymplForm.tr_J_J (hS τ) (hT τ)], ?_⟩
    rw [← GlobalTheory.RealSymplForm.tr_J_J (hS τ) (hT τ) z, GlobalTheory.RealSymplForm.cplxO_cplxO (hS τ).1 (hT τ).1]
    simp
    ring
  · simp

theorem aPlus_comm' (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z (aPlus (heisO ψ S T) θ τ' (cplxO (sS τ') (sT τ')) z' f) =
    aPlus (heisO ψ S T) θ τ' (cplxO (sS τ') (sT τ')) z' (aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z f) := by
  have ht := fun τ z => theta_dRho hθ hψ τ z hf
  have hc := fun τ z τ' z' => dRho_comm hψ hθ τ z τ' z' hf
  obtain ⟨h1, h2⟩ := omDir_cplx τ z hS hT τ' z'
  rw [aPlus_eq τ' _ z' f, aPlus_eq τ _ z f, aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)), aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)),
    aPlus_smul hψ hθ _ _ _ _ (ht _ _), aPlus_smul hψ hθ _ _ _ _ (ht _ _)]
  simp only [aPlus_eq]
  rw [hc τ z τ' z', hc τ z τ' (cplxO (sS τ') (sT τ') z'), hc τ (cplxO (sS τ) (sT τ) z) τ' z',
    hc τ (cplxO (sS τ) (sT τ) z) τ' (cplxO (sS τ') (sT τ') z')]
  rw [h1, h2]
  match_scalars
  all_goals first | ring1 | (ring_nf; simp only [I_pow_three]; ring1)

theorem annih_aPlus (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z (aPlus (heisO ψ S T) θ τ' (cplxO (sS τ') (sT τ')) z' f) =
    aPlus (heisO ψ S T) θ τ' (cplxO (sS τ') (sT τ')) z' (annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z f) +
      ((fockScale D τ' : ℂ)⁻¹ * (-(4 * π * I) * ((omDir S T τ z τ' z' : ℝ) +
        I * (omDir S T τ (cplxO (sS τ) (sT τ) z) τ' z' : ℝ)))) • f := by
  have ht := fun τ z => theta_dRho hθ hψ τ z hf
  have hc := fun τ z τ' z' => dRho_comm hψ hθ τ z τ' z' hf
  obtain ⟨h1, h2⟩ := omDir_cplx τ z hS hT τ' z'
  rw [aPlus_eq τ' _ z' f, annih_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    annih_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)), annih_smul hψ hθ _ _ _ _ (ht _ _)]
  conv_rhs => rw [annih, aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)), aPlus_smul hψ hθ _ _ _ _ (ht _ _)]
  simp only [aPlus_eq, annih]
  rw [hc τ z τ' z', hc τ z τ' (cplxO (sS τ') (sT τ') z'), hc τ (cplxO (sS τ) (sT τ) z) τ' z',
    hc τ (cplxO (sS τ) (sT τ) z) τ' (cplxO (sS τ') (sT τ') z')]
  rw [h1, h2]
  match_scalars
  all_goals first | ring1 | (ring_nf; simp only [I_pow_three]; ring1)

end Laws

end GlobalTheory.FockIndep
