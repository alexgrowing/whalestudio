import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeCommutatorRelation
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import ReciprocityTheory.SemistableReduction.AlgebraicIndependentOfDerivations

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe Matrix
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockInj

section Generic

variable {ι X : Type} {A B : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

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

theorem pure_C (f : X → ℂ) (c : ℂ) : pureTensorL A f (MvPolynomial.C c) = c • f := by
  rw [MvPolynomial.C_apply, pure_monomial]
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

theorem injective_of_pderiv {Y : Type} [AddCommGroup Y] [Module ℂ Y] (L : MvPolynomial ι ℂ →ₗ[ℂ] Y)
    (hd : ∀ Q, L Q = 0 → ∀ i, L (MvPolynomial.pderiv i Q) = 0) (hC : ∀ c : ℂ, L (MvPolynomial.C c) = 0 → c = 0) :
    Function.Injective L := by
  rw [injective_iff_map_eq_zero]
  have h0 : ∀ Q : MvPolynomial ι ℂ, Q.totalDegree = 0 → L Q = 0 → Q = 0 := by
    intro Q h hL
    have e := MvPolynomial.totalDegree_eq_zero_iff_eq_C.1 h
    rw [e] at hL
    rw [e, hC _ hL, map_zero]
  intro Q
  induction hn : Q.totalDegree using Nat.strong_induction_on generalizing Q with
  | _ n ih =>
    intro hL
    by_cases h : Q.totalDegree = 0
    · exact h0 Q h hL
    · refine h0 Q (ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.eq_C_of_pderiv_eq_zero Q fun i => ?_) hL
      exact ih _ (hn ▸ ReciprocityTheory.MultiplicativeHeights.DerivationAlgebraicIndependence.totalDegree_pderiv_lt Q i (Nat.pos_of_ne_zero h)) _ rfl (hd Q hL i)

theorem pure_injective (hadd : ∀ f f', P f → P f' → P (f + f')) (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f)
    (Badd : ∀ i f f', P f → P f' → B i (f + f') = B i f + B i f')
    (Bsm : ∀ i (a : ℂ) f, P f → B i (a • f) = a • B i f)
    (c : ι → ℂ) (hc0 : ∀ i, c i ≠ 0)
    (hBA : ∀ i j f, P f → B i (A j f) = A j (B i f) + (if i = j then c i else 0) • f)
    {f : X → ℂ} (hf : P f) (hf0 : f ≠ 0) (hB : ∀ i, B i f = 0) : Function.Injective (pureTensorL A f) := by
  have hm := pure_mem hadd hsm hA hf
  have hX := pure_X_mul hadd hsm hA hc Aadd Asm hf
  have key : ∀ i Q, B i (pureTensorL A f Q) = c i • pureTensorL A f (MvPolynomial.pderiv i Q) := by
    intro i Q
    induction Q using MvPolynomial.induction_on with
    | C a => rw [pure_C, Bsm _ _ _ hf, hB, MvPolynomial.pderiv_C, map_zero, smul_zero, smul_zero]
    | add p q hp hq => rw [map_add, Badd _ _ _ (hm _) (hm _), hp, hq, map_add, map_add, smul_add]
    | mul_X p j hp =>
      rw [mul_comm, hX, hBA _ _ _ (hm _), hp, Asm _ _ _ (hm _), ← hX, MvPolynomial.pderiv_mul, map_add, smul_add,
        add_comm]
      congr 1
      by_cases h : i = j
      · subst h
        rw [if_pos rfl, MvPolynomial.pderiv_X_self, one_mul]
      · rw [if_neg h, MvPolynomial.pderiv_X_of_ne (Ne.symm h), zero_mul, map_zero, zero_smul, smul_zero]
  refine injective_of_pderiv _ (fun Q hQ i => ?_) fun a ha => ?_
  · have h := key i Q
    have h2 := Bsm i 0 f hf
    rw [zero_smul, zero_smul] at h2
    rw [hQ, h2] at h
    exact (smul_eq_zero.1 h.symm).resolve_left (hc0 i)
  · rw [pure_C] at ha
    exact (smul_eq_zero.1 ha).resolve_right hf0

end Generic

section Mat

theorem Jm_mul_Jm {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  cases ε a <;> simp

def sg {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

theorem sum_eq_trace {m n : ℕ} (Pm : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin m) (Fin m) ℂ)
    (x y : Matrix (Fin m) (Fin n) ℂ) :
    ∑ a, ∑ b, ∑ e, ∑ d, Pm a b * starRingEnd ℂ (y e b) * Q e d * x d a = trace (Pm * yᴴ * Q * x) := by
  simp only [trace, diag, Matrix.mul_apply, Finset.sum_mul, conjTranspose_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]

theorem trace_frame {m n : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (F' : Matrix (Fin m) (Fin m) ℂ) (hF : IsUnit F)
    (hF' : IsUnit F') (ε : Fin n → Bool) (ε' : Fin m → Bool) (x y : Matrix (Fin m) (Fin n) ℂ) :
    trace ((Fᴴ * Formalism.REAL.Jm ε * F)⁻¹ * (F'⁻¹ * y * F)ᴴ * (F'ᴴ * Formalism.REAL.Jm ε' * F') * (F'⁻¹ * x * F)) =
      trace (Formalism.REAL.Jm ε * yᴴ * Formalism.REAL.Jm ε' * x) := by
  have hd := (isUnit_iff_isUnit_det F).1 hF
  have hd' := (isUnit_iff_isUnit_det F').1 hF'
  have hH : IsUnit Fᴴ.det := by rw [det_conjTranspose]; exact hd.star
  have hH' : IsUnit F'ᴴ.det := by rw [det_conjTranspose]; exact hd'.star
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (Jm_mul_Jm ε), conjTranspose_mul, conjTranspose_mul,
    conjTranspose_nonsing_inv]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hH, Matrix.nonsing_inv_mul_cancel_left _ _ hH',
    Matrix.mul_nonsing_inv_cancel_left _ _ hd']
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]

theorem trace_single {m n : ℕ} (ε : Fin n → Bool) (ε' : Fin m → Bool) (i k : Fin m) (j l : Fin n) (a b : ℂ) :
    trace (Formalism.REAL.Jm ε * (single k l b)ᴴ * Formalism.REAL.Jm ε' * single i j a) =
      if i = k ∧ j = l then sg ε' i * sg ε j * (a * starRingEnd ℂ b) else 0 := by
  rw [trace_mul_single, Formalism.REAL.Jm, Formalism.REAL.Jm, mul_diagonal, diagonal_mul, conjTranspose_apply, single_apply]
  by_cases h : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := h
    unfold sg
    cases ε j <;> cases ε' i <;> simp [mul_comm]
  · rw [if_neg h, if_neg (c := k = i ∧ l = j) (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]
    simp

theorem Jm_single_Jm {m n : ℕ} (ε : Fin n → Bool) (ε' : Fin m → Bool) (i : Fin m) (j : Fin n) :
    Complex.I • (Formalism.REAL.Jm ε' * single i j (1 : ℂ) * Formalism.REAL.Jm ε) = single i j (Complex.I * (sg ε' i * sg ε j)) := by
  ext a b
  rw [Matrix.smul_apply, Formalism.REAL.Jm, Formalism.REAL.Jm, mul_diagonal, diagonal_mul, single_apply, single_apply]
  split_ifs with h1 h2 h3 <;> simp_all [sg]

end Mat

section Heis

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem pi_lineAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    piW θ T S (lineAt θ τ z 1) = (Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) := by
  funext τ'
  refine ((isLineAt_lineAt hθ τ z).2.2 1 τ').trans ?_
  rw [Pi.single_apply, Complex.ofReal_one, one_smul]

theorem omO_single (τ τ' : D.what₂.Tau) (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omO S T (Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ)
      (Pi.single τ' z' : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) = if τ = τ' then formAt S T τ z z' else 0 := by
  show ∑ ρ, formAt S T ρ ((Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) ρ)
    ((Pi.single τ' z' : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) ρ) = _
  rw [Finset.sum_eq_single τ (fun ρ _ hρ => by rw [Pi.single_eq_of_ne hρ]; simp [formAt]) (by simp), Pi.single_eq_same]
  split_ifs with h
  · subst h
    rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h]
    simp [formAt]

theorem dRho_laws (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    (∀ f', IsThetaFunO ψ S T f' → Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (f + f') =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f + Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f') ∧
    (∀ a : ℂ, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (a • f) = a • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) ∧
    ∀ (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' z' f) =
        Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' z' (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) +
        (-(2 * Real.pi * Complex.I) * ((if τ = τ' then formAt S T τ z z' else 0 : ℝ) : ℂ)) • f := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hE : ∀ τ z g, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g =
      FockCompare.hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ z 1)) g := fun τ z g =>
    dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  have hs := theta_sm h hf
  have hd : ∀ {g}, IsThetaFunO ψ S T g → ∀ w, DifferentiableAt ℝ (fun x : RW T S => g (w + iotaW σ T S x)) 0 :=
    fun hg w => ((theta_sm h hg w).differentiable (by simp)).differentiableAt
  refine ⟨fun f' hf' => ?_, fun a => ?_, fun τ' z' => ?_⟩
  · funext w
    rw [Pi.add_apply, hE, hE, hE, hD_eq_fderiv _ _ _ _ (theta_sm h (theta_add hf hf')), hD_eq_fderiv _ _ _ _ hs,
      hD_eq_fderiv _ _ _ _ (theta_sm h hf')]
    have e : (fun x : RW T S => (f + f') (w + iotaW σ T S x)) =
        fun x : RW T S => f (w + iotaW σ T S x) + f' (w + iotaW σ T S x) := rfl
    rw [e, fderiv_fun_add (hd hf w) (hd hf' w), ContinuousLinearMap.add_apply, Pi.add_apply]
    ring
  · funext w
    rw [Pi.smul_apply, hE, hE, hD_eq_fderiv _ _ _ _ (theta_sm h (theta_smul a hf)), hD_eq_fderiv _ _ _ _ hs]
    have e : (fun x : RW T S => (a • f) (w + iotaW σ T S x)) =
        fun x : RW T S => a • f (w + iotaW σ T S x) := rfl
    rw [e, fderiv_fun_const_smul (hd hf w), ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    ring
  · have sk : ∀ u v, omO S T v u = -omO S T u v := fun u v => by
      have h1 := omO_self h (S := S) (T := T) (u + v)
      simp only [LinearMap.map_add, LinearMap.add_apply, omO_self h] at h1
      linarith
    refine eq_add_of_sub_eq' ?_
    rw [hE, hE, hE, hE, heisenberg_derivative_commutator _ _ _ _ _ (h.pi_iota T S)
      (fun g hg u w => hD_eq_fderiv _ _ _ g hg u w) sk f hs, pi_lineAt hθ, pi_lineAt hθ, omO_single]

def comb (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (τ : D.what₂.Tau) (α : ℂ)
    (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) : WO S T → ℂ :=
  Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f + α • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z' f

theorem comb_theta (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (α : ℂ)
    (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    IsThetaFunO ψ S T (comb ψ θ S T τ α z z' f) :=
  theta_add (theta_dRho hθ hψ τ z hf) (theta_smul α (theta_dRho hθ hψ τ z' hf))

theorem comb_add (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (α : ℂ)
    (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hf' : IsThetaFunO ψ S T f') :
    comb ψ θ S T τ α z z' (f + f') = comb ψ θ S T τ α z z' f + comb ψ θ S T τ α z z' f' := by
  simp only [comb, fun z => (dRho_laws hψ hθ hf τ z).1 f' hf']
  module

theorem comb_smul (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (α : ℂ)
    (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) (a : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    comb ψ θ S T τ α z z' (a • f) = a • comb ψ θ S T τ α z z' f := by
  simp only [comb, fun z => (dRho_laws hψ hθ hf τ z).2.1 a]
  module

theorem comb_comm (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (α β : ℂ)
    (x x' y y' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    comb ψ θ S T τ α x x' (comb ψ θ S T τ' β y y' f) = comb ψ θ S T τ' β y y' (comb ψ θ S T τ α x x' f) +
      (if τ = τ' then -(2 * Real.pi * Complex.I) * ((formAt S T τ x y : ℝ) + β * (formAt S T τ x y' : ℝ) +
        α * (formAt S T τ x' y : ℝ) + α * β * (formAt S T τ x' y' : ℝ)) else 0) • f := by
  have ht := fun τ z => theta_dRho hθ hψ τ z hf
  have hc := fun τ z => (dRho_laws hψ hθ hf τ z).2.2
  rw [comb.eq_1 ψ θ S T τ' β y y' f, comb.eq_1 ψ θ S T τ α x x' f,
    comb_add hψ hθ _ _ _ _ (ht _ _) (theta_smul _ (ht _ _)), comb_add hψ hθ _ _ _ _ (ht _ _) (theta_smul _ (ht _ _)),
    comb_smul hψ hθ _ _ _ _ _ (ht _ _), comb_smul hψ hθ _ _ _ _ _ (ht _ _)]
  simp only [comb]
  rw [hc τ x τ' y, hc τ x τ' y', hc τ x' τ' y, hc τ x' τ' y']
  split_ifs
  · module
  · simp only [Complex.ofReal_zero, mul_zero, zero_smul, add_zero]
    module

variable {P P' : D.what₂.Tau → SPar} (M : DSModel S P) (M' : DSModel T P')

def uv (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank) (a : ℂ) : Matrix (Fin T.rank) (Fin S.rank) ℂ :=
  (M'.fr τ)⁻¹ * single i j a * M.fr τ

theorem unitMap_eq (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank) :
    unitMap (onb M τ) (onb M' τ) i j = uv M M' τ i j 1 := by
  rw [unitMap, onb, onb, uv, Matrix.nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (M.fr_unit τ))]

theorem cplxO_uv (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank) :
    cplxO (cart M τ) (cart M' τ) (uv M M' τ i j 1) = uv M M' τ i j (Complex.I * (sg (M'.ε τ) i * sg (M.ε τ) j)) := by
  have hd := (isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hd' := (isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
  rw [cplxO, cart, cart, uv, uv, ← Jm_single_Jm, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hd']

include M in
theorem gramInv_map (τ : D.what₂.Tau) : (S.gram⁻¹).map (tauE D τ) = (gramAt D S τ)⁻¹ := by
  have hu : IsUnit (gramAt D S τ).det := by
    have hd := (isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    rw [← M.fr_gram, det_mul, det_mul, det_conjTranspose]
    exact (hd.star.mul (Matrix.isUnit_det_of_left_inverse (Jm_mul_Jm _))).mul hd
  have hg : IsUnit S.gram.det := by
    rw [isUnit_iff_ne_zero] at hu ⊢
    intro h
    apply hu
    have := (tauE D τ).map_det S.gram
    rw [h, map_zero] at this
    exact this.symm
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [gramAt, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hg]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem formAt_uv (τ : D.what₂.Tau) (i k : Fin T.rank) (j l : Fin S.rank) (a b : ℂ) :
    formAt S T τ (uv M M' τ i j a) (uv M M' τ k l b) = if i = k ∧ j = l then
      2 * (tauE D τ D.host.xi0 * (sg (M'.ε τ) i * sg (M.ε τ) j * (a * starRingEnd ℂ b))).re else 0 := by
  have h := sum_eq_trace ((S.gram⁻¹).map (tauE D τ)) (gramAt D T τ) (uv M M' τ i j a) (uv M M' τ k l b)
  unfold formAt
  erw [h]
  rw [gramInv_map M, ← M.fr_gram, ← M'.fr_gram, uv, uv, trace_frame _ _ (M.fr_unit τ) (M'.fr_unit τ), trace_single]
  split_ifs <;> simp

theorem xi_re (τ : D.what₂.Tau) : (tauE D τ D.host.xi0).re = 0 := by
  have h := congrArg Complex.re (tauE_star τ D.host.xi0)
  rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, Complex.neg_re, Complex.conj_re] at h
  linarith

theorem xi_im (τ : D.what₂.Tau) : (tauE D τ D.host.xi0).im ≠ 0 := fun h =>
  (map_ne_zero (tauE D τ)).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (Complex.ext (xi_re τ) h)

theorem fockScale_ne (τ : D.what₂.Tau) : (fockScale D τ : ℂ) ≠ 0 := by
  have h : 0 < ‖tauE D τ D.host.xi0‖ := norm_pos_iff.2 ((map_ne_zero (tauE D τ)).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  refine Complex.ofReal_ne_zero.2 (ne_of_gt ?_)
  unfold fockScale
  positivity

def op (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α : ℂ) (p : FVar D T.rank S.rank) (f : WO S T → ℂ) : WO S T → ℂ :=
  comb ψ θ S T p.1 α (uv M M' p.1 p.2.1 p.2.2 1)
    (uv M M' p.1 p.2.1 p.2.2 (Complex.I * (sg (M'.ε p.1) p.2.1 * sg (M.ε p.1) p.2.2))) f

theorem op_comm (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (α β : ℂ) (p q : FVar D T.rank S.rank)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    op M M' ψ θ α p (op M M' ψ θ β q f) = op M M' ψ θ β q (op M M' ψ θ α p f) +
      (if p = q then -(2 * Real.pi * Complex.I) * (2 * (tauE D p.1 D.host.xi0).im * (β - α)) else 0) • f := by
  obtain ⟨τ, i, j⟩ := p
  obtain ⟨τ', k, l⟩ := q
  unfold op
  rw [comb_comm hψ hθ _ _ _ _ _ _ _ _ hf]
  congr 2
  dsimp only
  by_cases h : τ = τ'
  · subst h
    rw [if_pos rfl, formAt_uv, formAt_uv, formAt_uv, formAt_uv]
    by_cases h' : i = k ∧ j = l
    · obtain ⟨rfl, rfl⟩ := h'
      simp only [and_self, if_true]
      congr 1
      unfold sg
      cases M'.ε τ i <;> cases M.ε τ j <;> simp [xi_re] <;> ring
    · rw [if_neg h', if_neg h', if_neg h', if_neg h', if_neg (fun e => h' (by simpa using e))]
      simp
  · rw [if_neg h, if_neg (fun e => h (congrArg Prod.fst e))]

theorem aPlusAll_eq (p : FVar D T.rank S.rank) (f : WO S T → ℂ) :
    aPlusAll (heisO ψ S T) θ (fun τ => cplxO (cart M τ) (cart M' τ)) (onb M) (onb M') p f =
      ((fockScale D p.1 : ℂ)⁻¹) • op M M' ψ θ (-Complex.I) p f := by
  rw [aPlusAll, aPlus, crea, unitMap_eq, cplxO_uv, op, comb, neg_smul, sub_eq_add_neg]

end Heis

theorem ptOf_injective : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → IsVacVec ψ θ M M' f → Function.Injective (ptOf ψ θ M M' f) := by
  intro D V W S S' ψ θ M M' f hψ hθ hf
  have ot : ∀ α p {g}, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (op M M' ψ θ α p g) :=
    fun α p g hg => comb_theta hψ hθ _ _ _ _ hg
  have oa : ∀ α p {g g'}, IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' →
      op M M' ψ θ α p (g + g') = op M M' ψ θ α p g + op M M' ψ θ α p g' :=
    fun α p g g' hg hg' => comb_add hψ hθ _ _ _ _ hg hg'
  have os : ∀ α p (a : ℂ) {g}, IsThetaFunO ψ V W g → op M M' ψ θ α p (a • g) = a • op M M' ψ θ α p g :=
    fun α p a g hg => comb_smul hψ hθ _ _ _ _ a hg
  refine pure_injective (P := IsThetaFunO ψ V W) (B := op M M' ψ θ Complex.I)
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun p g hg => ?_)
    (fun p q g hg => ?_) (fun p g g' hg hg' => ?_) (fun p a g hg => ?_) (fun p _ _ => oa _ p) (fun p a _ => os _ p a)
    (fun p => (fockScale D p.1 : ℂ)⁻¹ *
      (-(2 * Real.pi * Complex.I) * (2 * (tauE D p.1 D.host.xi0).im * (-Complex.I - Complex.I))))
    (fun p => ?_) (fun p q g hg => ?_) hf.theta hf.ne fun p => ?_
  · rw [aPlusAll_eq]
    exact GlobalTheory.OrientedHeis.theta_smul _ (ot _ _ hg)
  · simp only [aPlusAll_eq]
    rw [os _ _ _ (ot _ _ hg), os _ _ _ (ot _ _ hg), op_comm M M' hψ hθ _ _ p q hg, sub_self, mul_zero, mul_zero, ite_self,
      zero_smul, add_zero, smul_comm]
  · simp only [aPlusAll_eq, oa _ _ hg hg', smul_add]
  · simp only [aPlusAll_eq, os _ _ _ hg]
    rw [smul_comm]
  · have h1 : -Complex.I - Complex.I ≠ 0 := fun h => Complex.I_ne_zero (by linear_combination (-1 / 2 : ℂ) * h)
    exact mul_ne_zero (inv_ne_zero (fockScale_ne _)) (mul_ne_zero (neg_ne_zero.2 Complex.two_pi_I_ne_zero)
      (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 (xi_im _))) h1))
  · simp only [aPlusAll_eq]
    rw [os _ _ _ (ot _ _ hg), op_comm M M' hψ hθ _ _ p q hg, smul_add, smul_smul]
    congr 2
    split_ifs with h
    · rw [h]
    · rw [mul_zero]
  · have h := hf.vac p.1 (uv M M' p.1 p.2.1 p.2.2 1)
    rw [annih, cplxO_uv] at h
    exact h

end GlobalTheory.FockInj

end
