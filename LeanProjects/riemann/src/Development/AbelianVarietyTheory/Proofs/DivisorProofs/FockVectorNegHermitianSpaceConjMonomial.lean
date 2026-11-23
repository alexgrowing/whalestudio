import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj

namespace GlobalTheory.FockConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem inv_neg_mat {k : Type} [Fintype k] [DecidableEq k] {R : Type} [CommRing R] (A : Matrix k k R) :
    (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · have e : ((-1 : Rˣ) • A) = -A := by simp
    rw [← e, Matrix.inv_smul' (A := A) (k := (-1 : Rˣ)) h]
    simp
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      apply h
      have : IsUnit ((-1 : R) ^ Fintype.card k) := (isUnit_neg_one (α := R)).pow _
      exact (IsUnit.mul_iff.1 hu).2
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem symplOH_negSp (S T : HSp D) (x y : WO S T) :
    symplOH (negSp S) T x y = -symplOH S T x y := by
  have h : hO (negSp S) T x y = -hO S T x y := by
    unfold hO
    rw [negSp_gram, inv_neg_mat]
    simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  unfold symplOH symplO
  rw [h, mul_neg, map_neg, mul_neg]

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ a]
  simp [Complex.star_def]

theorem heisO_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) (w₀ : WO S T)
    (g : WO S T → ℂ) :
    heisO ψ (negSp S) T w₀ (fun w => star (g w)) = fun w => star (heisO ψ S T w₀ g w) := by
  funext w
  unfold heisO
  rw [star_mul, symplOH_negSp, ← star_psi hψ]
  ring

theorem lineAt_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (y : Matrix (Fin m) (Fin n) ℂ) :
    lineAt θ τ (-y) = -(lineAt θ τ y) := by
  have h := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ y
  refine GlobalTheory.RealLineAt.lineAt_unique D θ hθ m n τ (-y) _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ (-y)) ?_
  refine ⟨h.1.neg, fun t => ?_, fun t τ' => ?_⟩
  · have h2 := h.2.1 t
    ext i j
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    simp only [Matrix.map_apply, Matrix.zero_apply, AddMonoidHom.neg_apply, Matrix.neg_apply, RingHom.map_neg, this,
      neg_zero]
  · have h3 := h.2.2 t τ'
    have e : compAt θ τ' ((-(lineAt θ τ y)) t) = -compAt θ τ' (lineAt θ τ y t) := by
      ext i j
      simp only [compAt, Matrix.map_apply, AddMonoidHom.neg_apply, Matrix.neg_apply, RingHom.map_neg]
    rw [e, h3]
    split_ifs <;> simp

end GlobalTheory.FockConj

namespace GlobalTheory.FockConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem dRho_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (τ : D.what₂.Tau) (y : Matrix (Fin m) (Fin n) ℂ) (h : Mx D m n → ℂ) :
    Formalism.IndefR.Datum.dRho hs θ τ (-y) h = -Formalism.IndefR.Datum.dRho hs θ τ y h := by
  funext x
  have e : (fun t : ℝ => hs (lineAt θ τ (-y) t) h x) = fun t => (fun s : ℝ => hs (lineAt θ τ y s) h x) (-t) := by
    funext t
    rw [lineAt_neg hθ, AddMonoidHom.neg_apply, ← map_neg]
  simp only [Formalism.IndefR.Datum.dRho, Pi.neg_apply]
  rw [e]
  exact (deriv_comp_neg (f := fun s : ℝ => hs (lineAt θ τ y s) h x) (x := 0)).trans (by rw [neg_zero])

theorem dRho_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (θ : InfFam D) (S T : HSp D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ (negSp S) T) θ τ z (fun w => star (g w)) = fun w => star (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g w) := by
  funext x
  simp only [Formalism.IndefR.Datum.dRho]
  have e : (fun t : ℝ => heisO ψ (negSp S) T (lineAt θ τ z t) (fun w => star (g w)) x) =
      fun t => star (heisO ψ S T (lineAt θ τ z t) g x) := by
    funext t
    rw [heisO_negSp_star hψ]
  rw [e, deriv.star]

theorem cplxO_neg {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ)
    (z : Matrix (Fin m) (Fin n) ℂ) : cplxO (-sS) sT z = -cplxO sS sT z := by
  unfold cplxO
  rw [Matrix.mul_neg, smul_neg]

theorem aPlus_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) {θ : InfFam D} (hθ : IsInfFam θ)
    (S T : HSp D) (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    aPlus (heisO ψ (negSp S) T) θ τ (cplxO (-sS) sT) u (fun w => star (g w)) =
      fun w => star (aPlus (heisO ψ S T) θ τ (cplxO sS sT) u g w) := by
  funext w
  simp only [aPlus, crea, cplxO_neg, dRho_neg hθ, dRho_negSp_star hψ]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    smul_eq_mul, star_mul, star_sub, Complex.star_def, Complex.conj_I, map_inv₀, Complex.conj_ofReal]
  ring

theorem foldr_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) {θ : InfFam D} (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (L : List (FVar D T.rank S.rank)) (g : WO S T → ℂ) :
    L.foldr (fun i h => aPlusAll (heisO ψ (negSp S) T) θ (fun τ => cplxO (-sS τ) (sT τ)) BS BT i h)
        (fun w => star (g w)) =
      fun w => star (L.foldr (fun i h => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i h) g w) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    exact aPlus_negSp_star hψ hθ S T a.1 (sS a.1) (sT a.1) _ _

end GlobalTheory.FockConj

namespace GlobalTheory.FockConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorO_negSp_monomial : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO (negSp S) T → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (k : FVar D T.rank S.rank →₀ ℕ) (x : WO S T), pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT f (MvPolynomial.monomial k 1) x = starRingEnd ℂ (pureTensorO ψ θ S T sS sT BS BT (fun w => starRingEnd ℂ (f w)) (MvPolynomial.monomial k 1) x) := by
  intro D ψ θ S T sS sT BS BT f hψ hθ k x
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have h1 : pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT f (MvPolynomial.monomial k 1) =
      opPow (aPlusAll (heisO ψ (negSp S) T) θ (fun τ => cplxO (-sS τ) (sT τ)) BS BT) k f := by
    have := (MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ
      (fun k => opPow (aPlusAll (heisO ψ (negSp S) T) θ (fun τ => cplxO (-sS τ) (sT τ)) BS BT) k f) k
    rwa [MvPolynomial.coe_basisMonomials] at this
  have h2 : pureTensorO ψ θ S T sS sT BS BT (fun w => starRingEnd ℂ (f w)) (MvPolynomial.monomial k 1) =
      opPow (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) k (fun w => starRingEnd ℂ (f w)) := by
    have := (MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ
      (fun k => opPow (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) k
        (fun w => starRingEnd ℂ (f w))) k
    rwa [MvPolynomial.coe_basisMonomials] at this
  rw [h1, h2, opPow, opPow]
  have hf : f = fun w => star (starRingEnd ℂ (f w)) := by
    funext w
    simp
  conv_lhs => rw [hf]
  rw [foldr_negSp_star hn hθ S T sS sT BS BT]
  rfl

end GlobalTheory.FockConj
