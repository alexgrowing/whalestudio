import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.NormDeltaLowOfFockDeltaLow
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix MeasureTheory
open scoped ComplexOrder

namespace Formalism.IndefR.Fock.Der

open Formalism.IndefR.Fock.Sk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Defs

variable {m n : ℕ}

def dzPol (τ : D.what₂.Tau) (BS : Matrix (Fin n) (Fin n) ℂ) (BT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ)
    (z : Matrix (Fin m) (Fin n) ℂ) (P : MvPolynomial (FVar D m n) ℂ) : MvPolynomial (FVar D m n) ℂ :=
  MvPolynomial.C ((fockScale D τ : ℂ) / 2) * ∑ k : Fin m × Fin n,
    (MvPolynomial.C (fCoord BS BT pS pT z k) * MvPolynomial.X (τ, k.1, k.2) * P -
      MvPolynomial.C (starRingEnd ℂ (fCoord BS BT pS pT z k)) * MvPolynomial.pderiv (τ, k.1, k.2) P)

def dOm {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (θ : InfFam D) (τ : D.what₂.Tau)
    (XS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (XT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (F : WO S T → ℂ) :
    WO S T → ℂ :=
  fun x => deriv (fun t : ℝ => om (oneP θ S τ XS t, oneP θ T τ XT t) F x) 0

def IsVacTh (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (τ : D.what₂.Tau) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f

end Defs

section Steps

def QuadCommPol (D : D7) : Prop :=
  ∀ (m n pS pT : ℕ) (τ : D.what₂.Tau) (GS sS BS XS : Matrix (Fin n) (Fin n) ℂ) (GT sT BT XT : Matrix (Fin m) (Fin m) ℂ),
    IsONBasis GS sS BS pS → IsONBasis GT sT BT pT → XSᴴ * GS + GS * XS = 0 → XTᴴ * GT + GT * XT = 0 →
    ∀ (z : Matrix (Fin m) (Fin n) ℂ) (P : MvPolynomial (FVar D m n) ℂ),
      quadOp τ sS BS XS sT BT XT pS pT (dzPol τ BS BT pS pT z P) -
          dzPol τ BS BT pS pT z (quadOp τ sS BS XS sT BT XT pS pT P) =
        dzPol τ BS BT pS pT (adX XS XT z) P

def FCoordFacts : Prop :=
  ∀ (m n pS pT : ℕ) (GS sS BS : Matrix (Fin n) (Fin n) ℂ) (GT sT BT : Matrix (Fin m) (Fin m) ℂ),
    IsONBasis GS sS BS pS → IsONBasis GT sT BT pT →
    (∀ (z : Matrix (Fin m) (Fin n) ℂ) (k : Fin m × Fin n),
      fCoord BS BT pS pT (cplxO sS sT z) k = Complex.I * fCoord BS BT pS pT z k) ∧
    ∀ (i : Fin m) (c : Fin n) (k : Fin m × Fin n), fCoord BS BT pS pT (unitMap BS BT i c) k = if k = (i, c) then 1 else 0

def DRhoPoly (D : D7) : Prop :=
  LineAtExists D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT BS BT (pS pT : D.what₂.Tau → ℕ),
    PairSetup ψ θ S T sS sT BS BT pS pT →
    ∀ (τ : D.what₂.Tau) (f : WO S T → ℂ), IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f →
      ∀ (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ),
        dRho (heisO ψ S T) θ τ z (pureTensorO ψ θ S T sS sT BS BT f P) =
          pureTensorO ψ θ S T sS sT BS BT f (dzPol τ (BS τ) (BT τ) (pS τ) (pT τ) z P)

def HeisFarDRho (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → LineAtExists D →
    ∀ (S T : HSp D) (τ : D.what₂.Tau) (w : WO S T), compAt θ τ w = 0 →
      ∀ (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (F : WO S T → ℂ), IsThetaFunO ψ S T F →
        dRho (heisO ψ S T) θ τ z (heisO ψ S T w F) = heisO ψ S T w (dRho (heisO ψ S T) θ τ z F)

def OmSmoothO (D : D7) : Prop :=
  LineAtExists D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om →
    ∀ (τ : D.what₂.Tau) (XS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (XT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
      XS ∈ lieAt S τ → XT ∈ lieAt T τ → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F →
        (∀ x, DifferentiableAt ℝ (fun t : ℝ => om (oneP θ S τ XS t, oneP θ T τ XT t) F x) 0) ∧
          IsThetaFunO ψ S T (dOm om θ τ XS XT F)

open Classical in

def OmDerDRho (D : D7) : Prop :=
  LineAtExists D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om →
    ∀ (τ : D.what₂.Tau) (XS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (XT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
      XS ∈ lieAt S τ → XT ∈ lieAt T τ →
      ∀ (τ' : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (F : WO S T → ℂ), IsThetaFunO ψ S T F →
        dOm om θ τ XS XT (dRho (heisO ψ S T) θ τ' z F) - dRho (heisO ψ S T) θ τ' z (dOm om θ τ XS XT F) =
          if τ' = τ then dRho (heisO ψ S T) θ τ (adX XS XT z) F else 0

def OmDerFar (D : D7) : Prop :=
  LineAtExists D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om →
    ∀ (τ : D.what₂.Tau) (XS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (XT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
      XS ∈ lieAt S τ → XT ∈ lieAt T τ → ∀ w : WO S T, compAt θ τ w = 0 →
        ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F →
          dOm om θ τ XS XT (heisO ψ S T w F) = heisO ψ S T w (dOm om θ τ XS XT F)

def OmDerSkew (D : D7) : Prop :=
  LineAtExists D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om →
    ∀ (τ : D.what₂.Tau) (XS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (XT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
      XS ∈ lieAt S τ → XT ∈ lieAt T τ →
      ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
        ∀ F G : WO S T → ℂ, IsThetaFunO ψ S T F → IsThetaFunO ψ S T G →
          ∫ w in 𝓕, dOm om θ τ XS XT F w * starRingEnd ℂ (G w) ∂μ =
            -∫ w in 𝓕, F w * starRingEnd ℂ (dOm om θ τ XS XT G w) ∂μ

def VacSchur (D : D7) : Prop :=
  LineAtExists D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT BS BT (pS pT : D.what₂.Tau → ℕ),
    PairSetup ψ θ S T sS sT BS BT pS pT → ∀ (τ : D.what₂.Tau) (Φ : (WO S T → ℂ) → (WO S T → ℂ)),
      (∀ f, IsVacTh ψ θ S T (sS τ) (sT τ) τ f → IsVacTh ψ θ S T (sS τ) (sT τ) τ (Φ f)) →
      (∀ f g (c : ℂ), IsVacTh ψ θ S T (sS τ) (sT τ) τ f → IsVacTh ψ θ S T (sS τ) (sT τ) τ g →
        Φ (f + c • g) = Φ f + c • Φ g) →
      (∀ w : WO S T, compAt θ τ w = 0 → ∀ f, IsVacTh ψ θ S T (sS τ) (sT τ) τ f →
        Φ (heisO ψ S T w f) = heisO ψ S T w (Φ f)) →
      (∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
        ∀ f g, IsVacTh ψ θ S T (sS τ) (sT τ) τ f → IsVacTh ψ θ S T (sS τ) (sT τ) τ g →
          ∫ w in 𝓕, Φ f w * starRingEnd ℂ (g w) ∂μ = -∫ w in 𝓕, f w * starRingEnd ℂ (Φ g w) ∂μ) →
      ∃ c : ℂ, ∀ f, IsVacTh ψ θ S T (sS τ) (sT τ) τ f → Φ f = c • f

end Steps

section Help

open Formalism.IndefR.Fock.Alg

variable {ι X : Type} [DecidableEq ι] {Sm : Set (X → ℂ)} {aP aM : ι → (X → ℂ) → (X → ℂ)} {v : X → ℂ}

theorem pt_C (v : X → ℂ) (a : ℂ) : pureTensorL aP v (MvPolynomial.C a) = a • v := by
  rw [MvPolynomial.C_apply, pt_monomial, opPow_zero]

theorem pt_one (v : X → ℂ) : pureTensorL aP v 1 = v := by
  rw [← MvPolynomial.C_1, pt_C, one_smul]

theorem pt_C_mul (v : X → ℂ) (a : ℂ) (P : MvPolynomial ι ℂ) :
    pureTensorL aP v (MvPolynomial.C a * P) = a • pureTensorL aP v P := by
  rw [MvPolynomial.C_mul', map_smul]

theorem creation_add (h : IsCCR Sm aP aM) (i : ι) {f g : X → ℂ} (hf : f ∈ Sm) (hg : g ∈ Sm) :
    aP i (f + g) = aP i f + aP i g := by
  have := h.linP i 1 f g hf hg
  simpa using this

theorem pt_X_mul (h : IsCCR Sm aP aM) (hv : v ∈ Sm) (l : ι) (P : MvPolynomial ι ℂ) :
    pureTensorL aP v (MvPolynomial.X l * P) = aP l (pureTensorL aP v P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, pt_monomial, pt_monomial,
      add_comm (Finsupp.single l 1) k, opPow_add_single h hv, creation_smul h l c (opPow_mem h hv k)]
  | add p q hp hq =>
    rw [mul_add, map_add, map_add, hp, hq,
      creation_add h l (ccrMemAbs Sm aP aM v h hv p) (ccrMemAbs Sm aP aM v h hv q)]

end Help

section PolHelp

variable {m n : ℕ}

theorem pderiv_X_mul_of_ne {σ : Type} [DecidableEq σ] {i j : σ} (h : i ≠ j) (P : MvPolynomial σ ℂ) :
    MvPolynomial.pderiv i (MvPolynomial.X j * P) = MvPolynomial.X j * MvPolynomial.pderiv i P := by
  rw [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, if_neg (Ne.symm h), smul_zero, add_zero,
    smul_eq_mul]

theorem quadOp_add (τ : D.what₂.Tau) (sS BS XS : Matrix (Fin n) (Fin n) ℂ) (sT BT XT : Matrix (Fin m) (Fin m) ℂ)
    (pS pT : ℕ) (P P' : MvPolynomial (FVar D m n) ℂ) :
    quadOp τ sS BS XS sT BT XT pS pT (P + P') =
      quadOp τ sS BS XS sT BT XT pS pT P + quadOp τ sS BS XS sT BT XT pS pT P' := by
  simp only [quadOp, map_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem quadOp_C_mul (τ : D.what₂.Tau) (sS BS XS : Matrix (Fin n) (Fin n) ℂ) (sT BT XT : Matrix (Fin m) (Fin m) ℂ)
    (pS pT : ℕ) (a : ℂ) (P : MvPolynomial (FVar D m n) ℂ) :
    quadOp τ sS BS XS sT BT XT pS pT (MvPolynomial.C a * P) =
      MvPolynomial.C a * quadOp τ sS BS XS sT BT XT pS pT P := by
  simp only [quadOp, Finset.mul_sum, MvPolynomial.pderiv_C_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem quadOp_zero (τ : D.what₂.Tau) (sS BS XS : Matrix (Fin n) (Fin n) ℂ) (sT BT XT : Matrix (Fin m) (Fin m) ℂ)
    (pS pT : ℕ) : quadOp τ sS BS XS sT BT XT pS pT (0 : MvPolynomial (FVar D m n) ℂ) = 0 := by
  simpa using quadOp_C_mul τ sS BS XS sT BT XT pS pT 0 0

theorem quadOp_one (τ : D.what₂.Tau) (sS BS XS : Matrix (Fin n) (Fin n) ℂ) (sT BT XT : Matrix (Fin m) (Fin m) ℂ)
    (pS pT : ℕ) : quadOp τ sS BS XS sT BT XT pS pT (1 : MvPolynomial (FVar D m n) ℂ) =
      ∑ k : Fin m × Fin n, ∑ l : Fin m × Fin n,
        MvPolynomial.C (nCoef sS BS XS sT BT XT pS pT k l / 2) * MvPolynomial.X (τ, k.1, k.2) *
          MvPolynomial.X (τ, l.1, l.2) := by
  simp only [quadOp, Derivation.map_one_eq_zero, map_zero, mul_zero, mul_one, sub_zero, zero_add]

open Classical in
theorem quadOp_X_far (τ τ' : D.what₂.Tau) (h : τ' ≠ τ) (sS BS XS : Matrix (Fin n) (Fin n) ℂ)
    (sT BT XT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ) (i : Fin m) (c : Fin n) (P : MvPolynomial (FVar D m n) ℂ) :
    quadOp τ sS BS XS sT BT XT pS pT (MvPolynomial.X (τ', i, c) * P) =
      MvPolynomial.X (τ', i, c) * quadOp τ sS BS XS sT BT XT pS pT P := by
  have hne : ∀ k : Fin m × Fin n, ((τ, k.1, k.2) : FVar D m n) ≠ (τ', i, c) := fun k h' =>
    h (congrArg Prod.fst h').symm
  simp only [quadOp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [pderiv_X_mul_of_ne (σ := FVar D m n) (hne l), pderiv_X_mul_of_ne (σ := FVar D m n) (hne k)]
  ring

theorem hII : (MvPolynomial.C Complex.I : MvPolynomial (FVar D m n) ℂ) * MvPolynomial.C Complex.I = -1 := by
  rw [← map_mul, Complex.I_mul_I, map_neg, map_one]

theorem creaPol (hF : FCoordFacts) {pS pT : ℕ} {GS sS BS : Matrix (Fin n) (Fin n) ℂ}
    {GT sT BT : Matrix (Fin m) (Fin m) ℂ} (hS : IsONBasis GS sS BS pS) (hT : IsONBasis GT sT BT pT)
    (τ : D.what₂.Tau) (i : Fin m) (c : Fin n) (P : MvPolynomial (FVar D m n) ℂ) :
    MvPolynomial.C ((fockScale D τ : ℂ)⁻¹) * dzPol τ BS BT pS pT (unitMap BS BT i c) P +
      MvPolynomial.C (-((fockScale D τ : ℂ)⁻¹) * Complex.I) *
        dzPol τ BS BT pS pT (cplxO sS sT (unitMap BS BT i c)) P =
      MvPolynomial.X (τ, i, c) * P := by
  obtain ⟨hJ, hU⟩ := hF m n pS pT GS sS BS GT sT BT hS hT
  have hfs : (fockScale D τ : ℂ) ≠ 0 := by exact_mod_cast (Formalism.IndefR.Fock.CCR.fockScale_pos D τ).ne'
  have hD1 : dzPol τ BS BT pS pT (unitMap BS BT i c) P = ((fockScale D τ : ℂ) / 2) •
      (MvPolynomial.X (τ, i, c) * P - MvPolynomial.pderiv (τ, i, c) P) := by
    simp only [dzPol, hU]
    rw [Finset.sum_eq_single (i, c) (fun k _ hk => by simp [hk]) (by simp)]
    simp [MvPolynomial.C_mul']
  have hD2 : dzPol τ BS BT pS pT (cplxO sS sT (unitMap BS BT i c)) P = ((fockScale D τ : ℂ) / 2) •
      (Complex.I • (MvPolynomial.X (τ, i, c) * P) + Complex.I • MvPolynomial.pderiv (τ, i, c) P) := by
    simp only [dzPol, hJ, hU]
    rw [Finset.sum_eq_single (i, c) (fun k _ hk => by simp [hk]) (by simp)]
    simp only [if_true, mul_one, Complex.conj_I, MvPolynomial.C_mul', smul_mul_assoc, neg_smul, sub_neg_eq_add]
  rw [hD1, hD2, MvPolynomial.C_mul', MvPolynomial.C_mul']
  simp only [smul_sub, smul_add, smul_smul]
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hinv : (fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ) = 1 := inv_mul_cancel₀ hfs
  match_scalars
  all_goals first
    | linear_combination (-((fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ) / 2)) * hI2 + hinv
    | linear_combination (-((fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ) / 2)) * hI2
    | linear_combination ((fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ) / 2) * hI2 - hinv
    | linear_combination ((fockScale D τ : ℂ)⁻¹ * (fockScale D τ : ℂ) / 2) * hI2

theorem annihPolOne (hF : FCoordFacts) {pS pT : ℕ} {GS sS BS : Matrix (Fin n) (Fin n) ℂ}
    {GT sT BT : Matrix (Fin m) (Fin m) ℂ} (hS : IsONBasis GS sS BS pS) (hT : IsONBasis GT sT BT pT)
    (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) :
    dzPol τ BS BT pS pT z (1 : MvPolynomial (FVar D m n) ℂ) +
      MvPolynomial.C Complex.I * dzPol τ BS BT pS pT (cplxO sS sT z) 1 = 0 := by
  obtain ⟨hJ, -⟩ := hF m n pS pT GS sS BS GT sT BT hS hT
  simp only [dzPol, hJ, Derivation.map_one_eq_zero, mul_zero, sub_zero, mul_one]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [map_mul]
  linear_combination (MvPolynomial.C ((fockScale D τ : ℂ) / 2) * MvPolynomial.C (fCoord BS BT pS pT z k) *
    MvPolynomial.X (τ, k.1, k.2)) * (hII (D := D) (m := m) (n := n))

end PolHelp

section Assembly

open Formalism.IndefR.Fock.Alg Formalism.IndefR.Fock.CCR

variable {m n : ℕ}

def q1Op (aP : FVar D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (τ : D.what₂.Tau)
    (N : Fin m × Fin n → Fin m × Fin n → ℂ) (F : Mx D m n → ℂ) : Mx D m n → ℂ :=
  ∑ p : (Fin m × Fin n) × (Fin m × Fin n), (N p.1 p.2 / 2) • aP (τ, p.1.1, p.1.2) (aP (τ, p.2.1, p.2.2) F)

def ipF {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓕 : Set X) (F G : X → ℂ) : ℂ :=
  ∫ w in 𝓕, F w * starRingEnd ℂ (G w) ∂μ

section Gen

variable {Sm : Set (Mx D m n → ℂ)} {aP aM : FVar D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)}

theorem quadratic_operator_mem [DecidableEq (FVar D m n)] (h : IsCCR Sm aP aM) (τ : D.what₂.Tau) (N : Fin m × Fin n → Fin m × Fin n → ℂ)
    {F : Mx D m n → ℂ} (hF : F ∈ Sm) : q1Op aP τ N F ∈ Sm :=
  sum_mem' h _ _ _ fun p _ => h.memP _ _ (h.memP _ _ hF)

theorem quadratic_operator_linear [DecidableEq (FVar D m n)] (h : IsCCR Sm aP aM) (τ : D.what₂.Tau)
    (N : Fin m × Fin n → Fin m × Fin n → ℂ) {f g : Mx D m n → ℂ} (hf : f ∈ Sm) (hg : g ∈ Sm) (c : ℂ) :
    q1Op aP τ N (f + c • g) = q1Op aP τ N f + c • q1Op aP τ N g := by
  unfold q1Op
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [h.linP _ c f g hf hg, h.linP _ c _ _ (h.memP _ f hf) (h.memP _ g hg), smul_add, smul_comm]

theorem quadratic_operator_orthogonal [DecidableEq (FVar D m n)] (h : IsCCR Sm aP aM) {ip : (Mx D m n → ℂ) → (Mx D m n → ℂ) → ℂ}
    (hs : IsSesq Sm ip) (adj1 : ∀ k F G, F ∈ Sm → G ∈ Sm → ip (aP k F) G = ip F (aM k G))
    (adj2 : ∀ k F G, F ∈ Sm → G ∈ Sm → ip F (aP k G) = ip (aM k F) G) (τ : D.what₂.Tau)
    (N : Fin m × Fin n → Fin m × Fin n → ℂ) {f g : Mx D m n → ℂ} (hf : f ∈ Sm) (hg : g ∈ Sm)
    (hvf : ∀ k : Fin m × Fin n, aM (τ, k.1, k.2) f = 0) (hvg : ∀ k : Fin m × Fin n, aM (τ, k.1, k.2) g = 0) :
    ip (q1Op aP τ N f) g = 0 ∧ ip f (q1Op aP τ N g) = 0 := by
  constructor
  · unfold q1Op
    rw [ip_sum_left h hs _ _ _ (fun p _ => h.memP _ _ (h.memP _ _ hf)) hg]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [adj1 _ _ _ (h.memP _ _ hf) hg, hvg, ip_zero_right hs h.zero_mem (h.memP _ _ hf), mul_zero]
  · unfold q1Op
    rw [ip_sum_right h hs _ _ _ (fun p _ => h.memP _ _ (h.memP _ _ hg)) hf]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [adj2 _ _ _ hf (h.memP _ _ hg), hvf, ip_zero_left hs h.zero_mem (h.memP _ _ hg), mul_zero]

open Classical in
theorem quadratic_operator_pure_tensor (h : IsCCR Sm aP aM) {v : Mx D m n → ℂ} (hv : v ∈ Sm) (τ : D.what₂.Tau)
    (sS BS XS : Matrix (Fin n) (Fin n) ℂ) (sT BT XT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ) :
    pureTensorL aP v (quadOp τ sS BS XS sT BT XT pS pT 1) = q1Op aP τ (nCoef sS BS XS sT BT XT pS pT) v := by
  have e : ∀ g : (Fin m × Fin n) × (Fin m × Fin n) → (Mx D m n → ℂ), ∑ p, g p = ∑ k, ∑ l, g (k, l) :=
    fun g => by rw [Fintype.sum_prod_type]
  rw [quadOp_one, map_sum, q1Op, e]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, pt_C_mul, pt_X_mul h hv, ← mul_one (MvPolynomial.X ((τ, l.1, l.2) : FVar D m n)),
    pt_X_mul h hv, pt_one]

end Gen

open Classical in

theorem int_sesq_adj (hT : ThetaDRho D) (hL : DRhoLin D) (hC : DRhoComm D) (hLine : LineAtExists D)
    {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS sT BS BT} {pS pT : D.what₂.Tau → ℕ}
    (hP : PairSetup ψ θ S T sS sT BS BT pS pT) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hcov : IsCovolOne (ratL T S) μ 𝓕) :
    IsSesq {F | IsThetaFunO ψ S T F} (ipF μ 𝓕) ∧
    (∀ k F G, IsThetaFunO ψ S T F → IsThetaFunO ψ S T G →
      ipF μ 𝓕 (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k F) G =
        ipF μ 𝓕 F (aMinusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k G)) ∧
    (∀ k F G, IsThetaFunO ψ S T F → IsThetaFunO ψ S T G →
      ipF μ 𝓕 F (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k G) =
        ipF μ 𝓕 (aMinusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k F) G) := by
  have hstd := hP.std
  have hinf := hP.inf
  have hd : ∀ τ z F, IsThetaFunO ψ S T F → IsThetaFunO ψ S T (dRho (heisO ψ S T) θ τ z F) :=
    fun τ z F hF => (hT ψ θ hstd hinf hLine S T τ z F hF).1
  have hI := Formalism.IndefR.Fock.Skew.thetaIntO D ψ hstd S T μ 𝓕 hcov
  have hskew := Formalism.IndefR.Fock.Skew.dRhoSkew_of D hT
  have lin1 : ∀ F G H (a b : ℂ), IsThetaFunO ψ S T F → IsThetaFunO ψ S T G → IsThetaFunO ψ S T H →
      ipF μ 𝓕 (a • F + b • G) H = a * ipF μ 𝓕 F H + b * ipF μ 𝓕 G H := by
    intro F G H a b hF hG hH
    simp only [ipF, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : (fun w => (a * F w + b * G w) * starRingEnd ℂ (H w)) =
        fun w => a * (F w * starRingEnd ℂ (H w)) + b * (G w * starRingEnd ℂ (H w)) := by
      funext w; ring
    rw [e, integral_add ((hI F H hF hH).const_mul a) ((hI G H hG hH).const_mul b), integral_const_mul,
      integral_const_mul]
  have lin2 : ∀ F G H (a b : ℂ), IsThetaFunO ψ S T F → IsThetaFunO ψ S T G → IsThetaFunO ψ S T H →
      ipF μ 𝓕 H (a • F + b • G) = starRingEnd ℂ a * ipF μ 𝓕 H F + starRingEnd ℂ b * ipF μ 𝓕 H G := by
    intro F G H a b hF hG hH
    simp only [ipF, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have e : (fun w => H w * starRingEnd ℂ (a * F w + b * G w)) =
        fun w => starRingEnd ℂ a * (H w * starRingEnd ℂ (F w)) + starRingEnd ℂ b * (H w * starRingEnd ℂ (G w)) := by
      funext w; simp only [map_add, map_mul]; ring
    rw [e, integral_add ((hI H F hH hF).const_mul _) ((hI H G hH hG).const_mul _), integral_const_mul,
      integral_const_mul]
  have skew : ∀ τ z F G, IsThetaFunO ψ S T F → IsThetaFunO ψ S T G →
      ipF μ 𝓕 (dRho (heisO ψ S T) θ τ z F) G = -ipF μ 𝓕 F (dRho (heisO ψ S T) θ τ z G) :=
    fun τ z F G hF hG => hskew ψ θ hstd hinf hLine S T τ z μ 𝓕 hcov F G hF hG
  refine ⟨fun F G H c hF hG hH => ⟨by simpa using lin1 F G H 1 c hF hG hH, by simpa using lin2 F G H 1 c hF hG hH⟩,
    fun k F G hF hG => ?_, fun k F G hF hG => ?_⟩
  · rw [aMinusAll_eq, aPlusAll_eq, lin1 _ _ _ _ _ (hd _ _ F hF) (hd _ _ F hF) hG,
      lin2 _ _ _ _ _ (hd _ _ G hG) (hd _ _ G hG) hF, skew _ _ _ _ hF hG, skew _ _ _ _ hF hG]
    simp only [map_mul, map_neg, Formalism.IndefR.Fock.Norm.conj_inv_ofReal, Complex.conj_I]
    ring
  · rw [aMinusAll_eq, aPlusAll_eq, lin1 _ _ _ _ _ (hd _ _ F hF) (hd _ _ F hF) hG,
      lin2 _ _ _ _ _ (hd _ _ G hG) (hd _ _ G hG) hF, skew _ _ _ _ hF hG, skew _ _ _ _ hF hG]
    simp only [map_mul, map_neg, Formalism.IndefR.Fock.Norm.conj_inv_ofReal, Complex.conj_I]
    ring

set_option maxHeartbeats 1000000 in
open Classical in

theorem fockDerO_of (hT : ThetaDRho D) (hL : DRhoLin D) (hC : DRhoComm D) (hA : QuadCommPol D) (hF : FCoordFacts)
    (hB : DRhoPoly D) (hH : HeisFarDRho D) (hS : OmSmoothO D) (hDR : OmDerDRho D) (hFar : OmDerFar D)
    (hSk : OmDerSkew D) (hV : VacSchur D) : FockDerO D := by
  intro hLine ψ θ S T sS sT BS BT pS pT χS χT om hP hW τ XS XT hXS hXT
  simp only [pureTensorO]
  have hstd := hP.std
  have hinf := hP.inf
  have hccr := Formalism.IndefR.Fock.Final.ccrTheta_of_drho hT hL hC hLine ψ θ S T sS sT BS BT pS pT hP
  set aP := aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT with haP
  set aM := aMinusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT with haM
  set δ := dOm om θ τ XS XT with hδ
  set Q := quadOp τ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) with hQ
  set Dz : Matrix (Fin T.rank) (Fin S.rank) ℂ → MvPolynomial (FVar D T.rank S.rank) ℂ →
      MvPolynomial (FVar D T.rank S.rank) ℂ := fun z => dzPol τ (BS τ) (BT τ) (pS τ) (pT τ) z with hDz
  set A := adX XS XT with hAd
  set Jt := cplxO (sS τ) (sT τ) with hJt
  set N := nCoef (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) with hN
  set pt : (WO S T → ℂ) → MvPolynomial (FVar D T.rank S.rank) ℂ →ₗ[ℂ] (WO S T → ℂ) := fun f => pureTensorL aP f
    with hpt

  have hd : ∀ τ' z F, IsThetaFunO ψ S T F → IsThetaFunO ψ S T (dRho (heisO ψ S T) θ τ' z F) :=
    fun τ' z F hF => (hT ψ θ hstd hinf hLine S T τ' z F hF).1
  have hlin : ∀ τ' z (F G : WO S T → ℂ), IsThetaFunO ψ S T F → IsThetaFunO ψ S T G → ∀ a b : ℂ,
      dRho (heisO ψ S T) θ τ' z (a • F + b • G) =
        a • dRho (heisO ψ S T) θ τ' z F + b • dRho (heisO ψ S T) θ τ' z G :=
    fun τ' z F G hF hG a b => derived_action_linear_combination (θ := θ) hL hstd hinf hLine τ' z hF hG a b
  have hdiff : ∀ F, IsThetaFunO ψ S T F → ∀ x,
      DifferentiableAt ℝ (fun t : ℝ => om (oneP θ S τ XS t, oneP θ T τ XT t) F x) 0 :=
    fun F hF => (hS hLine ψ θ S T χS χT om hinf hW τ XS XT hXS hXT F hF).1
  have hδth : ∀ F, IsThetaFunO ψ S T F → IsThetaFunO ψ S T (δ F) :=
    fun F hF => (hS hLine ψ θ S T χS χT om hinf hW τ XS XT hXS hXT F hF).2
  have hδlin : ∀ (F G : WO S T → ℂ) (a b : ℂ), IsThetaFunO ψ S T F → IsThetaFunO ψ S T G →
      δ (a • F + b • G) = a • δ F + b • δ G := by
    intro F G a b hF hG
    funext x
    simp only [hδ, dOm, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (((hdiff F hF x).hasDerivAt.const_mul a).add ((hdiff G hG x).hasDerivAt.const_mul b)).deriv
  have hδ0 : δ 0 = 0 := by
    funext x
    simp [hδ, dOm]
  have hdr : ∀ τ' z F, IsThetaFunO ψ S T F →
      δ (dRho (heisO ψ S T) θ τ' z F) - dRho (heisO ψ S T) θ τ' z (δ F) =
        if τ' = τ then dRho (heisO ψ S T) θ τ (A z) F else 0 :=
    fun τ' z F hF => hDR hLine ψ θ S T χS χT om hinf hW τ XS XT hXS hXT τ' z F hF
  have hfar : ∀ w : WO S T, compAt θ τ w = 0 → ∀ F, IsThetaFunO ψ S T F →
      δ (heisO ψ S T w F) = heisO ψ S T w (δ F) :=
    fun w hw F hF => hFar hLine ψ θ S T χS χT om hinf hW τ XS XT hXS hXT w hw F hF
  have hb : ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ Jt f → ∀ z P,
      dRho (heisO ψ S T) θ τ z (pt f P) = pt f (Dz z P) :=
    fun f hf hv z P => hB hLine ψ θ S T sS sT BS BT pS pT hP τ f hf hv z P
  have ha : ∀ z P, Q (Dz z P) - Dz z (Q P) = Dz (A z) P :=
    fun z P => hA T.rank S.rank (pS τ) (pT τ) τ (gramAt D S τ) (sS τ) (BS τ) XS (gramAt D T τ) (sT τ) (BT τ) XT
      (hP.onbS τ) (hP.onbT τ) hXS hXT z P
  have hQlin : ∀ (a b : ℂ) P P', Q (MvPolynomial.C a * P + MvPolynomial.C b * P') =
      MvPolynomial.C a * Q P + MvPolynomial.C b * Q P' := fun a b P P' => by
    simp only [hQ, quadOp_add, quadOp_C_mul]
  have hpt_mem : ∀ f, IsThetaFunO ψ S T f → ∀ P, IsThetaFunO ψ S T (pt f P) :=
    fun f hf P => ccrMemAbs _ aP aM f hccr hf P
  have hptX : ∀ f, IsThetaFunO ψ S T f → ∀ l P, pt f (MvPolynomial.X l * P) = aP l (pt f P) :=
    fun f hf l P => pt_X_mul hccr hf l P

  set q1 : (WO S T → ℂ) → (WO S T → ℂ) := q1Op aP τ N with hq1
  have hq1pt : ∀ f, IsThetaFunO ψ S T f → pt f (Q 1) = q1 f := fun f hf => quadratic_operator_pure_tensor hccr hf τ _ _ _ _ _ _ _ _
  have hq1th : ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (q1 f) := fun f hf => quadratic_operator_mem hccr τ N hf
  set Φ : (WO S T → ℂ) → (WO S T → ℂ) := fun F => δ F - q1 F with hΦ

  have haPheis : ∀ w : WO S T, compAt θ τ w = 0 → ∀ (k : Fin T.rank × Fin S.rank) F, IsThetaFunO ψ S T F →
      aP (τ, k.1, k.2) (heisO ψ S T w F) = heisO ψ S T w (aP (τ, k.1, k.2) F) := by
    intro w hw k F hF
    simp only [haP, aPlusAll_eq]
    rw [hH ψ θ hstd hinf hLine S T τ w hw _ F hF, hH ψ θ hstd hinf hLine S T τ w hw _ F hF]
    funext x
    simp only [heisO, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hq1heis : ∀ w : WO S T, compAt θ τ w = 0 → ∀ F, IsThetaFunO ψ S T F →
      q1 (heisO ψ S T w F) = heisO ψ S T w (q1 F) := by
    intro w hw F hF
    have e : ∀ p : (Fin T.rank × Fin S.rank) × (Fin T.rank × Fin S.rank),
        aP (τ, p.1.1, p.1.2) (aP (τ, p.2.1, p.2.2) (heisO ψ S T w F)) =
          heisO ψ S T w (aP (τ, p.1.1, p.1.2) (aP (τ, p.2.1, p.2.2) F)) := fun p => by
      rw [haPheis w hw p.2 F hF, haPheis w hw p.1 _ (hccr.memP _ F hF)]
    simp only [hq1, q1Op, e]
    funext x
    simp only [heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring

  have hq1lin : ∀ f g (c : ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → q1 (f + c • g) = q1 f + c • q1 g :=
    fun f g c hf hg => quadratic_operator_linear hccr τ N hf hg c
  have hΦlin : ∀ f g (c : ℂ), IsVacTh ψ θ S T (sS τ) (sT τ) τ f → IsVacTh ψ θ S T (sS τ) (sT τ) τ g →
      Φ (f + c • g) = Φ f + c • Φ g := by
    intro f g c hf hg
    have e1 : δ (f + c • g) = δ f + c • δ g := by simpa using hδlin f g 1 c hf.1 hg.1
    simp only [hΦ]
    rw [e1, hq1lin f g c hf.1 hg.1, smul_sub]
    abel
  have hΦheis : ∀ w : WO S T, compAt θ τ w = 0 → ∀ f, IsVacTh ψ θ S T (sS τ) (sT τ) τ f →
      Φ (heisO ψ S T w f) = heisO ψ S T w (Φ f) := by
    intro w hw f hf
    simp only [hΦ]
    rw [hfar w hw f hf.1, hq1heis w hw f hf.1]
    funext x
    simp only [heisO, Pi.sub_apply]
    ring

  have hΦvac : ∀ f, IsVacTh ψ θ S T (sS τ) (sT τ) τ f → IsVacTh ψ θ S T (sS τ) (sT τ) τ (Φ f) := by
    intro f hf
    have hft := hf.1
    have hΦth : IsThetaFunO ψ S T (Φ f) := by
      have := theta_add_smul (hδth f hft) (hq1th f hft) (-1)
      simpa [hΦ, sub_eq_add_neg] using this
    refine ⟨hΦth, fun z => ?_⟩

    have hpol : Dz z (Q 1) + MvPolynomial.C Complex.I * Dz (Jt z) (Q 1) =
        -(Dz (A z) 1 + MvPolynomial.C Complex.I * Dz (A (Jt z)) 1) := by
      have h1 := ha z 1
      have h2 := ha (Jt z) 1
      have h0 := annihPolOne hF (hP.onbS τ) (hP.onbT τ) τ z
      have h3 : Q (Dz z 1) + MvPolynomial.C Complex.I * Q (Dz (Jt z) 1) = 0 := by
        have := hQlin 1 Complex.I (Dz z 1) (Dz (Jt z) 1)
        simp only [map_one, one_mul] at this
        rw [← this]
        have h0' : Dz z 1 + MvPolynomial.C Complex.I * Dz (Jt z) 1 = 0 := h0
        rw [h0', hQ, quadOp_zero]
      linear_combination (-1 : MvPolynomial (FVar D T.rank S.rank) ℂ) * h1 + (-MvPolynomial.C Complex.I) * h2 + h3
    have E6 : dRho (heisO ψ S T) θ τ z (q1 f) + Complex.I • dRho (heisO ψ S T) θ τ (Jt z) (q1 f) =
        -(dRho (heisO ψ S T) θ τ (A z) f + Complex.I • dRho (heisO ψ S T) θ τ (A (Jt z)) f) := by
      rw [← hq1pt f hft, hb f hft hf.2, hb f hft hf.2]
      have e := congrArg (pt f) hpol
      rw [map_add, map_neg, map_add, hpt, pt_C_mul, pt_C_mul] at e
      have eA : dRho (heisO ψ S T) θ τ (A z) f = pt f (Dz (A z) 1) := by
        have := hb f hft hf.2 (A z) 1; rwa [hpt, pt_one] at this
      have eAJ : dRho (heisO ψ S T) θ τ (A (Jt z)) f = pt f (Dz (A (Jt z)) 1) := by
        have := hb f hft hf.2 (A (Jt z)) 1; rwa [hpt, pt_one] at this
      rw [eA, eAJ]
      simpa [hpt] using e
    have E1 := hdr τ z f hft
    have E2 := hdr τ (Jt z) f hft
    rw [if_pos rfl] at E1 E2
    have E3 : δ (dRho (heisO ψ S T) θ τ z f) + Complex.I • δ (dRho (heisO ψ S T) θ τ (Jt z) f) = 0 := by
      have := hδlin _ _ 1 Complex.I (hd τ z f hft) (hd τ (Jt z) f hft)
      simp only [one_smul] at this
      rw [← this]
      have hz : dRho (heisO ψ S T) θ τ z f + Complex.I • dRho (heisO ψ S T) θ τ (Jt z) f = 0 := hf.2 z
      rw [hz, hδ0]
    have E4 : dRho (heisO ψ S T) θ τ z (Φ f) =
        dRho (heisO ψ S T) θ τ z (δ f) - dRho (heisO ψ S T) θ τ z (q1 f) := by
      have := hlin τ z _ _ (hδth f hft) (hq1th f hft) 1 (-1)
      simpa [hΦ, sub_eq_add_neg] using this
    have E5 : dRho (heisO ψ S T) θ τ (Jt z) (Φ f) =
        dRho (heisO ψ S T) θ τ (Jt z) (δ f) - dRho (heisO ψ S T) θ τ (Jt z) (q1 f) := by
      have := hlin τ (Jt z) _ _ (hδth f hft) (hq1th f hft) 1 (-1)
      simpa [hΦ, sub_eq_add_neg] using this
    show dRho (heisO ψ S T) θ τ z (Φ f) + Complex.I • dRho (heisO ψ S T) θ τ (Jt z) (Φ f) = 0
    funext x
    have e1 := congrFun E1 x
    have e2 := congrFun E2 x
    have e3 := congrFun E3 x
    have e4 := congrFun E4 x
    have e5 := congrFun E5 x
    have e6 := congrFun E6 x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, Pi.zero_apply, smul_eq_mul] at e1 e2 e3 e4 e5 e6 ⊢
    linear_combination e4 + Complex.I * e5 - e1 - Complex.I * e2 + e3 - e6

  have hskewΦ : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
      ∀ f g, IsVacTh ψ θ S T (sS τ) (sT τ) τ f → IsVacTh ψ θ S T (sS τ) (sT τ) τ g →
        ∫ w in 𝓕, Φ f w * starRingEnd ℂ (g w) ∂μ = -∫ w in 𝓕, f w * starRingEnd ℂ (Φ g w) ∂μ := by
    intro μ 𝓕 hcov f g hf hg
    obtain ⟨hs, adj1, adj2⟩ := int_sesq_adj hT hL hC hLine hP hcov
    have hvac0 : ∀ F, IsFockVacAt (heisO ψ S T) θ τ Jt F → ∀ k : Fin T.rank × Fin S.rank, aM (τ, k.1, k.2) F = 0 := by
      intro F hF k
      funext x
      have := congrFun (hF (unitMap (BS τ) (BT τ) k.1 k.2)) x
      simp only [haM, aMinusAll, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [show annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (unitMap (BS τ) (BT τ) k.1 k.2) F x = 0 from this,
        mul_zero]
    obtain ⟨e1, -⟩ := quadratic_operator_orthogonal hccr hs adj1 adj2 τ N hf.1 hg.1 (hvac0 f hf.2) (hvac0 g hg.2)
    obtain ⟨-, e2⟩ := quadratic_operator_orthogonal hccr hs adj1 adj2 τ N hf.1 hg.1 (hvac0 f hf.2) (hvac0 g hg.2)
    have eδ : ipF μ 𝓕 (δ f) g = -ipF μ 𝓕 f (δ g) :=
      hSk hLine ψ θ S T χS χT om hinf hW τ XS XT hXS hXT μ 𝓕 hcov f g hf.1 hg.1
    have hΦe : ∀ F, Φ F = δ F + (-1 : ℂ) • q1 F := fun F => by
      simp only [hΦ, neg_one_smul, sub_eq_add_neg]
    have lΦ : ipF μ 𝓕 (Φ f) g = ipF μ 𝓕 (δ f) g - ipF μ 𝓕 (q1 f) g := by
      rw [hΦe, ((hs _ _ _ (-1) (hδth f hf.1) (hq1th f hf.1) hg.1)).1]
      ring
    have rΦ : ipF μ 𝓕 f (Φ g) = ipF μ 𝓕 f (δ g) - ipF μ 𝓕 f (q1 g) := by
      rw [hΦe, ((hs _ _ _ (-1) (hδth g hg.1) (hq1th g hg.1) hf.1)).2]
      simp only [map_neg, map_one]
      ring
    show ipF μ 𝓕 (Φ f) g = -ipF μ 𝓕 f (Φ g)
    rw [lΦ, rΦ, e1, e2, sub_zero, sub_zero]
    exact eδ
  obtain ⟨κ, hκ⟩ := hV hLine ψ θ S T sS sT BS BT pS pT hP τ Φ hΦvac hΦlin hΦheis hskewΦ

  have hkey : ∀ f, IsVacTh ψ θ S T (sS τ) (sT τ) τ f → ∀ (l : FVar D T.rank S.rank) P,
      δ (aP l (pt f P)) - aP l (δ (pt f P)) = pt f (Q (MvPolynomial.X l * P) - MvPolynomial.X l * Q P) := by
    intro f hf l P
    obtain ⟨τ', i, c⟩ := l
    have hFt := hpt_mem f hf.1 P
    have hex : ∀ G, aP (τ', i, c) G = ((fockScale D τ' : ℂ)⁻¹) • dRho (heisO ψ S T) θ τ' (unitMap (BS τ') (BT τ') i c) G +
        (-((fockScale D τ' : ℂ)⁻¹) * Complex.I) •
          dRho (heisO ψ S T) θ τ' (cplxO (sS τ') (sT τ') (unitMap (BS τ') (BT τ') i c)) G :=
      fun G => aPlusAll_eq _ θ _ BS BT (τ', i, c) G
    rw [hex, hex, hδlin _ _ _ _ (hd _ _ _ hFt) (hd _ _ _ hFt)]
    have h1 := hdr τ' (unitMap (BS τ') (BT τ') i c) _ hFt
    have h2 := hdr τ' (cplxO (sS τ') (sT τ') (unitMap (BS τ') (BT τ') i c)) _ hFt
    by_cases hτ : τ' = τ
    · subst τ'
      rw [if_pos rfl] at h1 h2
      have hcr : ∀ R, MvPolynomial.X ((τ, i, c) : FVar D T.rank S.rank) * R =
          MvPolynomial.C ((fockScale D τ : ℂ)⁻¹) * Dz (unitMap (BS τ) (BT τ) i c) R +
            MvPolynomial.C (-((fockScale D τ : ℂ)⁻¹) * Complex.I) * Dz (Jt (unitMap (BS τ) (BT τ) i c)) R :=
        fun R => (creaPol hF (hP.onbS τ) (hP.onbT τ) τ i c R).symm
      have hpol : Q (MvPolynomial.X (τ, i, c) * P) - MvPolynomial.X (τ, i, c) * Q P =
          MvPolynomial.C ((fockScale D τ : ℂ)⁻¹) * Dz (A (unitMap (BS τ) (BT τ) i c)) P +
            MvPolynomial.C (-((fockScale D τ : ℂ)⁻¹) * Complex.I) * Dz (A (Jt (unitMap (BS τ) (BT τ) i c))) P := by
        rw [hcr P, hcr (Q P), hQlin, ← ha, ← ha]
        ring
      rw [hpol, map_add, hpt, pt_C_mul, pt_C_mul]
      rw [← hb f hf.1 hf.2, ← hb f hf.1 hf.2, ← h1, ← h2]
      funext x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [if_neg hτ] at h1 h2
      have hpol : Q (MvPolynomial.X (τ', i, c) * P) - MvPolynomial.X (τ', i, c) * Q P = 0 := by
        rw [hQ, quadOp_X_far τ τ' hτ, sub_self]
      rw [hpol, map_zero]
      funext x
      have e1 := congrFun h1 x
      have e2 := congrFun h2 x
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at e1 e2 ⊢
      linear_combination ((fockScale D τ' : ℂ)⁻¹) * e1 + (-((fockScale D τ' : ℂ)⁻¹) * Complex.I) * e2
  refine ⟨κ, fun f hft hvac P x => ?_⟩
  have hf : IsVacTh ψ θ S T (sS τ) (sT τ) τ f := ⟨hft, hvac⟩
  have hΦf : δ f = q1 f + κ • f := by
    have := hκ f hf
    simp only [hΦ] at this
    rw [← this]
    abel
  have hind : ∀ P, δ (pt f P) = pt f (Q P) + κ • pt f P := by
    intro P
    induction P using MvPolynomial.induction_on
    next a =>
      have eC : Q (MvPolynomial.C a) = MvPolynomial.C a * Q 1 := by
        rw [hQ, ← quadOp_C_mul, mul_one]
      have eδ : δ (a • f) = a • δ f := by simpa using hδlin f f a 0 hft hft
      rw [eC, hpt]
      simp only
      rw [pt_C_mul, pt_C, eδ, hΦf]
      have := hq1pt f hft
      simp only [hpt] at this
      rw [this, smul_add, smul_comm]
    next p q hp hq =>
      have eQ : Q (p + q) = Q p + Q q := by rw [hQ]; exact quadOp_add _ _ _ _ _ _ _ _ _ p q
      have eδ := hδlin _ _ 1 1 (hpt_mem f hft p) (hpt_mem f hft q)
      simp only [one_smul] at eδ
      rw [eQ, map_add, map_add, eδ, hp, hq, smul_add]
      abel
    next p l hp =>
      rw [mul_comm p, hptX f hft]
      have e1 := hkey f hf l p
      rw [sub_eq_iff_eq_add] at e1
      rw [e1, hp, hccr.linP l κ _ _ (hpt_mem f hft _) (hpt_mem f hft p), ← hptX f hft, ← hptX f hft, map_sub]
      abel
  have hd0 := (hdiff _ (hpt_mem f hft P) x).hasDerivAt
  have e : pt f (Q P + κ • P) x = δ (pt f P) x := by
    rw [map_add, map_smul, hind P]
  rw [e]
  exact hd0

end Assembly

section FCoordPf

theorem fCoordFacts : FCoordFacts := by
  intro m n pS pT GS sS BS GT sT BT hS hT
  obtain ⟨εS, hεS, h1S, h2S, hsS, -⟩ := Formalism.IndefR.Fock.Alg.onb_data hS
  obtain ⟨εT, hεT, h1T, h2T, hsT, -⟩ := Formalism.IndefR.Fock.Alg.onb_data hT
  have key : ∀ z : Matrix (Fin m) (Fin n) ℂ, BT⁻¹ * cplxO sS sT z * BS =
      Complex.I • (diagonal (fun a => (εT a : ℂ)) * (BT⁻¹ * z * BS) * diagonal (fun a => (εS a : ℂ))) := by
    intro z
    unfold cplxO
    rw [hsS, hsT]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc BT⁻¹ BT, h1T, Matrix.one_mul, h1S, Matrix.mul_one]
  refine ⟨fun z k => ?_, fun i c k => ?_⟩
  · unfold fCoord
    rw [key]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_diagonal, Matrix.diagonal_mul]
    have hp := Formalism.IndefR.Fock.Alg.eps_prod hεS hεT k.1 k.2
    split_ifs with h
    · rw [if_pos h] at hp
      linear_combination (Complex.I * (BT⁻¹ * z * BS) k.1 k.2) * hp
    · rw [if_neg h] at hp
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      linear_combination (-Complex.I * starRingEnd ℂ ((BT⁻¹ * z * BS) k.1 k.2)) * hp
  · have e : BT⁻¹ * unitMap BS BT i c * BS = Matrix.single i c 1 := by
      unfold unitMap
      simp only [Matrix.mul_assoc]
      rw [h1S, Matrix.mul_one, ← Matrix.mul_assoc, h1T, Matrix.one_mul]
    unfold fCoord
    rw [e]
    obtain ⟨a, b⟩ := k
    by_cases hk : (a, b) = (i, c)
    · simp only [Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      simp
    · have hk' : ¬ (i = a ∧ c = b) := fun h => hk (by rw [h.1, h.2])
      simp [Matrix.single_apply, hk', hk]

end FCoordPf

section Coords

variable {m n : ℕ}

def twF (pS pT : ℕ) (k : Fin m × Fin n) (c : ℂ) : ℂ := if PosF pS pT k.1 k.2 then c else starRingEnd ℂ c

theorem fCoord_add (BS : Matrix (Fin n) (Fin n) ℂ) (BT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ)
    (z z' : Matrix (Fin m) (Fin n) ℂ) (k : Fin m × Fin n) :
    fCoord BS BT pS pT (z + z') k = fCoord BS BT pS pT z k + fCoord BS BT pS pT z' k := by
  simp only [fCoord, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
  split_ifs <;> simp

theorem fCoord_smul (BS : Matrix (Fin n) (Fin n) ℂ) (BT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ) (c : ℂ)
    (z : Matrix (Fin m) (Fin n) ℂ) (k : Fin m × Fin n) :
    fCoord BS BT pS pT (c • z) k = twF pS pT k c * fCoord BS BT pS pT z k := by
  simp only [fCoord, twF, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem twF_ofReal (pS pT : ℕ) (k : Fin m × Fin n) (r : ℝ) : twF pS pT k (r : ℂ) = r := by
  simp only [twF]; split_ifs <;> simp

theorem fCoord_sub (BS : Matrix (Fin n) (Fin n) ℂ) (BT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ)
    (z z' : Matrix (Fin m) (Fin n) ℂ) (k : Fin m × Fin n) :
    fCoord BS BT pS pT (z - z') k = fCoord BS BT pS pT z k - fCoord BS BT pS pT z' k := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ z', fCoord_add, fCoord_smul]
  simp only [twF]; split_ifs <;> simp <;> ring

theorem fCoord_half (BS : Matrix (Fin n) (Fin n) ℂ) (BT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ)
    (z : Matrix (Fin m) (Fin n) ℂ) (k : Fin m × Fin n) :
    fCoord BS BT pS pT ((1 / 2 : ℂ) • z) k = (1 / 2) * fCoord BS BT pS pT z k := by
  rw [fCoord_smul, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, twF_ofReal]

theorem fCoord_sum {β : Type} (BS : Matrix (Fin n) (Fin n) ℂ) (BT : Matrix (Fin m) (Fin m) ℂ) (pS pT : ℕ)
    (s : Finset β) (z : β → Matrix (Fin m) (Fin n) ℂ) (k : Fin m × Fin n) :
    fCoord BS BT pS pT (∑ b ∈ s, z b) k = ∑ b ∈ s, fCoord BS BT pS pT (z b) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fCoord]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fCoord_add, ih]

theorem adX_add (XS : Matrix (Fin n) (Fin n) ℂ) (XT : Matrix (Fin m) (Fin m) ℂ) (z z' : Matrix (Fin m) (Fin n) ℂ) :
    adX XS XT (z + z') = adX XS XT z + adX XS XT z' := by
  simp only [adX, Matrix.mul_add, Matrix.add_mul]; abel

theorem adX_smul (XS : Matrix (Fin n) (Fin n) ℂ) (XT : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (z : Matrix (Fin m) (Fin n) ℂ) : adX XS XT (c • z) = c • adX XS XT z := by
  simp only [adX, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

theorem adX_sum {β : Type} (XS : Matrix (Fin n) (Fin n) ℂ) (XT : Matrix (Fin m) (Fin m) ℂ) (s : Finset β)
    (z : β → Matrix (Fin m) (Fin n) ℂ) : adX XS XT (∑ b ∈ s, z b) = ∑ b ∈ s, adX XS XT (z b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [adX]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, adX_add, ih]

theorem expand_unit {pS pT : ℕ} {GS sS BS : Matrix (Fin n) (Fin n) ℂ} {GT sT BT : Matrix (Fin m) (Fin m) ℂ}
    (hS : IsONBasis GS sS BS pS) (hT : IsONBasis GT sT BT pT) (z : Matrix (Fin m) (Fin n) ℂ) :
    z = ∑ l : Fin m × Fin n, ((((fCoord BS BT pS pT z l).re : ℝ) : ℂ) • unitMap BS BT l.1 l.2 +
      (((fCoord BS BT pS pT z l).im : ℝ) : ℂ) • cplxO sS sT (unitMap BS BT l.1 l.2)) := by
  obtain ⟨-, -, h1S, h2S, -⟩ := Formalism.IndefR.Fock.Alg.onb_data hS
  obtain ⟨-, -, h1T, h2T, -⟩ := Formalism.IndefR.Fock.Alg.onb_data hT
  have hterm : ∀ l : Fin m × Fin n, ((((fCoord BS BT pS pT z l).re : ℝ) : ℂ) • unitMap BS BT l.1 l.2 +
      (((fCoord BS BT pS pT z l).im : ℝ) : ℂ) • cplxO sS sT (unitMap BS BT l.1 l.2)) =
      BT * ((BT⁻¹ * z * BS) l.1 l.2 • Matrix.single l.1 l.2 (1 : ℂ)) * BS⁻¹ := by
    intro l
    rw [Formalism.IndefR.Fock.Alg.J_unit hS hT, smul_smul, ← add_smul, unitMap, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    unfold fCoord
    split_ifs
    · exact Complex.re_add_im _
    · simp only [Complex.conj_re, Complex.conj_im, Complex.ofReal_neg, neg_mul_neg]
      exact Complex.re_add_im _
  rw [Finset.sum_congr rfl fun l _ => hterm l, ← Matrix.sum_mul, ← Matrix.mul_sum]
  have hW : ∀ W : Matrix (Fin m) (Fin n) ℂ, ∑ l : Fin m × Fin n, W l.1 l.2 • Matrix.single l.1 l.2 (1 : ℂ) = W := by
    intro W
    ext i c
    rw [Matrix.sum_apply, Finset.sum_eq_single (i, c)]
    · simp [Matrix.single_apply]
    · intro b _ hb
      simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      rw [if_neg]
      · simp
      · rintro ⟨h1, h2⟩
        exact hb (Prod.ext h1 h2)
    · simp
  rw [hW]
  simp only [Matrix.mul_assoc, h2S, Matrix.mul_one]
  rw [← Matrix.mul_assoc, h2T, Matrix.one_mul]

theorem coord_adX {pS pT : ℕ} {GS sS BS XS : Matrix (Fin n) (Fin n) ℂ} {GT sT BT XT : Matrix (Fin m) (Fin m) ℂ}
    (hS : IsONBasis GS sS BS pS) (hT : IsONBasis GT sT BT pT) (z : Matrix (Fin m) (Fin n) ℂ) (k : Fin m × Fin n) :
    fCoord BS BT pS pT (adX XS XT z) k = ∑ l : Fin m × Fin n,
      (mCoef sS BS XS sT BT XT pS pT k l * fCoord BS BT pS pT z l +
        nCoef sS BS XS sT BT XT pS pT k l * starRingEnd ℂ (fCoord BS BT pS pT z l)) := by
  obtain ⟨hJ, -⟩ := fCoordFacts m n pS pT GS sS BS GT sT BT hS hT
  conv_lhs => rw [expand_unit hS hT z]
  rw [adX_sum, fCoord_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [adX_add, adX_smul, adX_smul, fCoord_add, fCoord_smul, fCoord_smul, twF_ofReal, twF_ofReal]
  have hM : mCoef sS BS XS sT BT XT pS pT k l = (1 / 2) * (fCoord BS BT pS pT (adX XS XT (unitMap BS BT l.1 l.2)) k -
      Complex.I * fCoord BS BT pS pT (adX XS XT (cplxO sS sT (unitMap BS BT l.1 l.2))) k) := by
    rw [mCoef, fCoord_half, fCoord_sub, hJ]
  have hN : nCoef sS BS XS sT BT XT pS pT k l = (1 / 2) * (fCoord BS BT pS pT (adX XS XT (unitMap BS BT l.1 l.2)) k +
      Complex.I * fCoord BS BT pS pT (adX XS XT (cplxO sS sT (unitMap BS BT l.1 l.2))) k) := by
    rw [nCoef, fCoord_half, fCoord_add, hJ]
  rw [hM, hN]
  set ζ := fCoord BS BT pS pT z l
  have hζ : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
  have hcζ : starRingEnd ℂ ζ = (ζ.re : ℂ) - (ζ.im : ℂ) * Complex.I := by
    conv_lhs => rw [hζ]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hcζ]
  linear_combination (-(1 / 2) * (fCoord BS BT pS pT (adX XS XT (unitMap BS BT l.1 l.2)) k -
      Complex.I * fCoord BS BT pS pT (adX XS XT (cplxO sS sT (unitMap BS BT l.1 l.2))) k)) * hζ +
    ((ζ.im : ℂ) * fCoord BS BT pS pT (adX XS XT (cplxO sS sT (unitMap BS BT l.1 l.2))) k) * Complex.I_sq

theorem mn_F {pS pT : ℕ} {GS sS BS XS : Matrix (Fin n) (Fin n) ℂ} {GT sT BT XT : Matrix (Fin m) (Fin m) ℂ}
    (hS : IsONBasis GS sS BS pS) (hT : IsONBasis GT sT BT pT) (k l : Fin m × Fin n) :
    mCoef sS BS XS sT BT XT pS pT k l =
      (if (PosF pS pT k.1 k.2 ↔ PosF pS pT l.1 l.2) then fCoord BS BT pS pT (adX XS XT (unitMap BS BT l.1 l.2)) k else 0) ∧
    nCoef sS BS XS sT BT XT pS pT k l =
      (if (PosF pS pT k.1 k.2 ↔ PosF pS pT l.1 l.2) then 0 else fCoord BS BT pS pT (adX XS XT (unitMap BS BT l.1 l.2)) k) := by
  obtain ⟨hJ, -⟩ := fCoordFacts m n pS pT GS sS BS GT sT BT hS hT
  have hJu := Formalism.IndefR.Fock.Alg.J_unit hS hT l.1 l.2
  rw [mCoef, nCoef, fCoord_half, fCoord_half, fCoord_sub, fCoord_add, hJ, hJu, adX_smul, fCoord_smul]
  simp only [twF]
  by_cases hk : PosF pS pT k.1 k.2 <;> by_cases hl : PosF pS pT l.1 l.2 <;>
    simp only [hk, hl, if_true, if_false, iff_self, iff_true, true_iff, iff_false, false_iff, not_true_eq_false,
      not_false_eq_true, map_neg, Complex.conj_I] <;>
    constructor <;>
    first
      | linear_combination (-(fCoord BS BT pS pT (adX XS XT (unitMap BS BT l.1 l.2)) k / 2)) * Complex.I_sq
      | linear_combination (fCoord BS BT pS pT (adX XS XT (unitMap BS BT l.1 l.2)) k / 2) * Complex.I_sq

end Coords

section QuadGen

variable {σ K : Type} [DecidableEq σ] [Fintype K] [DecidableEq K]

theorem pderiv_comm' (i j : σ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    simp only [MvPolynomial.pderiv_monomial]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [tsub_tsub, tsub_tsub, add_comm (Finsupp.single i 1)]
      congr 1
      simp only [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hij, if_neg (Ne.symm hij), tsub_zero]
      ring
  | add p q hp hq => simp only [map_add, hp, hq]

theorem pderiv_X_mul' (a b : σ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.pderiv a (MvPolynomial.X b * P) =
      MvPolynomial.X b * MvPolynomial.pderiv a P + (if b = a then P else 0) := by
  rw [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, smul_eq_mul, smul_eq_mul]
  split_ifs <;> simp

theorem pderiv_CX_mul' (a : ℂ) (b c : σ) (R : MvPolynomial σ ℂ) :
    MvPolynomial.pderiv c (MvPolynomial.C a * MvPolynomial.X b * R) =
      MvPolynomial.C a * (MvPolynomial.X b * MvPolynomial.pderiv c R + if b = c then R else 0) := by
  rw [mul_assoc, MvPolynomial.pderiv_C_mul, pderiv_X_mul']

theorem pderiv_CX_mul (a : ℂ) (b c : σ) (R : MvPolynomial σ ℂ) :
    MvPolynomial.pderiv c (MvPolynomial.C a * MvPolynomial.X b * R) =
      MvPolynomial.C a * (MvPolynomial.X b * MvPolynomial.pderiv c R + if b = c then R else 0) :=
  pderiv_CX_mul' a b c R

theorem pderiv_CXX_mul (a : ℂ) (b b' c : σ) (R : MvPolynomial σ ℂ) :
    MvPolynomial.pderiv c (MvPolynomial.C a * MvPolynomial.X b * MvPolynomial.X b' * R) =
      MvPolynomial.C a * (MvPolynomial.X b * (MvPolynomial.X b' * MvPolynomial.pderiv c R + if b' = c then R else 0) +
        if b = c then MvPolynomial.X b' * R else 0) := by
  rw [mul_assoc (MvPolynomial.C a * MvPolynomial.X b), pderiv_CX_mul, pderiv_X_mul']

def qGen (ι : K → σ) (M N : K → K → ℂ) (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ k, ∑ l, (MvPolynomial.C (M k l) * MvPolynomial.X (ι k) * MvPolynomial.pderiv (ι l) P +
    MvPolynomial.C (N k l / 2) * MvPolynomial.X (ι k) * MvPolynomial.X (ι l) * P -
    MvPolynomial.C (starRingEnd ℂ (N k l) / 2) * MvPolynomial.pderiv (ι k) (MvPolynomial.pderiv (ι l) P))

def dGen (ι : K → σ) (c d : K → ℂ) (P : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ k, (MvPolynomial.C (c k) * MvPolynomial.X (ι k) * P - MvPolynomial.C (d k) * MvPolynomial.pderiv (ι k) P)

theorem qGen_add (ι : K → σ) (M N : K → K → ℂ) (P P' : MvPolynomial σ ℂ) :
    qGen ι M N (P + P') = qGen ι M N P + qGen ι M N P' := by
  simp only [qGen, map_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem qGen_C_mul (ι : K → σ) (M N : K → K → ℂ) (a : ℂ) (P : MvPolynomial σ ℂ) :
    qGen ι M N (MvPolynomial.C a * P) = MvPolynomial.C a * qGen ι M N P := by
  simp only [qGen, Finset.mul_sum, MvPolynomial.pderiv_C_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem qGen_sub (ι : K → σ) (M N : K → K → ℂ) (P P' : MvPolynomial σ ℂ) :
    qGen ι M N (P - P') = qGen ι M N P - qGen ι M N P' := by
  have h := qGen_add ι M N (P - P') P'
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem qGen_sum {β : Type} (ι : K → σ) (M N : K → K → ℂ) (s : Finset β) (f : β → MvPolynomial σ ℂ) :
    qGen ι M N (∑ b ∈ s, f b) = ∑ b ∈ s, qGen ι M N (f b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using qGen_C_mul ι M N 0 0
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, qGen_add, ih]

theorem qGen_X (ι : K → σ) (hι : Function.Injective ι) (M N : K → K → ℂ) (j : K) (P : MvPolynomial σ ℂ) :
    qGen ι M N (MvPolynomial.X (ι j) * P) - MvPolynomial.X (ι j) * qGen ι M N P =
      ∑ k, (MvPolynomial.C (M k j) * MvPolynomial.X (ι k) * P -
        MvPolynomial.C (starRingEnd ℂ (N j k) / 2) * MvPolynomial.pderiv (ι k) P -
        MvPolynomial.C (starRingEnd ℂ (N k j) / 2) * MvPolynomial.pderiv (ι k) P) := by
  have term : ∀ k l, (MvPolynomial.C (M k l) * MvPolynomial.X (ι k) *
      MvPolynomial.pderiv (ι l) (MvPolynomial.X (ι j) * P) +
      MvPolynomial.C (N k l / 2) * MvPolynomial.X (ι k) * MvPolynomial.X (ι l) * (MvPolynomial.X (ι j) * P) -
      MvPolynomial.C (starRingEnd ℂ (N k l) / 2) *
        MvPolynomial.pderiv (ι k) (MvPolynomial.pderiv (ι l) (MvPolynomial.X (ι j) * P))) -
      MvPolynomial.X (ι j) * (MvPolynomial.C (M k l) * MvPolynomial.X (ι k) * MvPolynomial.pderiv (ι l) P +
        MvPolynomial.C (N k l / 2) * MvPolynomial.X (ι k) * MvPolynomial.X (ι l) * P -
        MvPolynomial.C (starRingEnd ℂ (N k l) / 2) * MvPolynomial.pderiv (ι k) (MvPolynomial.pderiv (ι l) P)) =
      (if l = j then MvPolynomial.C (M k j) * MvPolynomial.X (ι k) * P else 0) -
      (if k = j then MvPolynomial.C (starRingEnd ℂ (N j l) / 2) * MvPolynomial.pderiv (ι l) P else 0) -
      (if l = j then MvPolynomial.C (starRingEnd ℂ (N k j) / 2) * MvPolynomial.pderiv (ι k) P else 0) := by
    intro k l
    rw [pderiv_X_mul' (ι l) (ι j) P, map_add, pderiv_X_mul' (ι k) (ι j)]
    simp only [hι.eq_iff]
    by_cases hl : j = l <;> by_cases hk : j = k
    · subst hl; subst hk; simp; ring
    · subst hl; simp [Ne.symm hk, hk]; ring
    · subst hk; simp [Ne.symm hl, hl]; ring
    · simp [Ne.symm hl, hl, Ne.symm hk, hk]; ring
  unfold qGen
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, term]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun k l => if k = j then _ else _)]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem qGen_D (ι : K → σ) (hι : Function.Injective ι) (M N : K → K → ℂ) (j : K) (P : MvPolynomial σ ℂ) :
    qGen ι M N (MvPolynomial.pderiv (ι j) P) - MvPolynomial.pderiv (ι j) (qGen ι M N P) =
      ∑ k, (-(MvPolynomial.C (M j k) * MvPolynomial.pderiv (ι k) P) -
        MvPolynomial.C (N j k / 2) * MvPolynomial.X (ι k) * P - MvPolynomial.C (N k j / 2) * MvPolynomial.X (ι k) * P) := by
  have term : ∀ k l, (MvPolynomial.C (M k l) * MvPolynomial.X (ι k) *
      MvPolynomial.pderiv (ι l) (MvPolynomial.pderiv (ι j) P) +
      MvPolynomial.C (N k l / 2) * MvPolynomial.X (ι k) * MvPolynomial.X (ι l) * MvPolynomial.pderiv (ι j) P -
      MvPolynomial.C (starRingEnd ℂ (N k l) / 2) *
        MvPolynomial.pderiv (ι k) (MvPolynomial.pderiv (ι l) (MvPolynomial.pderiv (ι j) P))) -
      MvPolynomial.pderiv (ι j) (MvPolynomial.C (M k l) * MvPolynomial.X (ι k) * MvPolynomial.pderiv (ι l) P +
        MvPolynomial.C (N k l / 2) * MvPolynomial.X (ι k) * MvPolynomial.X (ι l) * P -
        MvPolynomial.C (starRingEnd ℂ (N k l) / 2) * MvPolynomial.pderiv (ι k) (MvPolynomial.pderiv (ι l) P)) =
      -(if k = j then MvPolynomial.C (M j l) * MvPolynomial.pderiv (ι l) P else 0) -
      (if k = j then MvPolynomial.C (N j l / 2) * MvPolynomial.X (ι l) * P else 0) -
      (if l = j then MvPolynomial.C (N k j / 2) * MvPolynomial.X (ι k) * P else 0) := by
    intro k l
    rw [map_sub, map_add, pderiv_CX_mul, pderiv_CXX_mul, MvPolynomial.pderiv_C_mul, pderiv_comm' (ι j) (ι k),
      pderiv_comm' (ι j) (ι l)]
    simp only [hι.eq_iff]
    split_ifs <;> subst_vars <;> ring
  unfold qGen
  rw [map_sum, ← Finset.sum_sub_distrib]
  simp only [map_sum, ← Finset.sum_sub_distrib, term]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [Finset.sum_comm (f := fun k l => if k = j then MvPolynomial.C (M j l) * _ else 0),
    Finset.sum_comm (f := fun k l => if k = j then MvPolynomial.C (N j l / 2) * _ * P else 0)]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem qGen_dGen (ι : K → σ) (hι : Function.Injective ι) (M N : K → K → ℂ) (c d c' d' : K → ℂ)
    (hc : ∀ k, c' k = ∑ j, (M k j * c j + (N k j + N j k) / 2 * d j))
    (hd : ∀ k, d' k = ∑ j, ((starRingEnd ℂ (N k j) + starRingEnd ℂ (N j k)) / 2 * c j - M j k * d j))
    (P : MvPolynomial σ ℂ) :
    qGen ι M N (dGen ι c d P) - dGen ι c d (qGen ι M N P) = dGen ι c' d' P := by
  have e1 : qGen ι M N (dGen ι c d P) - dGen ι c d (qGen ι M N P) =
      ∑ j, (MvPolynomial.C (c j) * (qGen ι M N (MvPolynomial.X (ι j) * P) - MvPolynomial.X (ι j) * qGen ι M N P) -
        MvPolynomial.C (d j) * (qGen ι M N (MvPolynomial.pderiv (ι j) P) -
          MvPolynomial.pderiv (ι j) (qGen ι M N P))) := by
    unfold dGen
    rw [qGen_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [qGen_sub, show MvPolynomial.C (c j) * MvPolynomial.X (ι j) * P = MvPolynomial.C (c j) * (MvPolynomial.X (ι j) * P) by ring,
      qGen_C_mul, qGen_C_mul]
    ring
  rw [e1]
  simp only [qGen_X ι hι, qGen_D ι hι, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  unfold dGen
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hc k, hd k, map_sum, map_sum]
  simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [add_div, map_add, map_sub, map_mul, map_neg]
  ring

end QuadGen

section QuadPf

variable {m n : ℕ}

theorem lie_entry {k p : ℕ} {G s B X : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G s B p)
    (hX : Xᴴ * G + G * X = 0) :
    ∃ ε : Fin k → ℝ, (∀ a, (ε a = 1 ∧ a.val < p) ∨ (ε a = -1 ∧ p ≤ a.val)) ∧
      ∀ a b, (B⁻¹ * X * B) a b = -((ε a : ℂ) * ε b) * starRingEnd ℂ ((B⁻¹ * X * B) b a) := by
  obtain ⟨ε, hε, h1, h2, hs, hG, -⟩ := Formalism.IndefR.Fock.Alg.onb_data h
  refine ⟨ε, hε, fun a b => ?_⟩
  have hε2 : ∀ a, (ε a : ℂ) * ε a = 1 := fun a => by rcases hε a with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have h3 : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Bᴴ * (B⁻¹ᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one, Matrix.one_mul]
  have h1' : ∀ Z : Matrix (Fin k) (Fin k) ℂ, B⁻¹ * (B * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hY : (B⁻¹ * X * B)ᴴ * diagonal (fun a => (ε a : ℂ)) + diagonal (fun a => (ε a : ℂ)) * (B⁻¹ * X * B) = 0 := by
    have e : (B⁻¹ * X * B)ᴴ * diagonal (fun a => (ε a : ℂ)) + diagonal (fun a => (ε a : ℂ)) * (B⁻¹ * X * B) =
        Bᴴ * (Xᴴ * G + G * X) * B := by
      rw [hG]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h1, Matrix.mul_one, h3]
    rw [e, hX, Matrix.mul_zero, Matrix.zero_mul]
  have := congrFun (congrFun hY a) b
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, Complex.star_def] at this
  linear_combination (ε a : ℂ) * this - (B⁻¹ * X * B) a b * hε2 a

theorem sum_single_mul {p q r : ℕ} (Y : Matrix (Fin p) (Fin q) ℂ) (j : Fin q) (d : Fin r) (i : Fin p) (c : Fin r) :
    (Y * Matrix.single j d (1 : ℂ)) i c = if d = c then Y i j else 0 := by
  by_cases hdc : d = c <;> simp [Matrix.mul_apply, Matrix.single_apply, hdc]

theorem single_mul_sum {p q r : ℕ} (Y : Matrix (Fin q) (Fin r) ℂ) (j : Fin p) (d : Fin q) (i : Fin p) (c : Fin r) :
    (Matrix.single j d (1 : ℂ) * Y) i c = if j = i then Y d c else 0 := by
  by_cases hji : j = i <;> simp [Matrix.mul_apply, Matrix.single_apply, hji]

theorem mn_skew_sym {pS pT : ℕ} {GS sS BS XS : Matrix (Fin n) (Fin n) ℂ} {GT sT BT XT : Matrix (Fin m) (Fin m) ℂ}
    (hS : IsONBasis GS sS BS pS) (hT : IsONBasis GT sT BT pT) (hXS : XSᴴ * GS + GS * XS = 0)
    (hXT : XTᴴ * GT + GT * XT = 0) (k l : Fin m × Fin n) :
    mCoef sS BS XS sT BT XT pS pT l k = -starRingEnd ℂ (mCoef sS BS XS sT BT XT pS pT k l) ∧
      nCoef sS BS XS sT BT XT pS pT l k = nCoef sS BS XS sT BT XT pS pT k l := by
  obtain ⟨εS, hεS, hYS⟩ := lie_entry hS hXS
  obtain ⟨εT, hεT, hYT⟩ := lie_entry hT hXT
  obtain ⟨-, -, h1S, h2S, -⟩ := Formalism.IndefR.Fock.Alg.onb_data hS
  obtain ⟨-, -, h1T, h2T, -⟩ := Formalism.IndefR.Fock.Alg.onb_data hT
  have hεS2 : ∀ a, (εS a : ℂ) * εS a = 1 := fun a => by rcases hεS a with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hεT2 : ∀ a, (εT a : ℂ) * εT a = 1 := fun a => by rcases hεT a with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hW : ∀ l : Fin m × Fin n, BT⁻¹ * adX XS XT (unitMap BS BT l.1 l.2) * BS =
      (BT⁻¹ * XT * BT) * Matrix.single l.1 l.2 (1 : ℂ) - Matrix.single l.1 l.2 (1 : ℂ) * (BS⁻¹ * XS * BS) := by
    intro l
    simp only [adX, unitMap, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [h1S, Matrix.mul_one, ← Matrix.mul_assoc BT⁻¹ BT, h1T, Matrix.one_mul]

  have ha : ∀ k l : Fin m × Fin n, (BT⁻¹ * adX XS XT (unitMap BS BT l.1 l.2) * BS) k.1 k.2 =
      (if l.2 = k.2 then (BT⁻¹ * XT * BT) k.1 l.1 else 0) - (if l.1 = k.1 then (BS⁻¹ * XS * BS) l.2 k.2 else 0) := by
    intro k l
    rw [hW, Matrix.sub_apply, sum_single_mul, single_mul_sum]
  have hF : ∀ k l : Fin m × Fin n, fCoord BS BT pS pT (adX XS XT (unitMap BS BT l.1 l.2)) k =
      twF pS pT k ((BT⁻¹ * adX XS XT (unitMap BS BT l.1 l.2) * BS) k.1 k.2) := fun k l => rfl
  have hrel : ∀ k l : Fin m × Fin n, (BT⁻¹ * adX XS XT (unitMap BS BT k.1 k.2) * BS) l.1 l.2 =
      -(((εT l.1 : ℂ) * εS l.2) * ((εT k.1 : ℂ) * εS k.2)) *
        starRingEnd ℂ ((BT⁻¹ * adX XS XT (unitMap BS BT l.1 l.2) * BS) k.1 k.2) := by
    rintro ⟨k1, k2⟩ ⟨l1, l2⟩
    rw [ha, ha]
    dsimp only
    by_cases h2 : k2 = l2 <;> by_cases h1 : k1 = l1
    · subst h2; subst h1
      simp only [if_true, map_sub, Complex.conj_ofReal]
      linear_combination hYT k1 k1 - hYS k2 k2 +
        ((εT k1 : ℂ) * εT k1 * starRingEnd ℂ ((BT⁻¹ * XT * BT) k1 k1)) * hεS2 k2 -
        ((εS k2 : ℂ) * εS k2 * starRingEnd ℂ ((BS⁻¹ * XS * BS) k2 k2)) * hεT2 k1
    · subst h2
      simp only [if_true, if_neg h1, if_neg (Ne.symm h1), sub_zero, Complex.conj_ofReal]
      linear_combination hYT l1 k1 + ((εT l1 : ℂ) * εT k1 * starRingEnd ℂ ((BT⁻¹ * XT * BT) k1 l1)) * hεS2 k2
    · subst h1
      simp only [if_true, if_neg h2, if_neg (Ne.symm h2), zero_sub, map_neg, Complex.conj_ofReal]
      linear_combination (-1 : ℂ) * hYS k2 l2 -
        ((εS k2 : ℂ) * εS l2 * starRingEnd ℂ ((BS⁻¹ * XS * BS) l2 k2)) * hεT2 k1
    · simp only [if_neg h1, if_neg (Ne.symm h1), if_neg h2, if_neg (Ne.symm h2), sub_zero, map_zero, mul_zero]
  have he : ∀ k : Fin m × Fin n, ((εT k.1 : ℂ) * εS k.2) = if PosF pS pT k.1 k.2 then 1 else -1 :=
    fun k => Formalism.IndefR.Fock.Alg.eps_prod hεS hεT k.1 k.2
  rw [(mn_F hS hT l k).1, (mn_F hS hT k l).1, (mn_F hS hT l k).2, (mn_F hS hT k l).2, hF, hF, hrel k l, he, he]
  simp only [twF]
  by_cases hk : PosF pS pT k.1 k.2 <;> by_cases hl : PosF pS pT l.1 l.2 <;>
    simp [hk, hl, map_neg, map_mul, Complex.conj_conj]

open Classical in

theorem quadCommPol : QuadCommPol D := by
  intro m n pS pT τ GS sS BS XS GT sT BT XT hS hT hXS hXT z P
  have hι : Function.Injective (fun k : Fin m × Fin n => ((τ, k.1, k.2) : FVar D m n)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2.1 h.2.2
  have hq : ∀ P, quadOp τ sS BS XS sT BT XT pS pT P = qGen (fun k : Fin m × Fin n => ((τ, k.1, k.2) : FVar D m n))
      (mCoef sS BS XS sT BT XT pS pT) (nCoef sS BS XS sT BT XT pS pT) P := fun P => rfl
  have hd : ∀ z P, dzPol τ BS BT pS pT z P = MvPolynomial.C ((fockScale D τ : ℂ) / 2) *
      dGen (fun k : Fin m × Fin n => ((τ, k.1, k.2) : FVar D m n)) (fCoord BS BT pS pT z)
        (fun k => starRingEnd ℂ (fCoord BS BT pS pT z k)) P := fun z P => rfl
  rw [hq, hq, hd, hd, hd, qGen_C_mul, ← mul_sub]
  congr 1
  apply qGen_dGen _ hι
  · intro k
    rw [coord_adX hS hT z k]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(mn_skew_sym hS hT hXS hXT k j).2]
    ring
  · intro k
    rw [coord_adX hS hT z k, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(mn_skew_sym hS hT hXS hXT k j).2, (mn_skew_sym hS hT hXS hXT j k).1]
    simp only [map_add, map_mul, map_neg, Complex.conj_conj]
    ring

end QuadPf

section DRhoPf

open Formalism.IndefR.Fock.Alg Formalism.IndefR.Fock.CCR

open Classical in

theorem dRhoPoly_of (hT : ThetaDRho D) (hL : DRhoLin D) (hC : DRhoComm D) : DRhoPoly D := by
  intro hLine ψ θ S T sS sT BS BT pS pT hP τ f hf hvac z P
  have hstd := hP.std
  have hinf := hP.inf
  have hccr := Formalism.IndefR.Fock.Final.ccrTheta_of_drho hT hL hC hLine ψ θ S T sS sT BS BT pS pT hP
  simp only [pureTensorO]
  set aP := aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT with haP
  set aM := aMinusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT with haM
  have hF : IsThetaFunO ψ S T (pureTensorL aP f P) := ccrMemAbs _ aP aM f hccr hf P
  obtain ⟨hadd, hsm, -⟩ := hL ψ θ hstd hinf hLine S T τ
  have hfs : (fockScale D τ : ℂ) ≠ 0 := by exact_mod_cast (fockScale_pos D τ).ne'
  have h0 : ∀ G, IsThetaFunO ψ S T G → dRho (heisO ψ S T) θ τ 0 G = 0 := by
    intro G hG
    have := hadd 0 0 G hG
    rw [add_zero] at this
    have h' : dRho (heisO ψ S T) θ τ 0 G + dRho (heisO ψ S T) θ τ 0 G = dRho (heisO ψ S T) θ τ 0 G + 0 := by
      rw [add_zero]; exact this.symm
    exact add_left_cancel h'
  have hsum : ∀ (s : Finset (Fin T.rank × Fin S.rank)) (g : Fin T.rank × Fin S.rank → Matrix (Fin T.rank) (Fin S.rank) ℂ),
      dRho (heisO ψ S T) θ τ (∑ b ∈ s, g b) (pureTensorL aP f P) =
        ∑ b ∈ s, dRho (heisO ψ S T) θ τ (g b) (pureTensorL aP f P) := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simpa using h0 _ hF
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd _ _ _ hF, ih]

  have hvac' : ∀ l : Fin T.rank × Fin S.rank, aM (τ, l.1, l.2) f = 0 := by
    intro l
    funext x
    have := congrFun (hvac (unitMap (BS τ) (BT τ) l.1 l.2)) x
    simp only [haM, aMinusAll, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [show annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (unitMap (BS τ) (BT τ) l.1 l.2) f x = 0 from this,
      mul_zero]
  have hP1 : ∀ l : Fin T.rank × Fin S.rank, aP (τ, l.1, l.2) (pureTensorL aP f P) =
      pureTensorL aP f (MvPolynomial.X (τ, l.1, l.2) * P) := fun l => (pt_X_mul hccr hf _ P).symm
  have hM1 : ∀ l : Fin T.rank × Fin S.rank, aM (τ, l.1, l.2) (pureTensorL aP f P) =
      pureTensorL aP f (MvPolynomial.pderiv (τ, l.1, l.2) P) := fun l => ccrDerivAt _ aP aM f hccr hf _ (hvac' l) P
  have hu : ∀ l : Fin T.rank × Fin S.rank, dRho (heisO ψ S T) θ τ (unitMap (BS τ) (BT τ) l.1 l.2) (pureTensorL aP f P) =
      ((fockScale D τ : ℂ) / 2) • (pureTensorL aP f (MvPolynomial.X (τ, l.1, l.2) * P) -
        pureTensorL aP f (MvPolynomial.pderiv (τ, l.1, l.2) P)) := by
    intro l
    rw [← hP1, ← hM1]
    funext x
    have e1 := congrFun (aPlusAll_eq (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT (τ, l.1, l.2)
      (pureTensorL aP f P)) x
    have e2 := congrFun (aMinusAll_eq (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT (τ, l.1, l.2)
      (pureTensorL aP f P)) x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e1 e2 ⊢
    rw [show aP (τ, l.1, l.2) (pureTensorL aP f P) x = _ from e1, show aM (τ, l.1, l.2) (pureTensorL aP f P) x = _ from e2]
    field_simp
    ring
  have hJu : ∀ l : Fin T.rank × Fin S.rank, dRho (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ) (unitMap (BS τ) (BT τ) l.1 l.2))
      (pureTensorL aP f P) = ((fockScale D τ : ℂ) / 2 * Complex.I) • (pureTensorL aP f (MvPolynomial.X (τ, l.1, l.2) * P) +
        pureTensorL aP f (MvPolynomial.pderiv (τ, l.1, l.2) P)) := by
    intro l
    rw [← hP1, ← hM1]
    funext x
    have e1 := congrFun (aPlusAll_eq (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT (τ, l.1, l.2)
      (pureTensorL aP f P)) x
    have e2 := congrFun (aMinusAll_eq (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT (τ, l.1, l.2)
      (pureTensorL aP f P)) x
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at e1 e2 ⊢
    rw [show aP (τ, l.1, l.2) (pureTensorL aP f P) x = _ from e1, show aM (τ, l.1, l.2) (pureTensorL aP f P) x = _ from e2]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  conv_lhs => rw [expand_unit (hP.onbS τ) (hP.onbT τ) z]
  rw [hsum]
  simp only [hadd _ _ _ hF, hsm _ _ _ hF, hu, hJu]

  simp only [dzPol, MvPolynomial.C_mul', map_smul, map_sum, map_sub, smul_mul_assoc]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  set ζ := fCoord (BS τ) (BT τ) (pS τ) (pT τ) z l
  have hζ : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I := (Complex.re_add_im ζ).symm
  have hcζ : starRingEnd ℂ ζ = (ζ.re : ℂ) - (ζ.im : ℂ) * Complex.I := by
    conv_lhs => rw [hζ]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hcζ]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  linear_combination (-((fockScale D τ : ℂ) / 2) * pureTensorL aP f (MvPolynomial.X (τ, l.1, l.2) * P) x) * hζ

end DRhoPf

section HeisFar

open Formalism.IndefR.Fock.DRho

theorem heisFarDRho (D : D7) : HeisFarDRho D := by
  intro ψ θ hψ hθ hLine S T τ w hw z F hF
  obtain rfl := Eqv.eq_thetaC D hθ

  have hph : ∀ t : ℝ, ψ (symplOH S T w (lineAt (Eqv.thetaC D) τ z t)) = 1 := by
    intro t
    rw [lineAt_eq hLine τ z t, psi_real S T hψ w _ (finPart_Lb _)]
    have hs : (∑ ρ, eR S T ρ (compAt (Eqv.thetaC D) ρ w) (compAt (Eqv.thetaC D) ρ (Lb D _ _ (t • sg τ z)))) = 0 := by
      refine Finset.sum_eq_zero fun ρ _ => ?_
      rw [compAt_Lb]
      by_cases hρ : ρ = τ
      · subst hρ
        rw [hw, eR, eM_zero_left]
      · have : Matrix.of ((t • sg (D := D) τ z) ρ) = 0 := by
          ext i j
          simp [sg, hρ]
        rw [this, eR, eM_zero_right]
    rw [hs]
    simp
  have hph' : ∀ t : ℝ, ψ (symplOH S T (lineAt (Eqv.thetaC D) τ z t) w) = 1 := by
    intro t
    rw [Formalism.IndefR.Fin.symplOH_swap, AddChar.map_neg_eq_inv, hph t, inv_one]
  funext x
  have key : (fun t : ℝ => heisO ψ S T (lineAt (Eqv.thetaC D) τ z t) (heisO ψ S T w F) x) =
      fun t => ψ (symplOH S T x w) * heisO ψ S T (lineAt (Eqv.thetaC D) τ z t) F (x + w) := by
    funext t
    simp only [heisO]
    rw [Formalism.IndefR.Fin.symplOH_add_left, Formalism.IndefR.Fin.symplOH_add_left, AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul, hph t, hph' t, add_right_comm x]
    ring
  show deriv (fun t : ℝ => heisO ψ S T (lineAt (Eqv.thetaC D) τ z t) (heisO ψ S T w F) x) 0 =
    ψ (symplOH S T x w) * deriv (fun t : ℝ => heisO ψ S T (lineAt (Eqv.thetaC D) τ z t) F (x + w)) 0
  rw [key, deriv_const_mul_field]

end HeisFar

section OmFar

open Formalism.IndefR.Fock.DRho
open scoped TensorProduct

def AtOnly (V : HSp D) (τ : D.what₂.Tau) (g : GA D V) : Prop :=
  g ∈ GinfC V ∧ ∀ ρ, ρ ≠ τ → compAt (Eqv.thetaC D) ρ (Formalism.L2.Theta.mt V g) = 1

theorem mt_mul (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem compAt_mul {m k n : ℕ} (ρ : D.what₂.Tau) (A : Matrix (Fin m) (Fin k) (AE D)) (B : Matrix (Fin k) (Fin n) (AE D)) :
    compAt (Eqv.thetaC D) ρ (A * B) = compAt (Eqv.thetaC D) ρ A * compAt (Eqv.thetaC D) ρ B := by
  unfold compAt
  exact Matrix.map_mul (f := (Eqv.thetaC D ρ).comp (infPart D))

theorem finPart_matmul {m k n : ℕ} (A : Matrix (Fin m) (Fin k) (AE D)) (B : Matrix (Fin k) (Fin n) (AE D)) :
    (A * B).map (finPart D) = A.map (finPart D) * B.map (finPart D) :=
  Matrix.map_mul

theorem finPart_mt {V : HSp D} {g : GA D V} (hg : g ∈ GinfC V) : (Formalism.L2.Theta.mt V g).map (finPart D) = 1 := by
  have h0 : finHom V g = 1 := hg
  have h : (finHom V g).1 = 1 := by rw [h0]; rfl
  exact h

theorem atOnly_inv {V : HSp D} {τ : D.what₂.Tau} {g : GA D V} (hg : AtOnly V τ g) : AtOnly V τ g⁻¹ := by
  refine ⟨(GinfC V).inv_mem hg.1, fun ρ hρ => ?_⟩
  have h := congrArg (compAt (Eqv.thetaC D) ρ) (mt_mul V g⁻¹ g)
  rw [inv_mul_cancel, mt_one, compAt_mul, hg.2 ρ hρ, Matrix.mul_one] at h
  rw [← h]
  try (ext i j; simp [compAt, Matrix.one_apply])

theorem actO_far {S T : HSp D} {τ : D.what₂.Tau} {g : GA D S} {h : GA D T} (hg : AtOnly S τ g) (hh : AtOnly T τ h)
    (w : WO S T) (hw : compAt (Eqv.thetaC D) τ w = 0) : actO S T g h w = w := by
  have hgi := atOnly_inv hg
  ext i j
  refine sub_eq_zero.1 (eq_zero_of_parts D _ ?_ ?_)
  · apply (Eqv.splitEquiv D).injective
    funext ρ
    rw [map_zero, Pi.zero_apply, Eqv.splitEquiv_apply, (infPart D).map_sub, (Eqv.thetaC D ρ).map_sub]
    show compAt (Eqv.thetaC D) ρ (actO S T g h w) i j - compAt (Eqv.thetaC D) ρ w i j = 0
    unfold actO
    rw [compAt_mul, compAt_mul]
    by_cases hρ : ρ = τ
    · subst hρ
      rw [hw]
      simp
    · rw [hh.2 ρ hρ, hgi.2 ρ hρ]
      simp
  · rw [(finPart D).map_sub, sub_eq_zero]
    have e := congrArg (fun M => M i j) (show (actO S T g h w).map (finPart D) = w.map (finPart D) by
      unfold actO
      rw [finPart_matmul, finPart_matmul, finPart_mt hh.1, finPart_mt hgi.1, Matrix.one_mul, Matrix.mul_one])
    exact e

theorem oneP_atOnly (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) :
    AtOnly V τ (oneP (Eqv.thetaC D) V τ X t) := by
  unfold oneP atTau
  split_ifs with hx
  · obtain ⟨h1, -, h3⟩ := hx.choose_spec
    exact ⟨h1, fun ρ hρ => h3 ρ hρ⟩
  · refine ⟨(GinfC V).one_mem, fun ρ _ => ?_⟩
    rw [mt_one]
    try (ext i j; simp [compAt, Matrix.one_apply])

theorem omDerFar (D : D7) : OmDerFar D := by
  intro hLine ψ θ S T χS χT om hθ hW τ XS XT hXS hXT w hw F hF
  obtain rfl := Eqv.eq_thetaC D hθ
  funext x
  have key : (fun t : ℝ => om (oneP (Eqv.thetaC D) S τ XS t, oneP (Eqv.thetaC D) T τ XT t) (heisO ψ S T w F) x) =
      fun t => ψ (symplOH S T x w) * om (oneP (Eqv.thetaC D) S τ XS t, oneP (Eqv.thetaC D) T τ XT t) F (x + w) := by
    funext t
    rw [hW.om_heis _ _ w F hF, actO_far (oneP_atOnly S τ XS t) (oneP_atOnly T τ XT t) w hw]
    rfl
  show deriv (fun t : ℝ => om (oneP (Eqv.thetaC D) S τ XS t, oneP (Eqv.thetaC D) T τ XT t) (heisO ψ S T w F) x) 0 =
    ψ (symplOH S T x w) * deriv (fun t : ℝ => om (oneP (Eqv.thetaC D) S τ XS t, oneP (Eqv.thetaC D) T τ XT t) F (x + w)) 0
  rw [key, deriv_const_mul_field]

end OmFar

theorem fockDerO_of_steps {D : D7} (hT : ThetaDRho D) (hL : DRhoLin D) (hC : DRhoComm D) (hH : HeisFarDRho D)
    (hS : OmSmoothO D) (hDR : OmDerDRho D) (hFar : OmDerFar D) (hSk : OmDerSkew D) (hV : VacSchur D) :
    FockDerO D :=
  fockDerO_of hT hL hC quadCommPol fCoordFacts (dRhoPoly_of hT hL hC) hH hS hDR hFar hSk hV

theorem fockDerO_of_om {D : D7} (hS : OmSmoothO D) (hDR : OmDerDRho D) (hSk : OmDerSkew D) (hV : VacSchur D) :
    FockDerO D :=
  fockDerO_of_steps (Formalism.IndefR.Fock.DRho.thetaDRho D) (Formalism.IndefR.Fock.DRho.dRhoLin D)
    (Formalism.IndefR.Fock.DRho.dRhoComm D) (heisFarDRho D) hS hDR (omDerFar D) hSk hV

end Formalism.IndefR.Fock.Der

end
