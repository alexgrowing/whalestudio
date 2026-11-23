import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamF
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOZeroEqJetP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7}

theorem sum_re_im_add_smul {m n a b : ℕ} (U V : Fin a → Fin b → Matrix (Fin m) (Fin n) ℂ) (z e : Fin a → Fin b → ℂ)
    (t : ℝ) :
    ∑ i, ∑ j, ((((z i j + t • e i j).re : ℝ) : ℂ) • U i j + (((z i j + t • e i j).im : ℝ) : ℂ) • V i j) =
      ∑ i, ∑ j, ((((z i j).re : ℝ) : ℂ) • U i j + (((z i j).im : ℝ) : ℂ) • V i j) +
        t • ∑ i, ∑ j, ((((e i j).re : ℝ) : ℂ) • U i j + (((e i j).im : ℝ) : ℂ) • V i j) := by
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_mul, add_smul, smul_add, mul_smul, Complex.coe_smul]
  abel

theorem fmR_add_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank)
    (t : ℝ) : fmR A B (z + t • e) = fmR A B z + t • fmR A B e := by
  funext τ
  exact sum_re_im_add_smul _ _ (z τ) (e τ) t

theorem heis_dRho_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (z e : VCx D.what₂.Tau S.rank T.rank) (τ : D.what₂.Tau) (v : Matrix (Fin T.rank) (Fin S.rank) ℂ), GlobalTheory.FockTransl.Jet.fmR A B e τ = v → (∀ τ', τ' ≠ τ → GlobalTheory.FockTransl.Jet.fmR A B e τ' = 0) → heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ v h) x = deriv (fun t : ℝ => Complex.exp (-((Real.pi : ℂ) * Complex.I) * ((t * GlobalTheory.FockTransl.Jet.omF A B z e : ℝ) : ℂ)) * heisO ψ S T (fockPt σ A B (z + t • e)) h x) 0 := by
  intro D ψ θ σ hψ hC S T A B h x z e τ v hv h0
  have hux : GlobalTheory.AdForm.JetRead.ux τ v = fmR A B e := by
    funext τ' i j
    unfold GlobalTheory.AdForm.JetRead.ux
    split_ifs with hτ
    · subst hτ; rw [← hv]
    · rw [h0 τ' hτ]; rfl
  have hline : ∀ t : ℝ, (lineAt θ τ v t : WO S T) = iotaW σ T S (t • fmR A B e) := fun t => by
    rw [GlobalTheory.AdForm.JetRead.lineAt_eq hC, hux]
  have hfun : (fun t : ℝ => ψ (symplOH S T x (fockPt σ A B z)) *
      heisO ψ S T (lineAt θ τ v t) h (x + fockPt σ A B z)) = fun t : ℝ =>
      Complex.exp (-((Real.pi : ℂ) * Complex.I) * ((t * omF A B z e : ℝ) : ℂ)) *
        heisO ψ S T (fockPt σ A B (z + t • e)) h x := by
    funext t
    have e1 : ψ (symplOH S T x (fockPt σ A B z)) * heisO ψ S T (lineAt θ τ v t) h (x + fockPt σ A B z) =
        heisO ψ S T (fockPt σ A B z) (heisO ψ S T (lineAt θ τ v t) h) x := rfl
    have e2 : fockPt σ A B z = iotaW σ T S (fmR A B z) := rfl
    have e3 : fockPt σ A B (z + t • e) = iotaW σ T S (fmR A B z) + iotaW σ T S (t • fmR A B e) := by
      rw [← AddMonoidHom.map_add, ← fmR_add_smul]; rfl
    rw [e1, GlobalTheory.OrientedHeis.heisO_heisO, Pi.smul_apply, smul_eq_mul, hline, e3, e2,
      GlobalTheory.OrientedHeis.psi_symplOH hC hψ, hC.pi_iota, LinearMap.map_smul, smul_eq_mul]
    rfl
  show ψ (symplOH S T x (fockPt σ A B z)) *
      deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ v t) h (x + fockPt σ A B z)) 0 = _
  rw [← deriv_const_mul_field, hfun]

end GlobalTheory.FockTransl.Jet

end
