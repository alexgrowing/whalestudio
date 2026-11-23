import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPairRealPointsSmulAdelicVacuumDetPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstitutionInverseTransposeMaximalMinorProductStatement

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem om_real_fock_eq : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  (∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))) →
  ∀ g ∈ GinfC X.A, ∀ T, X.om (g, 1) (X.fock T) = X.fock T := by
  intro D cc δ t0 Q P X hX hB g hg T
  set G : D.what₂.Tau → Matrix (Fin X.A.rank) (Fin X.A.rank) ℂ := fun τ => compAt X.θ τ (Formalism.L2.Theta.mt X.A g) with hG
  have hmt : ∀ τ, compAt X.θ τ (Formalism.L2.Theta.mt X.B (1 : GA D X.B)) = 1 := fun τ => by
    rw [GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one]
  have hmove := (GlobalTheory.OrientedHeis.om_pureTensorO D X.ψ X.θ X.A X.B X.χA X.χB X.om hX.2.weil hX.2.inf
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun τ => 1 * G τ) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1 * 1) g 1
    (fun τ => by simp) (fun τ => by simp) (fun τ => by simp [hG]) (fun τ => by rw [hmt])
    X.vac hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))).2
  have hsub := GlobalTheory.FockBaseChange.pureTensorO_subst D X.ψ X.θ X.A X.B hX.2.weil.std hX.2.inf (fun _ => 1) G
    (fun _ => 1) (fun _ => 1) X.vac hX.2.vac_theta (MvPolynomial.rename X.var (minorPol D T))
  have hdet : ∀ τ, (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det * ((G τ)⁻¹).det = 1 := fun τ => by
    have e := GlobalTheory.WeilVacMove.compAt_mt_mul_inv X.θ τ X.A g
    have hu : IsUnit (G τ) := IsUnit.of_mul_eq_one _ e
    rw [← Matrix.det_mul]
    rw [show compAt X.θ τ (Formalism.L2.Theta.mt X.A g) = G τ from rfl,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), Matrix.det_one]
  change X.om (g, 1) (pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac
    (MvPolynomial.rename X.var (minorPol D T))) = pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac
    (MvPolynomial.rename X.var (minorPol D T))
  rw [hmove, GlobalTheory.T.norm_pair_real_points_smul_adelic_vacuum_det_pow P X hX hB g hg, GlobalTheory.FiniteFock.pureTensorO_smul, hsub, GlobalTheory.T.substitution_inverse_transpose_maximalMinorProduct P X T G, map_smul, smul_smul,
    ← Finset.prod_mul_distrib]
  simp only [← mul_pow, hdet, one_pow, Finset.prod_const_one, one_smul]

end GlobalTheory.NormDict
