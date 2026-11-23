import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAComponentsMemCompletedLatticeOffPrimesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfBComponentsMemCompletedLatticeOffConjStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslateStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmAtSmulRight
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EventuallyFinEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DifferentiableOfChar
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOperatorFinitePartLatticeVacuumSign
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.FinRestComm

variable {D : D7}

theorem finPart_finRat_sub {S T : HSp D} (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank)
    (j : Fin S.rank) : finPart D (GlobalTheory.VacUnique.finRat S T M i j - incA D (M i j)) = 0 := by
  rw [RingHom.map_sub]
  exact sub_eq_zero.2 ((GlobalTheory.LatVac.finPart_pair 1 (M i j)).trans (GlobalTheory.LatVac.finPart_incA (M i j)).symm)

theorem infPart_of_idemSum {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hI : IsIdemSum e SS) :
    infPart D e = 0 := by
  obtain ⟨⟨es, hes, he⟩, -⟩ := hI
  subst he
  induction SS using Finset.induction_on with
  | empty => rw [Finset.sum_empty, RingHom.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, RingHom.map_add, GlobalTheory.SplitScalar.infPart_splitIdem (hes a (Finset.mem_insert_self a s)).1,
      ih fun PP hPP => hes PP (Finset.mem_insert_of_mem hPP), add_zero]

theorem smul_rest_eq_zero {S T : HSp D} {e : AE D} (hee : e * e = e) (hinf : infPart D e = 0)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    e • (GlobalTheory.VacUnique.finRat S T M - M.map (fun r => e * incA D r)) = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.zero_apply, smul_eq_mul, mul_sub,
    ← mul_assoc, hee, ← mul_sub]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [RingHom.map_mul, hinf, zero_mul, RingHom.map_zero]
  · rw [RingHom.map_mul, finPart_finRat_sub, mul_zero, RingHom.map_zero]

theorem char_sympl_rest_eq_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplO S T ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r)) (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y'))) = 1 := by
  intro D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' c hc hcP x' hx' y' hy'
  have hZ := GlobalTheory.T.halfA_components_mem_completedLattice_offPrimes D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' c hc hcP x' hx'
  have hY := GlobalTheory.T.halfB_components_mem_completedLattice_offConj D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' c hc hcP y' hy'
  have heZ := smul_rest_eq_zero (S := S) (T := T) (GlobalTheory.PlaceDatum.idemSum_mul_self hI) (infPart_of_idemSum hI)
    (LinearMap.toMatrix' x')
  have hsplit : GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y') =
      (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y') -
        (LinearMap.toMatrix' y').map (fun r => cA D e * incA D r)) +
      cA D e • (LinearMap.toMatrix' y').map (incA D) := by
    have : (LinearMap.toMatrix' y').map (fun r => cA D e * incA D r) =
        cA D e • (LinearMap.toMatrix' y').map (incA D) := Matrix.ext fun i j => rfl
    rw [this, sub_add_cancel]
  rw [hsplit, ← GlobalTheory.LatVac.symplHom_apply, map_add, AddChar.map_add_eq_mul, GlobalTheory.LatVac.symplHom_apply,
    GlobalTheory.LatVac.symplHom_apply, ← GlobalTheory.SplitScalar.symplO_smul, heZ, GlobalTheory.SplitScalar.symplO_zero_left,
    AddChar.map_zero_eq_one, mul_one]
  exact GlobalTheory.LatVac.char_sympl_eq_one hP.std hN hN' hZ hY

end GlobalTheory.FinRestComm
