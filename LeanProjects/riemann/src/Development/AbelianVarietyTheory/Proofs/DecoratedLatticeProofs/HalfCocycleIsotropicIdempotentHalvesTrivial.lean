import Mathlib
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

namespace GlobalTheory.HalfCocycle

theorem half_eq (D : D7) :
    incA D ((2 : D.host.E)⁻¹) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2)) := by
  have h2 : ((2 : D.host.E))⁻¹ = algebraMap D.host.F D.host.E (1 / 2) := by
    rw [map_div₀, map_one, map_ofNat, one_div]
  rw [h2, ← IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AE D)]
  show (inclR (AF D.host.F)) (algebraMap D.host.F D.host.E (1/2)) = _
  simp [inclR, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]

theorem half_mul_symplO {D : D7} (S T : HSp D) (x y : WO S T) :
    algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T x y = symplO S T (incA D ((2 : D.host.E)⁻¹) • x) y := by
  unfold symplO
  rw [GlobalTheory.SplitScalar.hO_smul_left, half_eq, mul_left_comm (incA D D.host.xi0),
    ← Algebra.smul_def (algebraMap D.host.F (AF D.host.F) (1 / 2)) (incA D D.host.xi0 * hO S T x y),
    LinearMap.map_smul, smul_eq_mul]

theorem half_idem_int {D : D7} {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hI : IsIdemSum e SS)
    (h2 : ∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) :
    finPart D (incA D ((2 : D.host.E)⁻¹) * e) ∈ intAE D := by
  obtain ⟨⟨es, hes, rfl⟩, _⟩ := hI
  rw [Finset.mul_sum, map_sum]
  refine AddSubgroup.sum_mem _ fun PP hPP => ?_
  have hn : (2 : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro hm
    apply h2 PP hPP
    have h2Q : 2 ∣ D.host.QS := (dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd
    obtain ⟨k, hk⟩ := h2Q
    rw [hk]
    push_cast
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hm))
  have hiff := (hes PP hPP).2 (2 : 𝓞 D.host.E) two_ne_zero
  have hc : ((2 : 𝓞 D.host.E) : D.host.E) = 2 := by first | rfl | simp | exact map_ofNat _ 2 | norm_cast
  rw [hc] at hiff
  rw [mul_comm]
  by_contra hc'
  exact hn (hiff.mpr hc')

end GlobalTheory.HalfCocycle

open GlobalTheory.HalfCocycle in

theorem GlobalTheory.HalfCocycle.char_symplOH_idem_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ u ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), ∀ v ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True), ψ (symplOH S T (e • u) (cA D e • v)) = 1 := by
  intro D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' u hu v hv
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self hI
  have key : symplO S T (e • u) (cA D e • v) = symplO S T (e • u) v := by
    rw [← GlobalTheory.SplitScalar.symplO_smul, smul_smul, hee]
  rw [symplOH, key, half_mul_symplO, smul_smul]
  exact GlobalTheory.LatVac.char_sympl_eq_one hP.std hN hN'
    (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (half_idem_int hI h2) u hu) hv
