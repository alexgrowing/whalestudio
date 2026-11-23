import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalVacuumOfIsLatticeVacuumCoprimeLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
namespace GlobalTheory.VacInertAt

variable {D : D7}

theorem half_eq_two_smul {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal) (S T : HSp D) (u : WO S T)
    (hu : u ∈ latO S T (L0c D S) (L0c D T) fun _ => True)
    (hh : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u) :
    ∃ u' ∈ latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
      (fun x => x = v), u = 2 • u' := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have h2F : (2 : D.host.F) ≠ 0 := two_ne_zero
  set γ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F := α * algebraMap D.host.F _ ((2 : D.host.F)⁻¹) with hγdef
  have hγ : γ ∈ intAf D.host.F := fun w => by
    rw [hγdef, map_mul, AlgHom.commutes]
    by_cases hw : w = v
    · subst hw
      rw [h1, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap, map_inv₀]
      have : HeightOneSpectrum.valuation D.host.F w (2 : D.host.F) = 1 := by
        rw [← map_ofNat (algebraMap (𝓞 D.host.F) D.host.F) 2, HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_eq_one_iff.2 h2
      rw [this, inv_one]
    · rw [h0 w hw, zero_mul]; exact zero_mem _
  have hγv : ∀ w, ¬ w = v → evalV D.host.F w γ = 0 := fun w hw => by
    rw [hγdef, map_mul, h0 w hw, zero_mul]
  have hαγ : α = γ + γ := by
    rw [← two_mul, hγdef, mul_comm α, ← mul_assoc, ← map_ofNat (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) 2,
      ← map_mul, mul_inv_cancel₀ h2F, map_one, one_mul]
  set a₀ := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 γ) with ha₀
  let φ : WO S T →+ WO S T := DistribMulAction.toAddMonoidHom (WO S T) a₀
  have key : latO S T (L0c D S) (L0c D T) (fun _ => True) ≤
      (latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
        (fun x => x = v)).comap φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, -, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨γ * β, GlobalTheory.VacLat.intAf_mul hγ hβ,
      fun w hw => by rw [map_mul, hγv w hw, zero_mul], a, ha, s, by rw [← hermitianSpaceBaseLattice_eq_frameLattice]; exact hs, t,
      by rw [← hermitianSpaceBaseLattice_eq_frameLattice]; exact ht, ?_⟩
    ext i j
    simp only [φ, DistribMulAction.toAddMonoidHom_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [ha₀, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.VacLat.pairA_mul]
  refine ⟨a₀ • u, key hu, ?_⟩
  have he : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = a₀ + a₀ := by
    rw [ha₀, ← map_add, hαγ]
    congr 1
    exact Prod.ext (add_zero 0).symm rfl
  ext i j
  rw [two_nsmul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← add_mul, ← he]
  exact (hh i j).symm

theorem isVacAt_of_vacFin : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)),
    w.under (𝓞 D.host.F) = v → Formalism.DivisionValues.conjPl w = w → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ),
    VacFin ψ S T v f → IsVacAt ψ S T w f := by
  intro D v w hv hw ψ S T f hf
  obtain ⟨ε, hε, -, hc, hpi⟩ := GlobalTheory.VacFixInert.inert_data hw
  have h2 := GlobalTheory.VacFixInert.two_not_mem hc
  rw [hv] at hε h2
  refine ⟨hf.1, fun e f' he u hu hhalf => ?_⟩
  have hee := (hpi e f' he).1
  have hh : IsHalf (algebraMap (AF D.host.F) (AE D) ε) u := by
    rcases hhalf with h | h
    · rw [hee] at h; exact h
    · rw [hee, GlobalTheory.IdemSupport.cA_algebraMap] at h; exact h
  obtain ⟨u', hu', rfl⟩ := half_eq_two_smul hε h2 S T u hu hh
  exact hf.2.1 u' hu'

end GlobalTheory.VacInertAt
