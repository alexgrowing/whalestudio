import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeScalarLabelCompEqShiftDownSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalVacuumOfIsLatticeVacuumCoprimeLevel
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

noncomputable section

namespace GlobalTheory.VacSplit

theorem isVacAt_of_vacFin : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → Formalism.DivisionValues.conjPl w ≠ w → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ), VacFin ψ S T v f → IsVacAt ψ S T w f := by
  intro D v w hvw hw ψ S T f hf
  refine ⟨hf.1, fun e f' he u hu hhalf => ?_⟩
  have he' := he
  obtain ⟨hid, rfl⟩ := GlobalTheory.CentralShift.split_of_primeIdem hw he
  obtain ⟨v', ε, hε, hf', hv'⟩ := GlobalTheory.VacLat.place_of_primeIdem he'
  rw [hvw] at hv'
  subst hv'
  have hfu : ∀ i j, (e + Formalism.L2.Theta.cA D e) * u i j = u i j := by
    have h1 := hid.1.1
    have h2 := hid.1.2.1
    have h3 : Formalism.L2.Theta.cA D e * Formalism.L2.Theta.cA D e = Formalism.L2.Theta.cA D e := by rw [← map_mul, h1]
    have h4 : Formalism.L2.Theta.cA D e * e = 0 := by rw [mul_comm]; exact h2
    rcases hhalf with h | h <;> intro i j
    · have h' : e * u i j = u i j := h i j
      rw [← h', ← mul_assoc, add_mul, h1, h4, add_zero]
    · have h' : Formalism.L2.Theta.cA D e * u i j = u i j := h i j
      rw [← h', ← mul_assoc, add_mul, h2, h3, zero_add]
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have hα : α ∈ intAf D.host.F := fun w' => by
    by_cases hw' : w' = v
    · subst hw'; rw [h1]; exact one_mem _
    · rw [h0 w' hw']; exact zero_mem _
  set a₀ := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) with ha₀
  let φ : WO S T →+ WO S T := DistribMulAction.toAddMonoidHom (WO S T) a₀
  have key : latO S T (L0c D S) (L0c D T) (fun _ => True) ≤
      (latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
        fun u => u = v).comap φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβ, -, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨α * β, GlobalTheory.VacLat.intAf_mul hα hβ,
      fun v'' hv'' => by rw [map_mul, h0 v'' hv'', zero_mul], a, ha, s, ?_, t, ?_, ?_⟩
    · show S.frame.equivFun.symm s ∈ S.L0
      rw [Module.Basis.equivFun_symm_apply]; exact hs
    · show T.frame.equivFun.symm t ∈ T.L0
      rw [Module.Basis.equivFun_symm_apply]; exact ht
    · ext i j
      simp only [φ, DistribMulAction.toAddMonoidHom_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [ha₀, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.VacLat.pairA_mul]
  have hum : u ∈ latO S T (frameLat S : Set (Fin S.rank → D.host.E)) (frameLat T : Set (Fin T.rank → D.host.E))
      fun u => u = v := by
    have hk := key hu
    have hφ : φ u = u := by
      ext i j
      have hx := hfu i j
      rw [hf'] at hx
      exact hx
    rwa [AddSubgroup.mem_comap, hφ] at hk
  rcases hhalf with h | h
  · exact hf.2.2 e hid.1 u hum h
  · refine hf.2.2 (Formalism.L2.Theta.cA D e) ⟨by rw [← map_mul, hid.1.1], ?_, ?_⟩ u hum h
    · rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm]; exact hid.1.2.1
    · obtain ⟨w', η, hη, hwη⟩ := hid.1.2.2
      exact ⟨w', η, hη, by rw [GlobalTheory.DualPairCheck.cA_cA, add_comm]; exact hwη⟩

end GlobalTheory.VacSplit

end
